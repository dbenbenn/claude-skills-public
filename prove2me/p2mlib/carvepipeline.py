"""The module-route carve as one resumable pipeline (scripts/carve_pipeline.py).

Replaces the per-job bash drivers (plain_carve.sh, plain_pipeline*.sh, ext_publish.sh ...): one
tracked implementation, every step idempotent and logged, state in DIR/pipeline_state.json, every
sub-tool called from one skill snapshot (p2mlib.snapshot) so editing or pushing the live skill
cannot reach a running carve."""
import ast
import fcntl
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
import uuid

from . import leantext, runlock, snapshot, workspace as wslib

STEPS = ['fetch', 'inputs', 'filter_patches', 'port', 'build', 'wsbuild', 'config', 'graph', 'extdefs', 'plan', 'gen', 'names',
         'order', 'measure', 'calibrate', 'publish_prep', 'prose', 'check_text', 'dryrun', 'publish_early',
         'measure_pieces', 'calibrate_pieces', 'pieces_prep', 'publish']
# Overlap mode (pipeline.json `overlap`, on for carves created since 2026-10-29; dbenbenn: "a slow proof
# really shouldn't need to block submitting definition bundles"): `measure`, `calibrate` and the gates
# up to `dryrun` cover the bundles and statements only (the part that freezes at publish);
# `publish_early` (with --publish) publishes them from a background publisher while these steps
# measure, calibrate and check the pieces, which `publish` then releases.
OVERLAP_ONLY = ('publish_early', 'measure_pieces', 'calibrate_pieces', 'pieces_prep')
DEFAULT_LEAN_CAP = '~/claude/claude-private/tools/lean-cap'
PARAM_KEYS = ['folder', 'root_module', 'targets', 'bundle_prefix', 'defs', 'forced', 'patches', 'compat_imports',
              'stdsimplex', 'budget', 'lean_src', 'commit', 'fetch', 'config_set', 'measure_flags', 'meta', 'tags',
              'overlap']


LIMIT_FACTOR = 1.6      # a measured item this many times the budget is too slow for the verifier
MAX_REPLANS = 2
MAX_SCALE = 8.0


class StepFailed(Exception):
    pass


ACCEPT_CAP = 200        # an accept_over item is excused only below this many seconds
UNIFORM_MIN, UNIFORM_RATIO = 3, 2.5   # pieces over plan by a similar factor >= this: re-plan (oaiq-073)
SYSTEMATIC_FRACTION = 0.25   # bundles over the limit: a systematic cost-model error when at least
                             # UNIFORM_MIN of them and this share of the measured bundles (Batch 3,
                             # 2026-10-25: QuarticPowerFree, KirchbergRordam, nearly every bundle 85-128 s
                             # against 55 s); fewer are split alone (oaiq-081: 3 of 194 bundles)
MAX_BUNDLE_SPLITS = 3   # rounds of splitting single slow bundles before a person looks
STATEMENT_SHARE = 0.5   # a slow piece whose statement alone compiles in this share of its time is slow
                        # by its type (oaiq-075: 316 s of 328 in .olean serialization): no split helps
PIECE_CAP = 120         # a piece (resubmittable) is excused below this; dbenbenn 2026-10-29 (was 150): a slow
                        # submit costs only wall-clock, a needless re-plan hours; verifier data: 94-103 s passed,
                        # 118-126 s timed out 3x (oaiq-078), 125 s and 162 s passed on a retry (oaiq-047, -085),
                        # 192 s timed out 3x (oaiq-031)


def calibration(plan, times, scale, budget, frozen=(), limit_factor=LIMIT_FACTOR, accepted=()):
    """Does the cost model's `scale` (time_scale) fit this carve's measured times?
    Returns {'over': [(item, secs, cost)], 'ratio', 'new_scale', 'limit', 'measured', 'slowest'}.

    Batch 3 (2026-10-25): the first plans of QuarticPowerFree and KirchbergRordam were made with the
    default scale and measured at 85-128 s per bundle against a budget of 55 s; a 128 s bundle timed
    out three times at the verifier. Re-planned with time_scale 2.2 and 4.5, every item fitted. One
    sample of pieces cannot predict this (per-item error ran 0.3-1.4x at the final scale, so a
    small sample would have called Kirchberg's first plan fine), but the full measurement that
    precedes publishing already holds every item: an item measured over `limit_factor` x budget,
    that is not frozen (published), sets the scale to scale x (its measured seconds / its planned
    cost), the worst item deciding, so that its share is split next time. Items measured
    under the limit never lower the scale: a pessimistic estimate costs a few more bundles, a
    timeout costs three publish attempts."""
    limit = budget * limit_factor
    over, measured, slowest = [], 0, None
    items = [('bundle:' + b['name'], b['name'], b.get('cost') or 0) for b in plan.get('bundles', [])]
    items += [('piece:' + n, n, p.get('cost') or 0) for n, p in (plan.get('pieces') or {}).items()]
    for key, name, cost in items:
        t = times.get(key) or (times.get(name) if key.startswith('bundle:') else None)
        if not t or not t.get('ok'):
            continue
        measured += 1
        if slowest is None or t['secs'] > slowest[1]:
            slowest = (key, t['secs'])
        if key.startswith('piece:') and t['secs'] <= PIECE_CAP:
            # a piece is a proof: resubmittable, so submit as is and split only after two real
            # timeouts (oaiq-035/037: a 106 s piece cost two ~1 h re-plans); bundles and statements
            # freeze at publish
            continue
        if key in accepted and t['secs'] <= ACCEPT_CAP:
            continue                                   # pipeline.json accept_over
        if t['secs'] > limit and name not in frozen:
            over.append((key, t['secs'], cost))
    # a statement over the limit publishes, but every verify that imports it compiles its module and
    # fails (opus-kadison, oaiq-039: 110 s and 176 s); re-planning cannot shrink it and accept_over does
    # not excuse it. Published (frozen) and external statements are someone's already.
    statements_over, ext = [], set(plan.get('external') or ())
    for n in plan.get('stubs') or {}:
        t = times.get('statement:' + n)
        if n in ext or n in frozen or not t or not t.get('ok'):
            continue
        measured += 1
        if t['secs'] > limit:
            statements_over.append(('statement:' + n, t['secs']))
    ratio = max((secs / max(cost, 1.0) for _, secs, cost in over), default=1.0)
    new_scale = round(min(MAX_SCALE, max(scale * 1.1, scale * ratio)), 1) if over else scale
    return {'over': over, 'ratio': ratio, 'new_scale': new_scale, 'limit': limit, 'measured': measured,
            'slowest': slowest, 'statements_over': statements_over}


def published_drift(lib, published_lib):
    """The .lean files of published_lib (bundles and statements published or being published) that
    lib lacks or holds with other bytes."""
    out = []
    if not os.path.isdir(published_lib):
        return out
    for f in sorted(os.listdir(published_lib)):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(lib, f)
        if not os.path.exists(p) or open(p, 'rb').read() != open(os.path.join(published_lib, f), 'rb').read():
            out.append(f)
    return out


def unit_active(unit):
    """Is the systemd user unit running (False without systemd)?"""
    if not unit or not shutil.which('systemctl'):
        return False
    return subprocess.run(['systemctl', '--user', 'is-active', '--quiet', unit]).returncode == 0


def publisher_unit(d):
    return 'carve-pub-' + hashlib.sha1(os.path.realpath(d).encode()).hexdigest()[:10]


ENV_KEEP = ('PATH', 'HOME', 'USER', 'LANG', 'LC_ALL')
ENV_PREFIXES = ('P2M_', 'LEAN_', 'ELAN_')


def systemd_run_command(unit, cwd, env, sh):
    """systemd-run running `/bin/sh -c sh` as the transient user unit `unit`, with the environment
    a carve's tools need."""
    sets = ['--setenv=%s=%s' % (k, v) for k, v in sorted(env.items()) if k in ENV_KEEP or k.startswith(ENV_PREFIXES)]
    return ['systemd-run', '--user', '--unit=' + unit, '--collect', '--quiet', '-p', 'WorkingDirectory=' + cwd,
            *sets, '/bin/sh', '-c', sh]


def module_root_name(rootmod, prefixes, files):
    """The ported file (stem) holding OpenAI module ROOTMOD: oai_port_modules.py names a module
    after its path below the longest matching prefix, '.' -> '_', possibly with a further
    directory prefix; an exact stem wins over a suffix match."""
    best = [p for p in prefixes if rootmod.startswith(p + '.')]
    if best:
        root = rootmod[len(max(best, key=len)) + 1:].replace('.', '_')
    else:
        root = rootmod.rsplit('.', 1)[-1]
    stems = [f[:-5] for f in sorted(files) if f.endswith('.lean')]
    if root in stems:
        return root
    for s in stems:
        if s.endswith('_' + root):
            return s
    raise StepFailed('no ported module for %s (looked for %s.lean or *_%s.lean)' % (rootmod, root, root))


def derive_defs(ws, targets):
    defs = []
    for t in targets:
        _, rel = wslib.statement_module(t)
        p = os.path.join(ws, rel)
        if not os.path.exists(p):
            raise StepFailed('the statement of %s is not in the workspace (%s); fetch_theorems.py first' % (t, rel))
        for line in open(p, encoding='utf-8'):
            m = re.match(r'import\s+(Definitions\.\S+)', line)
            if m and m.group(1) not in defs:
                defs.append(m.group(1))
    return defs


def missing_inputs(ws, targets, defs):
    """The names to fetch so every target statement and Def_ bundle the carve imports is in the workspace:
    a target whose Theorems/ file is absent, or whose preamble imports a Definitions.Def_X not on disk,
    and every listed bundle not on disk."""
    need = []
    for t in targets:
        _, rel = wslib.statement_module(t)
        p = os.path.join(ws, rel)
        if not os.path.exists(p):
            need.append(t)
            continue
        for line in open(p, encoding='utf-8'):
            m = re.match(r'import\s+Definitions\.(\S+)', line)
            if m and not os.path.exists(os.path.join(ws, 'Definitions', m.group(1) + '.lean')):
                need.append(t)
                break
    for d in defs:
        m = re.match(r'Definitions\.Def_(\S+)$', d)
        if m and not os.path.exists(os.path.join(ws, 'Definitions', 'Def_' + m.group(1) + '.lean')):
            need.append(m.group(1))
    return list(dict.fromkeys(need))


def check_meta(path, lean_src, root_module):
    """Why oai_meta.json cannot serve the prose links, or None. publish_prep/prose build every link from
    its `prefixes`; a missing file or prefixes that are not the port's module prefixes gave broken links
    only after the whole carve had run (oaiq-007, oaiq-016)."""
    if not os.path.exists(path):
        return 'no %s: write {"title", "date", "family", "commit", "paper", "prefixes"} (see p2mlib/prosetemplate.py)' % path
    try:
        m = json.load(open(path))
    except ValueError as e:
        return '%s is not valid JSON: %s' % (path, e)
    # what publish_prep and the prose templates read (oaiq-066: no `family` crashed publish_prep with a
    # KeyError after the hour of measuring)
    for k in ('title', 'date', 'family', 'commit'):
        if not m.get(k):
            return '%s has no %r (needed by publish_prep and the prose templates)' % (path, k)
    if not re.fullmatch(r'[0-9a-f]{40}', str(m['commit'])):
        return '%s: commit must be the full 40-hex openai/math commit (links pin it)' % path
    pre = m.get('prefixes')
    if not pre or not isinstance(pre, list):
        return '%s has no "prefixes" (the OpenAI module prefixes, e.g. ["OAI.Geometry.Foo"])' % path
    for p in pre:
        if not os.path.isdir(os.path.join(lean_src, *p.split('.'))):
            return '%s: prefix %r is not a directory of the fetched sources (%s)' % (path, p, lean_src)
    if not any(root_module == p or root_module.startswith(p + '.') for p in pre):
        return '%s: no prefix of %s is a prefix of the root module %s' % (path, pre, root_module)
    # the port strips its own prefixes, OAI.<top directory>, from module names; any other value makes
    # every link repeat a directory (oaiq-031: OAI.Algebra.AuslanderReiten, 181 broken links)
    port = [p for p in openai_prefixes(lean_src) if p.startswith('OAI.')]
    wrong = [p for p in pre if p not in port]
    if wrong:
        return ('%s: prefixes %s are not the port\'s module prefixes (%s, what oai_port_modules strips); '
                'use those' % (path, wrong, [p for p in port if any(w.startswith(p + '.') for w in wrong)] or port))
    return None


def hash_paths(paths, exts=('',)):
    """sha1 over the content of files and directory trees (names relative to each root, sorted), or None
    when none of the paths exists: the identity of what a step reads or writes."""
    h, seen = hashlib.sha1(), False
    for root in paths:
        files = []
        if os.path.isdir(root):
            for dp, dn, fn in os.walk(root):
                dn[:] = sorted(x for x in dn if x != '__pycache__' and not x.startswith('.'))
                files += [os.path.join(dp, f) for f in sorted(fn) if f.endswith(tuple(exts))]
        elif os.path.exists(root):
            files = [root]
        for f in files:
            seen = True
            h.update(os.path.relpath(f, root).encode() + b'\0' + open(f, 'rb').read() + b'\0')
    return h.hexdigest() if seen else None


OUTSIDE_CLOSURE_LIMIT = 50


def outside_closure(lean_src, root_module):
    """(OpenAI modules under lean_src outside root_module's import closure, modules in the closure).
    The port and filter-patches steps take every module under lean_src as input, so lean_src must be
    the closure (what oai_fetch writes), never a whole checkout of openai/math (oaiq-033..048)."""
    seen, todo = set(), [root_module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        f = os.path.join(lean_src, *m.split('.')) + '.lean'
        if not os.path.exists(f):
            continue
        seen.add(m)
        todo += [i for i in leantext.import_names(open(f, encoding='utf-8').read())
                 if i.split('.')[0] in ('OAI', 'ComparatorChallenges')]
    out = 0
    for d, _, fs in os.walk(os.path.join(lean_src, 'OAI')):
        for f in fs:
            if f.endswith('.lean'):
                m = os.path.relpath(os.path.join(d, f), lean_src)[:-5].replace(os.sep, '.')
                if m not in seen:
                    out += 1
                    if out > 10 * OUTSIDE_CLOSURE_LIMIT:
                        return out, len(seen)
    return out, len(seen)


def openai_prefixes(lean_src):
    """The module prefixes the port takes: OAI.<directory> for each directory of OAI/, then each other
    top directory of the sources that holds Lean files (a third-party package the closure imports and
    the openai/math repo does not ship, e.g. PrimeNumberTheoremAnd, StrongPNT; oaiq-083)."""
    oai = os.path.join(lean_src, 'OAI')
    out = ['OAI.' + d for d in sorted(os.listdir(oai)) if os.path.isdir(os.path.join(oai, d))]
    for d in sorted(os.listdir(lean_src)):
        top = os.path.join(lean_src, d)
        if d != 'OAI' and os.path.isdir(top) and any(f.endswith('.lean') for _, _, fs in os.walk(top) for f in fs):
            out.append(d)
    return out


def _now():
    return time.strftime('%Y-%m-%dT%H:%M:%S')


# What in the running skill snapshot decides a step's output, beside what it reads from other steps:
# {step: (input name, files relative to the snapshot's prove2me/)}. oaiq-085/092: after a fix to an
# oaiport rewrite, `--upgrade` kept the old ported text (it took `--redo port`). oaiq-047: an upgrade
# across a LeanInfo.lean change left `graph` done, and `plan` re-elaborated 1259 modules one at a time
# (the LeanInfo cache is keyed by LeanInfo.lean) for ~3 h with no output.
_COMPAT = ['lean/compat_4_34.lean', 'lean/StdSimplexCompat.lean', 'lean/StdSimplexTopCompat.lean']
# what of carve_prep.py `filter-patches` runs: its rule input was the whole file, which changes almost daily
# for other subcommands, so every skill commit made a planned carve's port stale (oaiq-081, 2026-10-29)
FILTER_PATCHES_CODE = ('cmd_filter_patches', 'port_filter_patches', 'filter_patches', 'cut_identifier', '_IDENT',
                       'COMPAT', 'positional', 'opt')
SNAPSHOT_RULES = {
    'filter_patches': ('filter rules', ['scripts/carve_prep.py::' + ','.join(FILTER_PATCHES_CODE),
                                        'p2mlib/oaiport.py'] + _COMPAT),
    'port': ('port rules', ['scripts/oai_port_modules.py', 'p2mlib/oaiport.py'] + _COMPAT),
    'graph': ('LeanInfo tool', ['lean/LeanInfo.lean', 'lean/DeclGraph.lean']),
}
GRAPH_READERS = ('extdefs', 'plan', 'gen')     # the steps that load the graph (and LeanInfo's readings)
GRAPH_CONFIG_KEYS = ('src', 'roots', 'prefix', 'work', 'external_theorems')   # what `carve.py graph` reads


def python_defs(text, names):
    """The source of the top-level definitions and assignments `names` of a Python file, as one string
    (a missing one as `NAME=<missing>`); the whole text if it does not parse."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return text
    got = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            ns = [node.name]
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            ts = node.targets if isinstance(node, ast.Assign) else [node.target]
            ns = [t.id for t in ts if isinstance(t, ast.Name)]
        else:
            continue
        for n in ns:
            if n in names:
                got[n] = ast.get_source_segment(text, node)
    return '\0'.join('%s=%s' % (n, got.get(n, '<missing>')) for n in names)


def rules_hash(snap, rels):
    """sha1 over the files `rels` (relative to SNAP/prove2me) that exist, or None if none does. An entry
    `FILE.py::a,b` takes only those top-level definitions of FILE.py (python_defs)."""
    h, seen = hashlib.sha1(), False
    for r in rels:
        rel, _, names = r.partition('::')
        f = os.path.join(snap, 'prove2me', rel)
        if os.path.exists(f):
            seen = True
            data = open(f, 'rb').read()
            if names:
                data = python_defs(data.decode('utf-8', 'replace'), names.split(',')).encode()
            h.update(r.encode() + b'\0' + data + b'\0')
    return h.hexdigest() if seen else None


def carve_of(path):
    """The nearest directory at or above `path` that holds a pipeline.json (a carve directory), or None."""
    p = os.path.abspath(os.path.expanduser(path))
    while True:
        if os.path.isfile(os.path.join(p, 'pipeline.json')):
            return p
        q = os.path.dirname(p)
        if q == p:
            return None
        p = q


def logged_snapshot(log):
    """The snapshot directory of the last run recorded in a step log (`==== TIME STEP (skill SHA)`), if
    it is still in the snapshot cache."""
    if not os.path.exists(log):
        return None
    shas = re.findall(r'^==== \S+ \S+ \(skill (\S+)\)$', open(log, errors='replace').read(), re.M)
    if not shas:
        return None
    d = os.path.join(snapshot.cache_dir(), shas[-1])
    return d if os.path.isdir(d) else None


class Pipeline:
    def __init__(self, d, params, snap_root, ws=None):
        self.d = os.path.abspath(d)
        self.p = params
        self.snap = snap_root
        self.ws = ws or wslib.workspace()
        self.scripts = os.path.join(snap_root, 'prove2me', 'scripts')
        self.state_path = os.path.join(self.d, 'pipeline_state.json')
        self.state = json.load(open(self.state_path)) if os.path.exists(self.state_path) else {'steps': {}}
        self.lean_src = os.path.abspath(os.path.expanduser(params.get('lean_src') or os.path.join(self.d, 'src', 'lean')))
        self.meta = os.path.abspath(os.path.expanduser(params.get('meta') or os.path.join(self.d, 'oai_meta.json')))
        self._kept_rules = set()
        self.ran_now = set()

    # -- state ------------------------------------------------------------------------------
    def save(self):
        tmp = self.state_path + '.tmp'
        json.dump(self.state, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.state_path)

    def folder_dir(self):
        return os.path.join(self.ws, 'Solutions', self.p['folder'])

    def step_inputs_hash(self, s):
        """{name: hash} of what step `s` reads that another step (or the user) produces, taken now. Recorded
        when the step finishes; a later run that finds a recorded hash different has a stale step, and
        it and everything after it run again. `--redo filter_patches` after editing the patches changed
        port_patches.json and left the port unpatched (six batches, 2026-10); `--from` and `--redo` stay
        as they were. config.json is not tracked: calibrate rewrites it on purpose."""
        pp = os.path.expanduser(self.p['patches']) if self.p.get('patches') else None
        port_out = hash_paths([self.folder_dir()], ('.lean',))
        opts = json.dumps(self.compat_args())
        h = {
            'filter_patches': {'patches file': hash_paths([pp] if pp else []),
                               'sources': hash_paths([self.lean_src], ('.lean',))},
            'port': {'filter_patches': hash_paths([self.port_patches()]),
                     'sources': hash_paths([self.lean_src], ('.lean',)), 'port options': opts},
            'build': {'port': port_out},
            'config': {'port': port_out},
            'gen': {'carve patches': hash_paths([cp] if (cp := self.carve_patches_path()) else [])},
        }.get(s, {})
        if s in GRAPH_READERS and (gp := self.graph_path()):
            # oaiq-123: a `graph` re-run by a LeanInfo change is popped alone, "its consumers check its
            # output": without this, a changed graph left the old plan in place
            h['graph output'] = hash_paths([gp])
        if s == 'filter_patches' and pp:           # a skipped filter_patches reads no rules
            h['port options'] = opts
        rule = SNAPSHOT_RULES.get(s)
        if rule and (s != 'filter_patches' or pp):
            h[rule[0]] = rules_hash(self.snap, rule[1])
        return h

    def graph_path(self):
        """The declaration graph `carve.py graph` writes (config `work`/decl_graph.jsonl), or None."""
        w = (self.read_config() or {}).get('work')
        return os.path.join(self.d, os.path.expanduser(w), 'decl_graph.jsonl') if w else None

    def carve_patches_path(self):
        """The post-carve patches file `carve.py gen` applies (config `patches`), or None. Its text is an input
        of `gen`: oaiq-114 fixed a broken patch in place, and the resume kept generating the old one."""
        try:
            p = json.load(open(os.path.join(self.d, 'config.json'))).get('patches')
        except (OSError, ValueError):
            p = None
        p = p or (self.p.get('config_set') or {}).get('patches')
        return os.path.join(self.d, os.path.expanduser(p)) if p else None

    RULE_KEYS = {r[0] for r in SNAPSHOT_RULES.values()}

    def stale_step(self):
        """The first finished step whose recorded input hashes differ from the current ones: (step, what).
        A record without a rule hash (a state from before they were recorded) is compared with the
        snapshot its step log names, when that is still cached. A changed rule of `graph` matters only
        while a step that loads the graph has still to run (it re-warms the LeanInfo cache)."""
        for s in STEPS:
            rec = self.state['steps'].get(s)
            if not rec or rec['status'] not in ('done', 'skipped'):
                continue
            now = self.step_inputs_hash(s)
            had = rec.get('in') or {}
            if s == 'filter_patches' and not had and (rec['status'] == 'skipped') == bool(self.p.get('patches')):
                # a record from before hashes: no hash to compare, but whether the step is skipped at all changed
                # (oaiq-119: patches added to pipeline.json, and the resume measured the unpatched port)
                return s, 'patches file'
            for k, old in had.items():
                if k in now and now[k] != old and (k not in self.RULE_KEYS or self._rule_matters(s)):
                    return s, k
            g = self.state['steps'].get('graph') or {}
            if (s in GRAPH_READERS and 'graph output' not in had and rec['status'] == 'done'
                    and g.get('status') == 'done' and g.get('finished', '') > rec.get('finished', '~')):
                # a record from before the graph hash: `graph` ran again after it (oaiq-019/oaiq-123)
                return s, 'graph output'
            rule = SNAPSHOT_RULES.get(s)
            if rule and rule[0] in now and rule[0] not in had and rec['status'] == 'done' and self._rule_matters(s):
                then = logged_snapshot(os.path.join(self.d, 'logs', s + '.log'))
                if then and os.path.realpath(then) != os.path.realpath(self.snap):
                    old = rules_hash(then, rule[1])
                    if old is not None and old != now[rule[0]]:
                        return s, rule[0]
        return None

    PORT_STEPS = ('filter_patches', 'port')

    def keep_port(self):
        """--keep-port: keep the port as it is across changes to the skill's port rules, from now until an
        explicit `--redo port` or `--redo filter_patches` (or a --from at or before them): pipeline_state.json
        `keep_port`. oaiq-081: planned and measured (1,586 items) on an old snapshot, the new rules changed
        port_patches.json and would have re-ported, rebuilt and re-planned the whole carve; recording the
        current rules once held only until the next skill commit changed them again. The current rules and
        options are recorded as well, so a later change of the port options is still seen."""
        kept = []
        for s in self.PORT_STEPS:
            rec = self.state['steps'].get(s)
            if not rec or rec['status'] != 'done':
                continue
            now, had = self.step_inputs_hash(s), rec.setdefault('in', {})
            for k in (SNAPSHOT_RULES[s][0], 'port options'):
                if k in now and had.get(k) != now[k]:
                    had[k] = now[k]
                    kept.append(s)
        if not self.state.get('keep_port'):
            self.state['keep_port'] = {'since': _now(), 'skill': os.path.basename(self.snap)}
        print('== --keep-port: keep the port as it is across port-rule changes until `--redo port` (or '
              '`--redo filter_patches`)%s' % (
                  '; the current rules are recorded for %s' % ' and '.join(sorted(set(kept))) if kept else ''),
              flush=True)
        self.save()

    def clear_keep_port(self, why):
        if self.state.pop('keep_port', None):
            print('== %s: --keep-port ends; the port follows the skill\'s port rules again' % why, flush=True)

    def _rule_matters(self, s):
        if s == 'graph':
            return any(self.state['steps'].get(x, {}).get('status') not in ('done', 'skipped') for x in GRAPH_READERS)
        if s in self.PORT_STEPS and self.state.get('keep_port'):
            if s not in self._kept_rules:
                self._kept_rules.add(s)
                print('== note: the skill\'s port rules changed since %s ran; kept by --keep-port (since %s; '
                      '`--redo port` re-ports)' % (s, self.state['keep_port'].get('since')), flush=True)
            return False
        if self.publishing_started():
            # live items froze their text: never re-port under them by ourselves
            if s not in self._kept_rules:
                self._kept_rules.add(s)
                print('== note: the skill\'s port rules changed since %s ran, but publishing has started, so '
                      'the port is kept (`--redo port` re-ports anyway)' % s, flush=True)
            return False
        return True

    def publishing_evidence(self):
        """Why this carve has visibly begun publishing, or None: a publish or publish_early step record, a
        split_run run state, or the frozen published part (auto_config `frozen`, set by publish_early)."""
        steps = self.state['steps']
        if 'publish' in steps:
            return 'step publish ran'
        if 'publish_early' in steps:
            return 'step publish_early ran'
        if os.path.exists(os.path.join(self.d, 'publish', 'run_state.json')):
            return 'publish/run_state.json exists'
        if (self.state.get('auto_config') or {}).get('frozen'):
            return 'publish_early froze the published part (auto_config frozen)'
        return None

    def mark_publishing(self, why):
        if not self.state.get('publishing_started'):
            self.state['publishing_started'] = {'at': _now(), 'why': why}

    def publishing_started(self):
        """Has publishing begun? A state fact (pipeline_state.json `publishing_started`), set the first time
        any evidence is seen and kept: a frozen re-plan drops publish_early from the step records, and
        publish/run_state.json need not exist yet, so the evidence alone came and went (2026-10-29)."""
        if self.state.get('publishing_started'):
            return True
        why = self.publishing_evidence()
        if why:
            self.mark_publishing(why)
            return True
        return False

    def forget_publishing(self):
        """--forget-publishing: the explicit reset, refused while any evidence remains."""
        why = self.publishing_evidence()
        if why:
            raise StepFailed('--forget-publishing: refused, publishing has visibly begun (%s)' % why)
        if self.state.pop('publishing_started', None):
            print('== --forget-publishing: this carve counts as not publishing again', flush=True)

    # -- the port folder's owner ------------------------------------------------------------
    def owner_path(self):
        return os.path.join(self.folder_dir(), wslib.CARVE_OWNER)

    def read_owner(self):
        try:
            return json.load(open(self.owner_path()))
        except (OSError, ValueError):
            return None

    def write_owner(self, how):
        if not os.path.isdir(self.folder_dir()):
            return
        if not self.state.get('carve_id'):
            self.state['carve_id'] = uuid.uuid4().hex
        rec = {'carve': os.path.realpath(self.d), 'carve_id': self.state['carve_id'], 'since': _now(), 'how': how}
        tmp = self.owner_path() + '.tmp'
        json.dump(rec, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.owner_path())
        print('== Solutions/%s now belongs to this carve (%s)' % (self.p['folder'], how), flush=True)

    def port_log_carves(self):
        """The carve directories named by the last port command in logs/port.log (its sources, its
        port_patches.json), or None when this carve's log records no port."""
        log = os.path.join(self.d, 'logs', 'port.log')
        if not os.path.exists(log):
            return None
        cmds = [l[2:].split() for l in open(log, errors='replace') if l.startswith('$ ') and 'oai_port_modules' in l]
        if not cmds:
            return None
        out = set()
        for t in cmds[-1][2:]:                     # past the interpreter and the (snapshot's) script
            if t.startswith('/'):
                c = carve_of(t)
                if c:
                    out.add(os.path.realpath(c))
        return out

    def ever_ported(self):
        return 'port' in self.state['steps'] or self.port_log_carves() is not None

    def recorded_port_hashes(self):
        """The hashes of the port folder this carve recorded: what build and config read, what port wrote."""
        st = self.state['steps']
        hs = {((st.get(s) or {}).get('in') or {}).get('port') for s in ('build', 'config')}
        hs.add(((st.get('port') or {}).get('out') or {}).get('port'))
        return hs - {None}

    BELONGS = ('Solutions/%s belongs to carve %s; a copy must use its own workspace (P2M_WORKSPACE) or another '
               'folder. If this carve is to own it now (the other was abandoned), `--claim-folder`')

    def check_ownership(self, claim=False):
        """Before any step: the port writes WORKSPACE/Solutions/FOLDER, outside the carve dir, and gen and
        measure write config `out` and `work`. Refuse when the folder belongs to another carve directory
        (its owner file), or config.json points `out`/`work` into another carve or `src` at another workspace. A folder without an
        owner file (a carve from before 2026-10-29) is adopted by the carve whose port log names no other
        carve and whose recorded port hash is its current hash (or that recorded none: ported, not yet
        built), claimed by a carve that never ported, and else waits for `--claim-folder`. A carve moved to
        another directory (same carve_id, the old directory gone) takes its folder along. 2026-10-29: a
        `cp -a` rehearsal copy of oaiq-081 on the shared workspace re-ported and rewrote 228 files of the
        live carve's Solutions/OAIQ081_SAT (its config.json also named the original's out/ and work/)."""
        here, folder, f = os.path.realpath(self.d), self.folder_dir(), self.p['folder']
        problems, how = [], None
        cfg = self.read_config() or {}
        for k in ('out', 'work'):
            v = cfg.get(k)
            c = carve_of(v) if isinstance(v, str) and v else None
            if c and os.path.realpath(c) != here:
                problems.append('config.json `%s` (%s) lies in carve %s, which gen and measure would write: '
                                'a copy must point `out` and `work` at its own directory' % (k, v, c))
        src = cfg.get('src')
        if isinstance(src, str) and src and os.path.realpath(os.path.expanduser(src)) != os.path.realpath(self.ws):
            problems.append('config.json `src` (%s) is not this run\'s workspace %s (P2M_WORKSPACE): graph, plan and '
                            'measure would read and compile there' % (src, self.ws))
        owner = self.read_owner()
        if owner:
            them = owner.get('carve')
            if them != here:
                moved = (owner.get('carve_id') and owner['carve_id'] == self.state.get('carve_id')
                         and not os.path.exists(os.path.join(them or '', 'pipeline_state.json')))
                if claim:
                    how = '--claim-folder, from %s' % them
                elif moved:
                    how = 'the carve moved from %s' % them
                else:
                    problems.append(self.BELONGS % (f, them))
        elif os.path.isdir(folder) and any(x.endswith('.lean') for _, _, fs in os.walk(folder) for x in fs):
            named = self.port_log_carves()
            others = sorted(c for c in named or () if c != here)
            if claim:
                how = '--claim-folder'
            elif others:
                problems.append(self.BELONGS % (f, others[0]) + ' (no owner file; this carve\'s port log names '
                                'that carve: a copy of it?)')
            elif hash_paths([folder], ('.lean',)) in self.recorded_port_hashes():
                how = 'adopted: its modules are the port this carve recorded'
            elif not self.ever_ported():
                how = 'first port'
            elif not self.recorded_port_hashes():
                # ported (by its own log), never built: no hash to compare
                how = 'adopted: this carve\'s port log names no other carve and no hash was recorded since'
            else:
                problems.append('Solutions/%s has no owner file and its modules are not the port this carve recorded '
                                '(changed since by hand, or by another carve). If it is this carve\'s, '
                                '`--claim-folder` (the changed modules then rebuild as stale)' % f)
        if problems:
            raise StepFailed('refused, nothing was run:\n  ' + '\n  '.join(problems))
        if how:
            self.write_owner(how)
            self.save()

    def overlap(self):
        return bool(self.p.get('overlap'))

    def steps(self):
        """The steps this carve runs: every one in overlap mode, else the classic list."""
        return list(STEPS) if self.overlap() else [x for x in STEPS if x not in OVERLAP_ONLY]

    def ported_modules(self):
        d = self.folder_dir()
        return sum(1 for _, _, fs in os.walk(d) for f in fs if f.endswith('.lean')) if os.path.isdir(d) else 0

    def stale_message(self, s, k):
        if k not in self.RULE_KEYS:
            return '== stale: %s (its input "%s" changed); re-running it and every later step' % (s, k)
        msg = ('== stale: %s (the skill\'s %s changed since it ran); re-running it (later steps run again only '
               'if its output changes)' % (s, k))
        if s == 'graph':
            n = self.ported_modules()
            msg += ('\n   WARNING: the LeanInfo cache is keyed by LeanInfo.lean, so none of the %d module%s is '
                    'cached for this snapshot: `graph` elaborates every one again (about the build\'s CPU time, '
                    '`jobs` at a time; progress in logs/graph.log)' % (n, '' if n == 1 else 's'))
        return msg

    def invalidate(self, frm):
        i = STEPS.index(frm)
        for s in STEPS[i:]:
            self.state['steps'].pop(s, None)

    # -- running ----------------------------------------------------------------------------
    def env(self):
        e = dict(os.environ)
        cap = os.environ.get('P2M_LEAN_CAP', DEFAULT_LEAN_CAP)
        cap = os.path.expanduser(cap) if cap else ''
        if cap and os.path.isdir(cap):
            e['PATH'] = cap + os.pathsep + e.get('PATH', '')
        e['P2M_SKILL_ROOT'] = self.snap
        e['P2M_WORKSPACE'] = self.ws
        return e

    def tool(self, name, *args):
        return [sys.executable, os.path.join(self.scripts, name + '.py'), *map(str, args)]

    def run_cmds(self, step, cmds, cwd=None):
        log = os.path.join(self.d, 'logs', step + '.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        with open(log, 'a') as f:
            f.write('==== %s %s (skill %s)\n' % (_now(), step, os.path.basename(self.snap)))
            for c in cmds:
                f.write('$ %s\n' % ' '.join(c))
                f.flush()
                r = subprocess.run(c, cwd=cwd or self.d, env=self.env(), stdout=f, stderr=subprocess.STDOUT)
                if r.returncode:
                    f.write('(exit %d)\n' % r.returncode)
                    f.flush()
                    tail = ''.join(open(log, errors='replace').readlines()[-15:])
                    raise StepFailed("step '%s' failed (exit %d); log %s\n%s" % (step, r.returncode, log, tail))

    # -- steps ------------------------------------------------------------------------------
    def prefixes(self):
        return openai_prefixes(self.lean_src)

    def defs(self):
        return self.p.get('defs') or derive_defs(self.ws, self.p['targets'])

    def root(self):
        files = os.listdir(os.path.join(self.ws, 'Solutions', self.p['folder']))
        return module_root_name(self.p['root_module'], self.prefixes(), files)

    def port_patches(self):
        return os.path.join(self.d, 'port_patches.json')

    def compat_args(self):
        a = []
        if self.p.get('compat_imports'):
            a += ['--compat-imports', self.p['compat_imports']]
        if self.p.get('stdsimplex'):
            a += ['--stdsimplex', self.p['stdsimplex']]
        return a

    def step_fetch(self):
        if not self.p.get('fetch'):
            return 'skipped'
        a = [os.path.join(self.d, 'src'), self.p['root_module']]
        if self.p.get('commit'):
            a += ['--commit', self.p['commit']]
        self.run_cmds('fetch', [self.tool('oai_fetch', *a)])

    def step_inputs(self):
        names = missing_inputs(self.ws, self.p['targets'], self.p.get('defs') or [])
        if not names:
            return 'skipped'
        self.run_cmds('inputs', [self.tool('fetch_theorems', '--names', *names, '--no-build')])
        again = missing_inputs(self.ws, self.p['targets'], self.p.get('defs') or [])
        if again:
            raise StepFailed("step 'inputs': still not in the workspace after fetch_theorems: %s "
                             "(published yet? see logs/inputs.log)" % ', '.join(again))

    def check_closure(self, step):
        out, inside = outside_closure(self.lean_src, self.p['root_module'])
        if out > OUTSIDE_CLOSURE_LIMIT:
            raise StepFailed("step '%s': %s holds %s OpenAI modules outside the import closure of %s (%d "
                             "modules); the port would take them all as input. Use --fetch without "
                             "--lean-src (oai_fetch copies just the closure from the local openai/math "
                             "clone), or point lean_src in pipeline.json at a closure-only copy"
                             % (step, self.lean_src, '%d' % out if out <= 10 * OUTSIDE_CLOSURE_LIMIT
                                else 'more than %d' % (10 * OUTSIDE_CLOSURE_LIMIT), self.p['root_module'], inside))

    def step_filter_patches(self):
        if not self.p.get('patches'):
            return 'skipped'
        self.check_closure('filter_patches')
        self.run_cmds('filter_patches', [self.tool('carve_prep', 'filter-patches', os.path.expanduser(self.p['patches']),
                                                   self.lean_src, self.port_patches(), *self.prefixes(), *self.compat_args(),
                                                   '--folder', self.p['folder'])])

    def step_port(self):
        self.check_closure('port')
        a = [self.lean_src, self.p['folder'], *self.prefixes()]
        if self.p.get('patches'):
            a += ['--patches', self.port_patches()]
        self.run_cmds('port', [self.tool('oai_port_modules', *a, *self.compat_args())])
        rec = self.state['steps'].get('port')
        if rec is not None:
            rec['out'] = {'port': hash_paths([self.folder_dir()], ('.lean',))}
        if not self.read_owner():
            self.write_owner('first port')

    def step_build(self):
        self.run_cmds('build', [self.tool('oai_build_modules', self.p['folder'], self.root(), '--log', 'build.log',
                                          '--elab-log', 'build_elab.log')])

    def step_wsbuild(self):
        mods = self.defs() + [wslib.statement_module(t)[0] for t in self.p['targets']]
        self.run_cmds('wsbuild', [['lake', 'build', *mods]], cwd=self.ws)

    def step_config(self):
        bad = check_meta(self.meta, self.lean_src, self.p['root_module'])
        if bad:
            raise StepFailed("step 'config' failed: " + bad)
        a = ['config', self.d, self.p['folder'], self.root(), self.p['targets'][0]]
        for d in self.defs():
            a += ['--def', d]
        a += ['--bundle-prefix', self.p['bundle_prefix'], '--budget', '%g' % self.p.get('budget', 55)]
        for f in self.p.get('forced') or []:
            a += ['--forced', f]
        self.run_cmds('config', [self.tool('carve_prep', *a)])
        path = os.path.join(self.d, 'config.json')
        cfg = json.load(open(path))
        cfg['targets'] = list(self.p['targets'])
        cfg['external'] = sorted(set(cfg.get('external', [])) | set(self.p['targets']))
        if self.p.get('compat_imports'):
            cfg['collapse_mathlib'] = False
        cfg.update(self.p.get('config_set') or {})
        self.apply_auto(cfg)
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = dict(self.p.get('config_set') or {})

    def apply_auto(self, cfg):
        """What the pipeline itself set once publishing began (pipeline_state.json `auto_config`), over
        config.json: `frozen` (the published plan, its bundles, their published text), `forced` and
        `template_forced` (the published statements, so a re-plan keeps them; unions with what the
        user forced) and `cost_factors` (pieces measured over their plan). Re-applied whenever
        config.json is rewritten from pipeline.json, so a re-run `config` cannot unfreeze a carve."""
        a = self.state.get('auto_config') or {}
        if a.get('frozen'):
            cfg['frozen'] = dict(cfg.get('frozen') or {}, **a['frozen'])
        for k in ('forced', 'template_forced'):
            if a.get(k):
                cfg[k] = sorted(set(cfg.get(k) or ()) | set(a[k]))
        if a.get('cost_factors'):
            cf = dict(cfg.get('cost_factors') or {})
            for k, v in a['cost_factors'].items():
                cf[k] = max(cf.get(k, 1.0), v)
            cfg['cost_factors'] = cf
        return cfg

    def sync_config_set(self):
        """pipeline.json `config_set` keys changed since `config` applied them go straight into
        config.json, and the steps that read them run again: from `gen` for `patches` (post-carve
        literal patches), from `plan` for anything else. Re-running `config` instead would regenerate
        config.json and lose what calibrate wrote (time_scale). oaiq-051: a resume never applied new
        patches, and measure kept failing on unpatched text."""
        path = os.path.join(self.d, 'config.json')
        rec = self.state['steps'].get('config')
        if not rec or rec['status'] != 'done' or not os.path.exists(path):
            return
        want = dict(self.p.get('config_set') or {})
        cfg = json.load(open(path))
        if 'config_set_applied' not in self.state:
            # a state from before this was recorded: config.json holds what was applied (oaiq-120: taking
            # `want` as applied skipped a new `frozen`/`forced`, and the resume published the old plan)
            self.state['config_set_applied'] = {k: cfg[k] for k in want if k in cfg}
        old = self.state['config_set_applied']
        changed = sorted(k for k in set(want) | set(old) if want.get(k) != old.get(k))
        if not changed:
            self.save()
            return
        for k in changed:
            if k in want:
                cfg[k] = want[k]
            else:
                cfg.pop(k, None)
        self.apply_auto(cfg)
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = want
        frm = 'gen' if set(changed) <= {'patches'} else 'plan'
        print('== config_set changed (%s): config.json updated; re-running from %s' % (', '.join(changed), frm), flush=True)
        if frm in self.state['steps']:
            self.invalidate(frm)
        self.save()

    def read_config(self):
        path = os.path.join(self.d, 'config.json')
        try:
            return json.load(open(path))
        except (OSError, ValueError):
            return None

    def config_consumers(self, before):
        """config.json is not hashed (extdefs and calibrate rewrite it on purpose), so a re-run `config`
        that changed it re-runs what reads it: from `graph` if a key graph reads changed, else from
        `extdefs` (oaiq-047: `--redo config` reset time_scale and left the old plan done)."""
        after = self.read_config()
        if after is None or after == before:
            return
        frm = 'graph' if any(before.get(k) != after.get(k) for k in GRAPH_CONFIG_KEYS) else 'extdefs'
        later = [x for x in STEPS[STEPS.index(frm):] if x in self.state['steps']]
        if later:
            print('== config.json changed (%s): re-running from %s' % (
                ', '.join(sorted(k for k in set(before) | set(after) if before.get(k) != after.get(k)))[:200], frm),
                flush=True)
            self.invalidate(frm)

    def step_names(self):
        # planned names already live with other text, checked before the hours of measuring (oaiq-068/074)
        self.run_cmds('names', [self.tool('carve_prep', 'name-check', 'config.json')])

    def step_graph(self):
        self.run_cmds('graph', [self.tool('carve', 'graph', 'config.json')])

    def step_extdefs(self):
        a = ['ext-defs', 'config.json']
        for d in self.defs():
            a += ['--def', d]
        self.run_cmds('extdefs', [self.tool('carve_prep', *a)])

    def step_plan(self):
        self.run_cmds('plan', [self.tool('carve', 'plan', 'config.json')])

    def step_gen(self):
        self.run_cmds('gen', [self.tool('carve', 'gen', 'config.json')])
        self.check_published_unchanged('gen')

    def published_dir(self):
        return os.path.join(self.d, 'published')

    def check_published_unchanged(self, step):
        """Overlap mode, once bundles and statements began publishing: none of their files may change
        (published/lib holds them as they went to the publisher)."""
        if not (self.state.get('auto_config') or {}).get('frozen'):
            return
        cfg = self.read_config() or {}
        out = os.path.expanduser(cfg.get('out') or self.d)
        drift = published_drift(os.path.join(out, 'lib'), os.path.join(self.published_dir(), 'lib'))
        if drift:
            raise StepFailed(
                "step '%s': %d bundle/statement file(s) that are published or being published changed: %s. They are "
                "frozen: undo what changed them (a carve patch must not touch a bundle or statement once it "
                "publishes; config `frozen`/`forced`, which the pipeline set when publishing began, keep a "
                "re-plan from moving them). Compare out/lib with %s/lib."
                % (step, len(drift), ', '.join(drift[:20]), self.published_dir()))

    def step_order(self):
        self.run_cmds('order', [self.tool('carve', 'order', 'config.json')])

    def measure_flags(self):
        # every failing file in one run, not one per ~12 min round (oaiq-051), as the build does
        flags = list(self.p.get('measure_flags') or [])
        if '--keep-going' not in flags:
            flags.append('--keep-going')
        return flags

    def step_measure(self):
        kinds = ['--kinds', 'bundle,statement'] if self.overlap() else []
        self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *self.measure_flags(), *kinds)])

    def step_measure_pieces(self):
        self.run_cmds('measure_pieces', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                                   '--kinds', 'piece')])

    def work_paths(self, cfg):
        work = os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work'))
        plan_path = os.path.expanduser(cfg.get('plan') or os.path.join(work, 'plan.json'))
        return work, plan_path, os.path.join(work, 'times.json')

    STATEMENT_OVER_MSG = (
        "step 'calibrate': statement module(s) over the %.0f s limit: %s. A statement publishes, but every "
        "verify that imports it compiles its module and times out (opus-kadison, oaiq-039), and re-planning "
        "cannot shrink one. Profile it (`lean -o x.olean -Dprofiler=true`): if `.olean serialization` "
        "dominates, the statement's type is huge; name its large sides or subterms with `abbrev`s in a "
        "bundle (only declaration types cost, a definition's value is cheap) and state it with them "
        "(references/openai-ports.md \"Slow or odd failures\"); log %s")

    PIECE_HINT = (
        "Find what is slow before splitting. (1) Compile the piece's check file with "
        "`lean -o x.olean -Dprofiler=true`: if `.olean serialization` dominates while elaboration is fast, "
        "the statement's type is huge (oaiq-075: 316 s of 341 s, a term re-embedded thousands of times); "
        "name its large sides or subterms with `abbrev`s in a bundle and state it with them (declaration types cost, a definition's value is cheap; opus-kadison), do not split. (2) Else "
        "`-Dtrace.profiler=true -Dtrace.profiler.threshold=20000` shows the slow declaration or tactic "
        "(oaiq-074: one fun_prop goal, 53 s). (3) Kernel computation (`decide +kernel`, `native_decide`) or "
        "plain bulk: force the heavy lemmas into statements, listing them in pipeline.json `forced` (a private "
        "one by its graph node name, `_private.<module>.0.<name>`), then --from config (oaiq-031: one 192 s "
        "piece became 20 pieces of ~11 s).")

    def calibrate_inputs(self):
        cfg = json.load(open(os.path.join(self.d, 'config.json')))
        work, plan_path, times_path = self.work_paths(cfg)
        if not (os.path.exists(plan_path) and os.path.exists(times_path)):
            return None                                            # nothing was measured
        frozen = cfg.get('frozen') or {}
        fz = list(frozen.get('bundles') or ())
        fp = os.path.expanduser(frozen.get('plan') or '')
        if fp and os.path.exists(os.path.join(self.d, fp)):
            fz += list((json.load(open(os.path.join(self.d, fp))).get('stubs') or {}))   # live statements
        return cfg, json.load(open(plan_path)), json.load(open(times_path)), fz, times_path

    def calibrate_log(self, lines):
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        open(log, 'a').write('\n'.join(lines) + '\n')
        return log

    def calibrate_head(self, cfg, res, what=''):
        lines = ['%s: %smeasured %d items against budget %g (limit %.0f s), slowest %s' % (
            _now(), what, res['measured'], cfg.get('budget', 55), res['limit'], res['slowest'])]
        for key, secs, cost in res['over']:
            lines.append('  over: %s measured %.0f s, planned %.0f s' % (key, secs, cost))
        return lines

    def step_calibrate(self):
        got = self.calibrate_inputs()
        if got is None:
            return 'skipped'
        cfg, plan, times, fz, times_path = got
        if self.overlap():
            return self.calibrate_frozen_part(cfg, plan, times, fz, times_path)
        res = calibration(plan, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or ())
        lines = self.calibrate_head(cfg, res)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if res['statements_over']:
            self.calibrate_log(lines + ['  statement over: %s measured %.0f s' % x for x in res['statements_over']])
            raise StepFailed(self.STATEMENT_OVER_MSG % (
                res['limit'], ', '.join('%s (%.0f s)' % x for x in res['statements_over']), log))
        if not res['over']:
            self.calibrate_log(lines + ['fits the model; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        pieces_only = all(k.startswith('piece:') for k, _, _ in res['over'])
        ratios = sorted(secs / max(cost, 1.0) for _, secs, cost in res['over'])
        uniform = (pieces_only and len(ratios) >= UNIFORM_MIN and ratios[len(ratios) // 2] >= UNIFORM_RATIO
                   and ratios[-1] <= 2 * ratios[0])
        if pieces_only and not uniform:
            # one slow piece (or a scatter) is something specific, which re-planning has never shrunk
            # (KMedian 106 s through two re-plans, oaiq-031 192 s): stop and say how to find it
            self.calibrate_log(lines)
            raise StepFailed(
                "step 'calibrate': only pieces are over the limit, and re-planning does not shrink a piece:\n%s\n%s Log %s"
                % ('\n'.join(lines[1:]), self.PIECE_HINT, log))
        if uniform:
            # several pieces over plan by a similar large factor: the model underestimates this port, and a
            # re-plan at that factor promotes lemmas to statements (oaiq-073: ratio 3.5-4.3, re-planned at 4,
            # all 364 items fitted)
            res['new_scale'] = round(min(MAX_SCALE, cfg.get('time_scale', 1.5) * ratios[len(ratios) // 2]), 1)
        self.replan(cfg, res['new_scale'], lines)

    def replan(self, cfg, new_scale, lines, step='calibrate'):
        """Raise time_scale and plan again from `plan` (at most MAX_REPLANS times)."""
        n = self.state.get('replans', 0)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if n >= MAX_REPLANS:
            self.calibrate_log(lines)
            raise StepFailed("step '%s': %d re-plans did not fit the budget; items over the limit:\n%s\n"
                             "split by hand (carve.py split) or raise time_scale; log %s" % (step, n, '\n'.join(lines[1:]), log))
        lines.append('re-planning %d/%d: time_scale %g -> %g' % (n + 1, MAX_REPLANS, cfg.get('time_scale', 1.5),
                                                               new_scale))
        self.calibrate_log(lines)
        cfg['time_scale'] = new_scale
        json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
        self.state['replans'] = n + 1
        # work/repairs.json keys its cuts by file name, and a re-plan renumbers the bundles: the old
        # cuts would be re-applied to other files (oaiq-039: bundle 30 lost two imports it needs)
        rp = os.path.join(os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work')), 'repairs.json')
        if os.path.exists(rp):
            os.replace(rp, rp.replace('repairs.json', 'repairs.before-replan-%d.json' % (n + 1)))
        self.invalidate('plan')
        self.restart = True
        print('%s: %s' % (step, lines[-1]), file=sys.stderr, flush=True)

    # -- overlap mode: calibrating the part that freezes, then the pieces -------------------------
    def anything_published(self, cfg):
        """Has any item of this carve (or of a carve it extends: config `frozen`) gone to the platform?"""
        return self.publishing_started() or bool((cfg.get('frozen') or {}).get('bundles'))

    def calibrate_frozen_part(self, cfg, plan, times, fz, times_path):
        """Overlap mode, `calibrate`: the bundles and statements only (pieces are measured after).
        A statement over the limit stops, as ever. Bundles over it: a systematic cost-model error (at
        least UNIFORM_MIN and SYSTEMATIC_FRACTION of the measured bundles) re-plans globally at a
        larger time_scale, but only while nothing is published; otherwise each slow bundle is split
        alone (`carve.py split --only`), every other bundle kept, so only the files importing it
        change and are measured again (dbenbenn 2026-10-29: oaiq-081's bundle 22 of 194 re-planned the
        whole carve)."""
        part = dict(plan, pieces={})
        res = calibration(part, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or ())
        lines = self.calibrate_head(cfg, res, 'bundles and statements: ')
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if res['statements_over']:
            self.calibrate_log(lines + ['  statement over: %s measured %.0f s' % x for x in res['statements_over']])
            raise StepFailed(self.STATEMENT_OVER_MSG % (
                res['limit'], ', '.join('%s (%.0f s)' % x for x in res['statements_over']), log))
        if not res['over']:
            self.calibrate_log(lines + ['fits the model; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        measured = sum(1 for b in plan.get('bundles', []) if (times.get('bundle:' + b['name']) or {}).get('ok'))
        systematic = len(res['over']) >= UNIFORM_MIN and len(res['over']) >= SYSTEMATIC_FRACTION * measured
        if systematic and not self.anything_published(cfg):
            return self.replan(cfg, res['new_scale'], lines)
        n = self.state.get('bundle_splits', 0)
        names = [k.split(':', 1)[1] for k, _, _ in res['over']]
        if n >= MAX_BUNDLE_SPLITS:
            self.calibrate_log(lines)
            raise StepFailed("step 'calibrate': %d rounds of splitting single bundles left these over the limit:\n%s\n"
                             "split by hand (carve.py split CONFIG TIMES --limit S --only NAME) or look at what is "
                             "slow in them (lean -Dprofiler=true); log %s" % (n, '\n'.join(lines[1:]), log))
        lines.append('splitting %s alone (round %d/%d; %s): every other bundle kept, its importers regenerated' % (
            ', '.join(names), n + 1, MAX_BUNDLE_SPLITS,
            'published items are frozen' if self.anything_published(cfg) else
            '%d of %d bundles over: no systematic error' % (len(names), measured)))
        self.calibrate_log(lines)
        self.run_cmds('calibrate', [self.tool('carve', 'split', 'config.json', times_path, '--limit',
                                              '%g' % cfg.get('budget', 55), '--only', ','.join(names))])
        self.state['bundle_splits'] = n + 1
        self.invalidate('gen')
        self.restart = True
        print('calibrate: %s' % lines[-1], file=sys.stderr, flush=True)

    def live_items(self):
        sp = os.path.join(self.d, 'publish', 'run_state.json')
        try:
            st = json.load(open(sp))
        except (OSError, ValueError):
            return set()
        return {x for x, v in st.items() if v.get('state') == 'live'}

    def step_calibrate_pieces(self):
        """Overlap mode: the pieces, measured after the bundles and statements. Nothing published:
        as `calibrate` always did (a uniform overrun re-plans at the ratio, a lone slow piece stops
        with the profiling hint). Once anything is published nothing is re-planned globally: each
        slow piece is split by a frozen re-plan in which only its own declarations cost more (config
        `cost_factors`, its measured / planned ratio), once; a piece still slow after that, or whose
        statement alone is slow (its type is the cost), stops for a person."""
        got = self.calibrate_inputs()
        if got is None:
            return 'skipped'
        cfg, plan, times, _, _ = got
        live = {x.split(':', 1)[1] for x in self.live_items() if x.startswith('piece:')}
        part = dict(plan, bundles=[], stubs={})
        res = calibration(part, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), live,
                          accepted=self.p.get('accept_over') or ())
        lines = self.calibrate_head(cfg, res, 'pieces: ')
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if not res['over']:
            self.calibrate_log(lines + ['pieces fit; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        ratios = sorted(secs / max(cost, 1.0) for _, secs, cost in res['over'])
        uniform = (len(ratios) >= UNIFORM_MIN and ratios[len(ratios) // 2] >= UNIFORM_RATIO
                   and ratios[-1] <= 2 * ratios[0])
        if not self.anything_published(cfg):
            if not uniform:
                self.calibrate_log(lines)
                raise StepFailed(
                    "step 'calibrate_pieces': only pieces are over the limit, and re-planning does not shrink a "
                    "piece:\n%s\n%s Log %s" % ('\n'.join(lines[1:]), self.PIECE_HINT, log))
            return self.replan(cfg, round(min(MAX_SCALE, cfg.get('time_scale', 1.5) * ratios[len(ratios) // 2]), 1),
                               lines, 'calibrate_pieces')
        tried = self.state.setdefault('auto_split', {})
        auto, manual = [], []
        for key, secs, cost in res['over']:
            n = key.split(':', 1)[1]
            st = times.get('statement:' + n) or {}
            if n in tried:
                manual.append('%s: %.0f s, still over after an automatic split (it was %.0f s)' % (
                    key, secs, tried[n]['secs']))
            elif st.get('ok') and st['secs'] >= STATEMENT_SHARE * secs:
                manual.append('%s: %.0f s, of which its statement alone takes %.0f s: the type is the cost, '
                              'and no split helps' % (key, secs, st['secs']))
            elif not (plan.get('pieces') or {}).get(n, {}).get('keep'):
                manual.append('%s: %.0f s, no declarations recorded for it in the plan' % (key, secs))
            else:
                auto.append((n, secs, cost))
        k = self.state.get('piece_replans', 0)
        if auto and k < MAX_REPLANS:
            a = self.state.setdefault('auto_config', {})
            cf = dict(a.get('cost_factors') or {})
            for n, secs, cost in auto:
                r = round(max(1.0, secs / max(cost, 1.0)), 2)
                for x in plan['pieces'][n]['keep']:
                    cf[x] = max(cf.get(x, 1.0), r)
                tried[n] = {'secs': secs, 'cost': cost, 'ratio': r}
            a['cost_factors'] = cf
            self.state['piece_replans'] = k + 1
            lines.append('splitting %d piece(s) by a frozen re-plan (%d/%d), their declarations costed at their '
                         'measured ratio: %s' % (len(auto), k + 1, MAX_REPLANS,
                                                 ', '.join('%s x%.1f' % (n, tried[n]['ratio']) for n, _, _ in auto)))
            for m in manual:
                lines.append('  needs a person (after this round): ' + m)
            self.calibrate_log(lines)
            self.apply_auto(cfg)
            json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
            self.invalidate('plan')
            self.restart = True
            print('calibrate_pieces: %s' % lines[-1 - len(manual)], file=sys.stderr, flush=True)
            return None
        if auto:
            manual += ['%s: %.0f s, %d automatic re-plans already' % ('piece:' + n, secs, k) for n, secs, _ in auto]
        self.calibrate_log(lines + ['  needs a person: ' + m for m in manual])
        raise StepFailed(
            "step 'calibrate_pieces': piece(s) over the %.0f s limit after the bundles and statements began "
            "publishing:\n  %s\nThe published part is frozen (config `frozen` and `forced`, set by the pipeline), so "
            "nothing published is re-planned; the other pieces wait until every piece fits (the release is "
            "written in `publish`). %s A published statement cannot be restated: where its type is the cost, "
            "declaring OpenAI's theorem directly as `theorem _root_.solution` halves the serialization. Forced "
            "lemmas: pipeline.json `forced` plus `config_set.template_forced` (template prose), then "
            "`--from config --publish`. A piece under %d s may go as is and be split after two real timeouts: "
            "pipeline.json `accept_over` [\"piece:NAME\"]. Log %s"
            % (res['limit'], '\n  '.join(manual), self.PIECE_HINT, ACCEPT_CAP, log))

    def source_line(self):
        m = json.load(open(self.meta))
        return ('OpenAI, %s, OpenAI Math Release, %s, https://github.com/openai/math (result family %s), '
                'Apache License 2.0' % (m['title'], m['date'], m['family']))

    def step_publish_prep(self):
        # once publishing began, publish/ is read by a publisher: sync it, never rebuild it
        sync = ['--sync'] if self.overlap() and self.publishing_started() else []
        self.run_cmds('publish_prep', [self.tool('carve_prep', 'publish-prep', self.d, self.source_line(),
                                                 self.p.get('tags') or 'openai-math', *sync)])

    def step_prose(self):
        # the sources map each module to its openai/math path (oaiq-035: guessed paths doubled a directory)
        self.run_cmds('prose', [self.tool('carve_prep', 'prose-template', self.d, '--meta', self.meta,
                                          '--lean-root', self.lean_src)])
        log = os.path.join(self.d, 'logs', 'prose.log')
        need = [l for l in open(log).read().splitlines() if 'needs written prose' in l]
        if need:
            print('NOTE: written prose still needed (goal and forced items); check_text and dryrun fail until '
                  'these files exist:', *need, sep='\n  ', file=sys.stderr)

    def step_check_text(self):
        # overlap mode: the bundles' and statements' text now, the explanations in pieces_prep
        kinds = ['--kinds', 'bundle,statement'] if self.overlap() else []
        self.run_cmds('check_text', [self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'), *kinds)])

    def step_dryrun(self):
        run = 'publish/run_early.json' if self.overlap() else 'publish/run.json'
        self.run_cmds('dryrun', [self.tool('split_run', run)])

    def step_publish(self):
        if not self.p.get('go'):
            return 'skipped'
        self.mark_publishing('step publish started')
        self.save()
        if self.overlap():
            # every piece measured, calibrated and checked (pieces_prep): release them for this plan; a
            # background publisher still running on it sends them, and the final run below resumes it
            plan = os.path.join(self.d, 'publish', 'plan.json')
            rel = {'plan_sha': hashlib.sha1(open(plan, 'rb').read()).hexdigest(), 'pieces': 'all',
                   'released': _now()}
            tmp = os.path.join(self.d, 'publish', 'release.json.tmp')
            json.dump(rel, open(tmp, 'w'), indent=1)
            os.replace(tmp, os.path.join(self.d, 'publish', 'release.json'))
            print('== pieces released for publishing (publish/release.json)', flush=True)
            self.join_publisher('the final publish')
        self.run_cmds('publish', [self.tool('split_run', 'publish/run.json', '--go')])

    # -- overlap mode: the background publisher ---------------------------------------------------
    def publish_lock_key(self):
        return runlock.dir_key('publish', os.path.join(self.d, 'publish', 'run.json'))

    def publisher_running(self):
        """Is a publisher (the background one, or any `split_run --go` on this carve) running?"""
        if runlock.held_by(self.publish_lock_key()):
            return True
        pub = self.state.get('publisher') or {}
        if pub.get('unit') and unit_active(pub['unit']):
            return True
        pid = pub.get('pid')
        return bool(pid) and 'split_run' in runlock.cmdline(pid)

    def join_publisher(self, before, poll=30):
        if not self.publisher_running():
            return
        pub = self.state.get('publisher') or {}
        print('== waiting for the background publisher (%s) to end before %s; progress in publish/PROGRESS.log, '
              'its output in logs/publish_early.log' % (pub.get('unit') or 'pid %s' % pub.get('pid'), before), flush=True)
        while self.publisher_running():
            time.sleep(poll)
        print('== background publisher ended %s' % _now(), flush=True)

    def step_publish_early(self):
        """Overlap mode, with --publish: the bundles and statements (measured, calibrated, checked)
        go to the platform from a background publisher, its own systemd user unit, while the pieces
        are measured. Before it starts, what it will publish is frozen: published/ keeps the plan and
        the files, and config `frozen`, `forced` (the statements) and `template_forced` are set
        (pipeline_state.json `auto_config`), so no later step re-plans or rewrites them."""
        if self.publisher_running():
            print('== a publisher already runs on this carve; it goes on (new items wait for the final publish)',
                  flush=True)
            return None
        if not os.path.exists(os.path.join(self.d, 'publish', 'run_early.json')):
            # publish_prep ran from a skill before overlap mode (a classic carve switched after it): the
            # background publisher would die at once on the missing file
            raise StepFailed("step 'publish_early': no publish/run_early.json (publish_prep ran from a skill before "
                             "overlap mode); run again with `--redo publish_prep` (nothing is published yet)")
        self.freeze_published()
        self.start_publisher()

    def freeze_published(self):
        P = os.path.join(self.d, 'publish')
        plan_file = os.path.join(P, 'plan.json')
        if not os.path.exists(plan_file):
            raise StepFailed("step 'publish_early': no publish/plan.json (publish_prep did not run?)")
        plan = json.load(open(plan_file))
        dst = self.published_dir()
        os.makedirs(os.path.join(dst, 'lib'), exist_ok=True)
        shutil.copy(plan_file, os.path.join(dst, 'plan.json'))
        lib = os.path.join(P, 'out', 'lib')
        for f in sorted(os.listdir(lib)) if os.path.isdir(lib) else ():
            shutil.copy(os.path.join(lib, f), os.path.join(dst, 'lib', f))
        ext = set(plan.get('external') or ())
        stubs = {n for n in plan.get('stubs') or {} if n not in ext}
        named = set(self.p.get('forced') or ()) | set((self.p.get('config_set') or {}).get('forced') or ())
        self.mark_publishing('publish_early froze the published part')
        a = self.state.setdefault('auto_config', {})
        a['frozen'] = {'plan': os.path.join(dst, 'plan.json'), 'bundles': [b['name'] for b in plan.get('bundles') or ()],
                       'lib': os.path.join(dst, 'lib')}
        a['forced'] = sorted(set(a.get('forced') or ()) | stubs)
        a['template_forced'] = sorted(set(a.get('template_forced') or ()) | (stubs - named))
        path = os.path.join(self.d, 'config.json')
        cfg = self.read_config() or {}
        json.dump(self.apply_auto(cfg), open(path, 'w'), indent=1)
        self.save()

    def start_publisher(self):
        log = os.path.join(self.d, 'logs', 'publish_early.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        cmd = ' '.join(shlex.quote(x) for x in self.tool('split_run', 'publish/run_early.json', '--go'))
        sh = '%s >> %s 2>&1; echo "== publisher exit $?" >> %s' % (cmd, shlex.quote(log), shlex.quote(log))
        with open(log, 'a') as f:
            f.write('== %s background publisher (bundles and statements; pieces once released), skill %s\n'
                    % (_now(), os.path.basename(self.snap)))
        unit, pid = None, None
        if shutil.which('systemd-run'):
            unit = publisher_unit(self.d)
            r = subprocess.run(systemd_run_command(unit, self.d, self.env(), sh), capture_output=True, text=True)
            if r.returncode:
                raise StepFailed("step 'publish_early': systemd-run failed: %s" % (r.stderr or r.stdout).strip())
        else:
            pid = subprocess.Popen(['/bin/sh', '-c', sh], cwd=self.d, env=self.env(), start_new_session=True,
                                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL).pid
        self.state['publisher'] = {'unit': unit, 'pid': pid, 'started': _now(), 'log': log}
        self.save()
        print('== background publisher started (%s): bundles and statements now, pieces once released; '
              'progress in publish/PROGRESS.log' % (unit or 'pid %d' % pid), flush=True)

    def step_pieces_prep(self):
        """Overlap mode: the pieces' gates, after calibrate_pieces. publish-prep --sync brings the measured
        pieces (and any new statements) into publish/ without touching what is published (it refuses
        if a published file would change), then prose-template, check-text of the explanations and a dry
        run over every item."""
        meta = ['--meta', self.meta, '--lean-root', self.lean_src]
        self.run_cmds('pieces_prep', [
            self.tool('carve_prep', 'publish-prep', self.d, self.source_line(), self.p.get('tags') or 'openai-math', '--sync'),
            self.tool('carve_prep', 'prose-template', self.d, *meta),
            # the prose was checked in check_text (which re-runs after any re-plan): the explanations only
            # (oaiq-047: check-text over 1,279 statements took 50 min)
            self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'), '--kinds', 'piece'),
            self.tool('split_run', 'publish/run.json')])

    # -- driver -----------------------------------------------------------------------------
    def run(self, stop_after=None, only_redo=(), claim_folder=False):
        self.check_ownership(claim_folder)
        self.publishing_started()                 # record evidence seen now as a state fact
        self.save()
        self.sync_config_set()
        redo = set(only_redo)
        self.ran_now = set()
        while True:
            self.restart = False
            self._run_once(stop_after, redo)
            if not self.restart:
                return self.state
            redo = set()               # a re-plan invalidated what follows the plan: run it again

    STALE_AFTER_PUBLISHING = (
        "step '%s': its input \"%s\" changed since it ran, but publishing has started: re-running it would re-port, "
        "rebuild and re-plan under live items, so nothing was run. Undo the change, or run `--redo %s` to do it "
        "deliberately (an overlap carve keeps its published part frozen; a classic one needs config `frozen` and "
        "`forced`, references/openai-ports.md \"After publishing\").")

    def _run_once(self, stop_after, only_redo):
        for s in self.steps():
            while True:
                st = self.stale_step()
                if not st or STEPS.index(st[0]) > STEPS.index(s):
                    break
                # after publishing, only what this run did deliberately (a --redo, or a step it ran before)
                # may make a step stale; a change from outside (an edited patches file, a port folder
                # rewritten under the carve) stops for a person
                if (st[1] not in self.RULE_KEYS and self.publishing_started() and st[0] not in only_redo
                        and not any(STEPS.index(x) < STEPS.index(st[0]) for x in self.ran_now)):
                    raise StepFailed(self.STALE_AFTER_PUBLISHING % (st[0], st[1], st[0]))
                print(self.stale_message(*st), flush=True)
                if st[1] in self.RULE_KEYS:
                    self.state['steps'].pop(st[0])        # like --redo: its consumers check its output
                else:
                    self.invalidate(st[0])
                self.save()
            rec = self.state['steps'].get(s)
            # --publish always re-enters split_run (it resumes from its run state): after a re-split the
            # recorded `publish` made --publish a 2 s no-op (oaiq-065, oaiq-071)
            again = s in ('publish', 'publish_early') and self.p.get('go')
            if rec and rec['status'] in ('done', 'skipped') and s not in only_redo and not again:
                if s == stop_after:
                    break
                continue
            if s == 'publish' and not self.p.get('go'):
                break                                              # publishing is opt-in, never recorded
            if s == 'publish_early' and not self.p.get('go'):
                if s == stop_after:
                    break
                continue                                           # the pieces are measured all the same
            print('== %s %s' % (s, _now()), flush=True)
            rec = self.state['steps'][s] = {'status': 'running', 'started': _now()}
            hashes = self.step_inputs_hash(s)
            if hashes:
                rec['in'] = hashes
            self.save()
            cfg_before = self.read_config() if s == 'config' else None
            try:
                res = getattr(self, 'step_' + s)()
            except StepFailed as e:
                rec.update(status='failed', finished=_now(), message=str(e).splitlines()[0])
                self.save()
                raise
            rec.update(status=res or 'done', finished=_now())
            self.ran_now.add(s)
            if cfg_before is not None:
                self.config_consumers(cfg_before)
            self.save()
            if self.restart:
                self.state['steps'].pop(s, None)                   # re-run this step after the re-plan
                self.save()
                return
            if s == stop_after:
                break


def lock(d):
    runlock.hold(runlock.dir_key('pipeline', d), 'carve_pipeline.py on %s (pid %d)' % (d, os.getpid()))
