"""The module-route carve as one resumable pipeline (scripts/carve_pipeline.py).

Replaces the per-job bash drivers (plain_carve.sh, plain_pipeline*.sh, ext_publish.sh ...): one
tracked implementation, every step idempotent and logged, state in DIR/pipeline_state.json, every
sub-tool called from one skill snapshot (p2mlib.snapshot) so editing or pushing the live skill
cannot reach a running carve."""
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time

from . import runlock, snapshot, workspace as wslib

STEPS = ['fetch', 'inputs', 'filter_patches', 'port', 'build', 'wsbuild', 'config', 'graph', 'extdefs', 'plan', 'gen', 'names',
         'order', 'measure', 'calibrate', 'publish_prep', 'prose', 'check_text', 'dryrun', 'publish']
DEFAULT_LEAN_CAP = '~/claude/claude-private/tools/lean-cap'
PARAM_KEYS = ['folder', 'root_module', 'targets', 'bundle_prefix', 'defs', 'forced', 'patches', 'compat_imports',
              'stdsimplex', 'budget', 'lean_src', 'commit', 'fetch', 'config_set', 'measure_flags', 'meta', 'tags']


LIMIT_FACTOR = 1.6      # a measured item this many times the budget is too slow for the verifier
MAX_REPLANS = 2
MAX_SCALE = 8.0


class StepFailed(Exception):
    pass


ACCEPT_CAP = 200        # an accept_over item is excused only below this many seconds
UNIFORM_MIN, UNIFORM_RATIO = 3, 2.5   # pieces over plan by a similar factor >= this: re-plan (oaiq-073)
PIECE_CAP = 150         # a piece (resubmittable) is excused below this: dbenbenn's "submit at ~145 s";
                        # oaiq-031's 192 s piece timed out three times at the verifier's 300 s


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
    ratio = max((secs / max(cost, 1.0) for _, secs, cost in over), default=1.0)
    new_scale = round(min(MAX_SCALE, max(scale * 1.1, scale * ratio)), 1) if over else scale
    return {'over': over, 'ratio': ratio, 'new_scale': new_scale, 'limit': limit, 'measured': measured,
            'slowest': slowest}


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
        todo += [i for i in re.findall(r'^import\s+(\S+)', open(f, encoding='utf-8').read(), re.M)
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
        return {
            'filter_patches': {'patches file': hash_paths([pp] if pp else []),
                               'sources': hash_paths([self.lean_src], ('.lean',))},
            'port': {'filter_patches': hash_paths([self.port_patches()]),
                     'sources': hash_paths([self.lean_src], ('.lean',))},
            'build': {'port': port_out},
            'config': {'port': port_out},
        }.get(s, {})

    def stale_step(self):
        """The first finished step whose recorded input hashes differ from the current ones: (step, what)."""
        for s in STEPS:
            rec = self.state['steps'].get(s)
            if not rec or rec['status'] not in ('done', 'skipped') or not rec.get('in'):
                continue
            now = self.step_inputs_hash(s)
            for k, old in rec['in'].items():
                if k in now and now[k] != old:
                    return s, k
        return None

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
                                                   self.lean_src, self.port_patches(), *self.prefixes(), *self.compat_args())])

    def step_port(self):
        self.check_closure('port')
        a = [self.lean_src, self.p['folder'], *self.prefixes()]
        if self.p.get('patches'):
            a += ['--patches', self.port_patches()]
        self.run_cmds('port', [self.tool('oai_port_modules', *a, *self.compat_args())])

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
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = dict(self.p.get('config_set') or {})

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
        if 'config_set_applied' not in self.state:           # a state from before this was recorded
            self.state['config_set_applied'] = want
            return
        old = self.state['config_set_applied']
        changed = sorted(k for k in set(want) | set(old) if want.get(k) != old.get(k))
        if not changed:
            return
        cfg = json.load(open(path))
        for k in changed:
            if k in want:
                cfg[k] = want[k]
            else:
                cfg.pop(k, None)
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = want
        frm = 'gen' if set(changed) <= {'patches'} else 'plan'
        print('== config_set changed (%s): config.json updated; re-running from %s' % (', '.join(changed), frm), flush=True)
        if frm in self.state['steps']:
            self.invalidate(frm)
        self.save()

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

    def step_order(self):
        self.run_cmds('order', [self.tool('carve', 'order', 'config.json')])

    def step_measure(self):
        # every failing file in one run, not one per ~12 min round (oaiq-051), as the build does
        flags = list(self.p.get('measure_flags') or [])
        if '--keep-going' not in flags:
            flags.append('--keep-going')
        self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *flags)])

    def step_calibrate(self):
        cfg = json.load(open(os.path.join(self.d, 'config.json')))
        work = os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work'))
        plan_path = os.path.expanduser(cfg.get('plan') or os.path.join(work, 'plan.json'))
        times_path = os.path.join(work, 'times.json')
        if not (os.path.exists(plan_path) and os.path.exists(times_path)):
            return 'skipped'                                       # nothing was measured
        plan, times = json.load(open(plan_path)), json.load(open(times_path))
        fz = (cfg.get('frozen') or {}).get('bundles') or ()
        res = calibration(plan, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or ())
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        lines = ['%s: measured %d items against budget %g (limit %.0f s), slowest %s' % (
            _now(), res['measured'], cfg.get('budget', 55), res['limit'], res['slowest'])]
        for key, secs, cost in res['over']:
            lines.append('  over: %s measured %.0f s, planned %.0f s' % (key, secs, cost))
        if not res['over']:
            open(log, 'a').write('\n'.join(lines + ['fits the model; time_scale %g kept' % cfg.get('time_scale', 1.5)]) + '\n')
            return None
        n = self.state.get('replans', 0)
        pieces_only = all(k.startswith('piece:') for k, _, _ in res['over'])
        ratios = sorted(secs / max(cost, 1.0) for _, secs, cost in res['over'])
        uniform = (pieces_only and len(ratios) >= UNIFORM_MIN and ratios[len(ratios) // 2] >= UNIFORM_RATIO
                   and ratios[-1] <= 2 * ratios[0])
        if pieces_only and not uniform:
            # one slow piece (or a scatter) is something specific, which re-planning has never shrunk
            # (KMedian 106 s through two re-plans, oaiq-031 192 s): stop and say how to find it
            open(log, 'a').write('\n'.join(lines) + '\n')
            raise StepFailed(
                "step 'calibrate': only pieces are over the limit, and re-planning does not shrink a piece:\n%s\n"
                "Find what is slow before splitting. (1) Compile the piece's check file with "
                "`lean -o x.olean -Dprofiler=true`: if `.olean serialization` dominates while elaboration is fast, "
                "the statement's type is huge (oaiq-075: 316 s of 341 s, a term re-embedded thousands of times); "
                "name the big term with a def by a patch, do not split. (2) Else "
                "`-Dtrace.profiler=true -Dtrace.profiler.threshold=20000` shows the slow declaration or tactic "
                "(oaiq-074: one fun_prop goal, 53 s). (3) Kernel computation (`decide +kernel`, `native_decide`) or "
                "plain bulk: force the heavy lemmas into statements, listing them in pipeline.json `forced` (a private "
                "one by its graph node name, `_private.<module>.0.<name>`), then --from config (oaiq-031: one 192 s "
                "piece became 20 pieces of ~11 s). Log %s" % ('\n'.join(lines[1:]), log))
        if uniform:
            # several pieces over plan by a similar large factor: the model underestimates this port, and a
            # re-plan at that factor promotes lemmas to statements (oaiq-073: ratio 3.5-4.3, re-planned at 4,
            # all 364 items fitted)
            res['new_scale'] = round(min(MAX_SCALE, cfg.get('time_scale', 1.5) * ratios[len(ratios) // 2]), 1)
        if n >= MAX_REPLANS:
            open(log, 'a').write('\n'.join(lines) + '\n')
            raise StepFailed("step 'calibrate': %d re-plans did not fit the budget; items over the limit:\n%s\n"
                             "split by hand (carve.py split) or raise time_scale; log %s" % (n, '\n'.join(lines[1:]), log))
        lines.append('re-planning %d/%d: time_scale %g -> %g' % (n + 1, MAX_REPLANS, cfg.get('time_scale', 1.5),
                                                               res['new_scale']))
        open(log, 'a').write('\n'.join(lines) + '\n')
        cfg['time_scale'] = res['new_scale']
        json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
        self.state['replans'] = n + 1
        # work/repairs.json keys its cuts by file name, and a re-plan renumbers the bundles: the old
        # cuts would be re-applied to other files (oaiq-039: bundle 30 lost two imports it needs)
        rp = os.path.join(os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work')), 'repairs.json')
        if os.path.exists(rp):
            os.replace(rp, rp.replace('repairs.json', 'repairs.before-replan-%d.json' % (n + 1)))
        self.invalidate('plan')
        self.restart = True
        print('calibrate: %s' % lines[-1], file=sys.stderr, flush=True)

    def source_line(self):
        m = json.load(open(self.meta))
        return ('OpenAI, %s, OpenAI Math Release, %s, https://github.com/openai/math (result family %s), '
                'Apache License 2.0' % (m['title'], m['date'], m['family']))

    def step_publish_prep(self):
        self.run_cmds('publish_prep', [self.tool('carve_prep', 'publish-prep', self.d, self.source_line(),
                                                 self.p.get('tags') or 'openai-math')])

    def step_prose(self):
        # the sources map each module to its openai/math path (oaiq-035: guessed paths doubled a directory)
        self.run_cmds('prose', [self.tool('carve_prep', 'prose-template', self.d, '--meta', self.meta,
                                          '--lean-root', self.lean_src)])
        log = os.path.join(self.d, 'logs', 'prose.log')
        need = [l for l in open(log).read().splitlines() if 'needs written prose' in l]
        if need:
            print('NOTE: written prose still needed (goal and forced items):', *need, sep='\n  ', file=sys.stderr)

    def step_check_text(self):
        self.run_cmds('check_text', [self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'))])

    def step_dryrun(self):
        self.run_cmds('dryrun', [self.tool('split_run', 'publish/run.json')])

    def step_publish(self):
        if not self.p.get('go'):
            return 'skipped'
        self.run_cmds('publish', [self.tool('split_run', 'publish/run.json', '--go')])

    # -- driver -----------------------------------------------------------------------------
    def run(self, stop_after=None, only_redo=()):
        self.sync_config_set()
        redo = set(only_redo)
        while True:
            self.restart = False
            self._run_once(stop_after, redo)
            if not self.restart:
                return self.state
            redo = set()               # a re-plan invalidated what follows the plan: run it again

    def _run_once(self, stop_after, only_redo):
        for s in STEPS:
            while True:
                st = self.stale_step()
                if not st or STEPS.index(st[0]) > STEPS.index(s):
                    break
                print('== stale: %s (its input "%s" changed); re-running it and every later step' % st, flush=True)
                self.invalidate(st[0])
                self.save()
            rec = self.state['steps'].get(s)
            # --publish always re-enters split_run (it resumes from its run state): after a re-split the
            # recorded `publish` made --publish a 2 s no-op (oaiq-065, oaiq-071)
            again = s == 'publish' and self.p.get('go')
            if rec and rec['status'] in ('done', 'skipped') and s not in only_redo and not again:
                if s == stop_after:
                    break
                continue
            if s == 'publish' and not self.p.get('go'):
                break                                              # publishing is opt-in, never recorded
            print('== %s %s' % (s, _now()), flush=True)
            rec = self.state['steps'][s] = {'status': 'running', 'started': _now()}
            hashes = self.step_inputs_hash(s)
            if hashes:
                rec['in'] = hashes
            self.save()
            try:
                res = getattr(self, 'step_' + s)()
            except StepFailed as e:
                rec.update(status='failed', finished=_now(), message=str(e).splitlines()[0])
                self.save()
                raise
            rec.update(status=res or 'done', finished=_now())
            self.save()
            if self.restart:
                self.state['steps'].pop(s, None)                   # re-run this step after the re-plan
                self.save()
                return
            if s == stop_after:
                break


def lock(d):
    runlock.hold(runlock.dir_key('pipeline', d), 'carve_pipeline.py on %s (pid %d)' % (d, os.getpid()))
