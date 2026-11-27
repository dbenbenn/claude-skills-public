"""Carving a development of our own that already sits built in the workspace (`carve_pipeline.py --native`).

An openai/math port is fetched, ported, built and described by `oai_meta.json`; a native tree is none of
that. It lies in WORKSPACE/Solutions/FOLDER as we wrote it, built with `lake build`, importing published
bundles (`Definitions.Def_*`) and published statements (`Theorems.Thm_*`) directly, and its goal theorem
usually proves a statement published long before, under another name. Artin KP (2026-11-16,
p2m-standalone artin/proofs/kp/PACKAGING.md section 3.2) carved one by calling the carve primitives by
hand; this module is what that trial supplied by hand, as pure functions the driver and carve_prep call:

* `closure`: the project modules the roots import, and what they import from outside;
* `external_theorems`, `published_modules`: the published statements the closure imports (config
  `external_theorems`) and every Definitions/Theorems module it reaches (`extra_olean_modules`: the carve's
  own olean directory shadows the workspace's, so measure copies them all);
* `stale_oleans`: the tree must be built, and built after its last edit (the carver cuts by the command
  ranges in the .olean's module, PACKAGING.md / openai-ports.md "Rebuild the port before `carve.py graph`");
* `parse_proves`: `LOCAL=PUBLISHED[@ID]`, the theorem of ours that proves an already published statement;
* `make_config`: config.json as the trial wrote it;
* `build_lines`: the cost model's build log from the per-module elaboration times LeanInfo recorded;
* `target_no_promote`: what rests on the published target and so must stay inside the goal's piece;
* the meta file `native_meta.json`, which replaces `oai_meta.json` for the prose and the source line:

      {"title":  "what the development proves, as a title",
       "credit": "the authors of the development, as they are to be credited",
       "repo":   "https://github.com/OWNER/REPO",          # where its source is kept; null for a private
                                                            # repository: then nothing links to it (credit only)
       "commit": "<40 hex>",                                # the commit the links pin
       "paths":  {"Solutions.Artin.KP": "artin/proofs/kp/lean"},   # workspace module prefix -> directory of the
                                                            # repo holding those modules (longest prefix wins;
                                                            # a module under none is named without a link)
       "ported_from": "what the workspace tree is a port of",  # optional: the tree was edited from the
                                                            # repo's commit (renamed, re-imported), so its lines
                                                            # no longer match: `paths` may then be empty, the
                                                            # repo is linked at the commit and the texts say so
       "paper":  "the paper the development formalizes, with its DOI link",     # optional
       "tags":   "artin,number-theory",                     # optional publish tags (default formalization)
       "license": "…"}                                      # optional
"""
import json
import os
import re

from . import workspace as wslib

IMPORT = re.compile(r'^import[ \t]+(\S+)', re.M)
META_NAME = 'native_meta.json'
META_KEYS = ('title', 'credit', 'repo', 'commit', 'paths')
META_FORMAT = ('{"title", "credit" (the authors of the development), "repo" (URL of the source repository, or '
               'null when it is private: no links then), "commit" (40 hex), "paths" ({workspace module prefix: '
               'directory in the repo}), optional "paper", "tags", "license"} (p2mlib/nativecarve.py)')
NULLABLE_KEYS = {'repo': None, 'paths': {}}   # present, but may be null / empty (a private repository)


def meta_missing(m):
    """The first required key the native meta lacks, or None. `repo` may be null and `paths` empty, but
    both keys must be there, so a private source is a decision, not an omission."""
    for k in META_KEYS:
        if k in NULLABLE_KEYS:
            if k not in m:
                return k
        elif not m.get(k):
            return k
    return None
DEFAULT_TAGS = 'formalization'
IMPORT_OVERHEAD = 3.0       # s: what `import Mathlib` costs a module, as oai_build_modules --elab-log takes off
# hand-set config keys a re-run `config` keeps (carve_prep's KEEP_KEYS, less what make_config derives itself)
KEEP_KEYS = ('patches', 'frozen', 'pinned', 'repaired', 'instance_names', 'measured',
             'bundles_import_statements', 'literal_patches', 'own_namespaces', 'prelude_modules')


class NativeError(Exception):
    pass


def module_file(ws, module):
    return os.path.join(ws, *module.split('.')) + '.lean'


def imports_of(path):
    with open(path, encoding='utf-8', errors='replace') as f:
        return list(dict.fromkeys(IMPORT.findall(f.read())))


def closure(ws, prefix, roots):
    """(project modules, external imports): the modules under `prefix` (a dotted module prefix,
    `Solutions.Artin`) that the roots import, imports before importers, and the sorted modules outside it
    that they import directly (Mathlib, Definitions.*, Theorems.*)."""
    order, seen, ext = [], set(), set()

    def under(m):
        return m == prefix or m.startswith(prefix + '.')

    def visit(m, via):
        if m in seen:
            return
        seen.add(m)
        p = module_file(ws, m)
        if not os.path.exists(p):
            raise NativeError('%s has no source %s%s' % (m, p, ' (imported by %s)' % via if via else ''))
        for x in imports_of(p):
            if under(x):
                visit(x, m)
            else:
                ext.add(x)
        order.append(m)
    for r in roots:
        if not under(r):
            raise NativeError('root module %s is not under the prefix %s (--folder)' % (r, prefix))
        visit(r, None)
    return order, sorted(ext)


def external_theorems(ws, ext):
    """{theorem full name: module} of the published statements among the closure's outside imports
    (config `external_theorems`: imported where used, never carved again)."""
    out = {}
    for m in ext:
        if not m.startswith('Theorems.'):
            continue
        p = module_file(ws, m)
        if not os.path.exists(p):
            raise NativeError('%s is imported but %s is missing: fetch_theorems.py --names' % (m, p))
        full, _ = wslib.statement_decl(open(p, encoding='utf-8').read())
        if not full:
            raise NativeError('%s declares no theorem' % p)
        out[full] = m
    return dict(sorted(out.items()))


def published_modules(ws, ext):
    """Every Definitions/Theorems module the closure reaches, through the stubs' and bundles' own imports
    too (sorted). Without them every measured file failed: the carve's olean/ shadows Definitions/."""
    out, todo = set(), [m for m in ext if m.startswith(('Definitions.', 'Theorems.'))]
    while todo:
        m = todo.pop()
        if m in out:
            continue
        out.add(m)
        p = module_file(ws, m)
        if os.path.exists(p):
            todo += [x for x in imports_of(p) if x.startswith(('Definitions.', 'Theorems.'))]
    return sorted(out)


def olean_file(ws, module):
    return os.path.join(ws, '.lake', 'build', 'lib', 'lean', *module.split('.')) + '.olean'


def stale_oleans(ws, modules):
    """[(module, why)] for the modules whose .olean is missing or older than the source."""
    out = []
    for m in modules:
        o, s = olean_file(ws, m), module_file(ws, m)
        if not os.path.exists(o):
            out.append((m, 'not built'))
        elif os.path.getmtime(o) < os.path.getmtime(s):
            out.append((m, 'older than its source'))
    return out


def parse_proves(specs):
    """({local theorem: published name}, {published name: theorem id}) from `LOCAL=PUBLISHED[@ID]`."""
    proves, ids = {}, {}
    for spec in specs or ():
        local, eq, rest = spec.partition('=')
        name, _, tid = rest.partition('@')
        if not (eq and local and name):
            raise NativeError('--proves %s: write LOCAL=PUBLISHED[@ID], the development\'s theorem and the '
                              'published statement it proves (its prove2.me id, or a prefix of it)' % spec)
        if local == name:
            raise NativeError('--proves %s: the theorem has the published name itself, so it needs no mapping'
                              % spec)
        proves[local] = name
        if tid:
            ids[name] = tid
    return proves, ids


def sources_whole_mathlib(ws, modules):
    return any('Mathlib' in imports_of(module_file(ws, m)) for m in modules)


def make_config(d, ws, folder, roots, targets, proves=None, proves_ids=None, bundle_prefix=None, forced=(),
                budget=55, old=None):
    """config.json for carve.py from a built native tree (PACKAGING.md 3.2, the "config" and "published
    modules" rows). Raises NativeError when the tree is not built or a published statement is missing."""
    d = os.path.abspath(d)
    prefix = 'Solutions.' + folder.strip('/').replace('/', '.')
    proves = dict(proves or {})
    mods, ext = closure(ws, prefix, roots)
    stale = stale_oleans(ws, mods)
    if stale:
        raise NativeError(
            '%d of the %d modules are not built from their current source (%s%s). Native mode carves a tree that '
            'is already built, by the command ranges in its .olean files: run `lake build %s` in %s, then resume'
            % (len(stale), len(mods), ', '.join('%s: %s' % x for x in stale[:5]),
               ', ...' if len(stale) > 5 else '', ' '.join(roots), ws))
    for local, name in proves.items():
        if local not in targets:
            raise NativeError('--proves %s=%s: %s is not a target (--target)' % (local, name, local))
        p = os.path.join(ws, wslib.statement_module(name)[1])
        if not os.path.exists(p):
            raise NativeError('the published statement %s is not in the workspace (%s): fetch_theorems.py '
                              '--names %s' % (name, p, name))
    thms = external_theorems(ws, ext)
    cfg = {'src': ws, 'roots': list(roots), 'prefix': prefix, 'targets': list(targets), 'forced': list(forced),
           # only a target that proves a statement published already is someone else's; the rest get stubs
           'external': [t for t in targets if t in proves],
           'proves': proves, 'proves_ids': dict(proves_ids or {}),
           'external_defs': {}, 'external_theorems': thms,
           'work': d + '/work', 'out': d + '/out',
           'bundle_prefix': bundle_prefix or re.sub(r'\W', '', folder.upper())[:10],
           'budget': budget, 'piece_size': 700000, 'bundle_budget': budget, 'bundle_size': 450000,
           'time_scale': 1.2, 'collapse_mathlib': sources_whole_mathlib(ws, mods), 'chunker': 'schedule',
           'statement_suffix': '', 'build_logs': [d + '/build_adj.log'], 'jobs': 1,
           'extra_olean_modules': published_modules(ws, ext),
           'carry_stub_definitions': True, 'native': True}
    for k in KEEP_KEYS:
        if old and k in old:
            cfg[k] = old[k]
    return cfg


def read_times(path):
    """{module: CPU seconds} from a per-module measurement, one JSON object a line with `module` and
    `build_s` (the CPU of `lean` compiling the module alone, its import included: Artin KP's
    scratch/pkg_kp/times.jsonl). Lines without both are skipped."""
    out = {}
    with open(os.path.expanduser(path), encoding='utf-8') as f:
        for line in f:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict) and r.get('module') and isinstance(r.get('build_s'), (int, float)):
                out[r['module']] = float(r['build_s'])
    return out


def build_lines(modules, secs, overhead=IMPORT_OVERHEAD):
    """(build-log text, modules without a time): one `Built M (N.Ns)` line (what carve.parse_build_log
    reads) per module, its elaboration seconds `secs(module)` less the import overhead (floor 0.1 s)."""
    out, missing = [], []
    for m in modules:
        s = secs(m)
        if s:
            out.append('✔ [1/1] Built %s (%.1fs)\n' % (m, max(s - overhead, 0.1)))
        else:
            missing.append(m)
    return ''.join(out), missing


def target_no_promote(g, proves, target_users):
    """The theorems (other than the proving ones) that rest, through any chain, on a published target of
    `proves`: the plan must never make them statements (config `no_promote`), or their pieces would import
    the statement the goal's piece proves (carve.proves_problems)."""
    out = set()
    for name in proves.values():
        out |= {k for k in target_users(g, name) if g.nodes[k].theorem}
    return sorted(out - set(proves))


# ---------------------------------------------------------------- the meta file

def load_meta(path):
    return json.load(open(path, encoding='utf-8'))


def meta_problem(path):
    """Why the native meta file cannot be used, or None."""
    if not os.path.exists(path):
        return 'no %s: write %s' % (path, META_FORMAT)
    try:
        m = load_meta(path)
    except ValueError as e:
        return '%s is not JSON (%s)' % (path, e)
    if m.get('prefixes') or m.get('family'):
        return ('%s has `prefixes`/`family`: that is an oai_meta.json (an openai/math port). A native tree '
                'needs %s' % (path, META_FORMAT))
    k = meta_missing(m)
    if k:
        return '%s: no %r; the file is %s' % (path, k, META_FORMAT)
    if not re.fullmatch(r'[0-9a-f]{40}', m['commit']):
        return '%s: commit must be the full 40-hex commit (links pin it)' % path
    if m['repo'] and not m['paths'] and not m.get('ported_from'):
        return ('%s: paths is empty, so nothing would link to %s; give paths, set repo to null, or say in '
                '"ported_from" what the workspace tree is a port of (then the repo is linked at the commit, '
                'without line links)' % (path, m['repo']))
    if not isinstance(m['paths'] or {}, dict):
        return '%s: paths must be {workspace module prefix: directory in the repo}' % path
    return None


def is_native_meta(meta):
    return bool(meta) and 'repo' in meta and 'prefixes' not in meta


def module_path(meta, module):
    """The path in the source repository of a workspace module, or None when no `paths` prefix covers it."""
    best = None
    for pre, where in (meta.get('paths') or {}).items():
        if (module == pre or module.startswith(pre + '.')) and (best is None or len(pre) > len(best[0])):
            best = (pre, where)
    if best is None or module == best[0]:
        return None
    return '%s/%s.lean' % (best[1].strip('/'), module[len(best[0]) + 1:].replace('.', '/'))


def module_link(meta, module, line=None):
    p = module_path(meta, module)
    if not p or not meta.get('repo'):
        return None
    return '%s/blob/%s/%s%s' % (meta['repo'].rstrip('/'), meta['commit'], p, '#L%d' % line if line else '')


def repo_ref(meta):
    """`[host/owner/repo](url) at commit abc1234`, or None for a private source (`"repo": null`); for a
    port (`ported_from`), `…, ported: <what>`."""
    if not meta.get('repo'):
        return None
    r = meta['repo'].rstrip('/')
    out = '[%s](%s/tree/%s) at commit %s' % (re.sub(r'^https?://', '', r), r, meta['commit'], meta['commit'][:7])
    if meta.get('ported_from'):
        out += '; this split is carved from a port of it: %s' % meta['ported_from']
    return out


def source_line(meta):
    """The `source` field of every item the carve publishes."""
    out = '%s, %s' % (meta['credit'], meta['title'])
    if meta.get('repo'):
        out += ', %s (commit %s)' % (meta['repo'].rstrip('/'), meta['commit'][:7])
    if meta.get('ported_from'):
        out += '; ported: %s' % meta['ported_from']
    if meta.get('paper'):
        out += '; after %s' % meta['paper']
    if meta.get('license'):
        out += '; %s' % meta['license']
    return out
