#!/usr/bin/env python3
"""The small steps around carving a ported openai/math result (oai_port_modules.py,
oai_build_modules.py, then carve.py graph/plan/gen, carve_measure.py, carve.py split).

usage:
  carve_prep.py config DIR FOLDER ROOT TARGET [--def Definitions.Def_X ...] [--bundle-prefix P]
                       [--forced NAME ...] [--budget 37] [--overhead 0] [--ws WORKSPACE]
      DIR/config.json for the port in Solutions/FOLDER (root module Solutions.FOLDER.ROOT) and the
      published TARGET (an `external` target: its statement is already published), and
      DIR/build_adj.log: every DIR/build_elab*.log merged (later files win). Those logs come from
      oai_build_modules.py --elab-log, which already took the import overhead off, so by default
      nothing more is subtracted (HenonLaneEmden 2026-10-19: subtracting 2.8 s again floored
      nearly every module and pieces came out 5-7x over their estimates); --overhead takes off
      more (floor 0.1 s). external_defs: every declaration of each --def bundle, by full
      name (p2mlib.oaiport.bundle_decl_names); narrow it with `ext-defs` after `carve.py graph`.
      The old config's hand-set keys (patches, external_theorems, frozen, pinned, ...) are kept.
      A port carrying the StdSimplex shim (Solutions/FOLDER/StdSimplexCompat.lean) gets the published
      shim bundle (oaiport.STDSIMPLEX_BUNDLE, once in the workspace) as a --def automatically.
  carve_prep.py ext-defs CONFIG.json [--def Definitions.Def_X ...] [--names FILE] [--lean]
      after `carve.py graph`: external_defs = the bundles' declarations that are graph nodes
      (a field or constructor maps to its owner). --lean lists each bundle's constants with Lean
      (exact, one Lean run per bundle; waits for a lean-cap slot), --names reads them from a file
      (`NAME` or `NAME MODULE` per line); default: parsed from the bundle sources, with Lean asked
      for a bundle that has an anonymous instance (its name is Lean's to generate).
  carve_prep.py filter-patches PATCHES.json LEAN_ROOT OUT.json PREFIX [PREFIX ...]
                       [--compat-ns NS | --root-compat] [--compat FILE] [--header H.lean]
                       [--stdsimplex auto|structure|subtype|off]
      keep the single-file patches (oai_port.py) whose `old` occurs exactly `count` times over the
      modules under the prefixes AS oai_port_modules.py PATCHES THEM (after its import, header,
      core and compat rewrites, macro inlining and guard renames: pass it the same options), for
      oai_port_modules.py; lists the others. Single-file-only patches go too: `"route": "single"`
      or a universe-list reordering (merge.py's `universe` line; a module has its own). Mark a
      patch `"route": "modules"` to keep oai_port.py from applying it.
  carve_prep.py publish-prep DIR SOURCE TAG[,TAG...]
      DIR/publish/: out/ and work/{plan,order,times}.json copied, run.json and
      run_{1_bundles,2_statements,3_pieces}.json for split_run.py, MANIFEST.sha1; prose/ and
      explanations/ created empty (written by hand).
  carve_prep.py bundle-prose PUBLISH_DIR TEMPLATE.md
      prose/<NAME>.md for every bundle: TEMPLATE with {NAME}, {MODULES} (the bundle's `-- module`
      markers), {IMPORTS} (its bundle imports) and {EXTRA} (extra_<NAME>.md beside the template).
  carve_prep.py prose-template DIR [--meta oai_meta.json] [--force]
      after publish-prep, with no model call (p2mlib.prosetemplate): DIR/publish/prose/<slug>.md for
      every intermediate statement and prose/<NAME>.md for every bundle, explanations/<slug>.md
      for every piece proving an intermediate statement, from the plan, out/, work/decl_graph.jsonl
      and DIR/oai_meta.json ({"title", "date", "family", "commit" (full), "paper", "prefixes",
      optional "lean_root"}). The goal and every `forced` node are skipped and listed as needing
      written prose. A file that exists and is not an unchanged template (prose front matter
      `template:`, sha1 in .template.json) is kept unless --force. Run check-text after.
  carve_prep.py check-text PUBLISH_DIR [--search FILE ...] [--allow NAME ...]
      explanation rules (p2mlib.explanation) for explanations/*.md; every Lean-looking name in
      backticks in prose/ and explanations/ must occur in out/, the --search files, Mathlib or Lean
      core (a dotted name also passes by its last component; the workspace modules the files
      import are searched too; --allow names a prose mention of a name this Mathlib lacks, such as
      OpenAI's original that a port replaced); a stub (out/lib/Thm_*.lean) may hold
      no comment (the platform refuses one, and a statement's text freezes). Exit 1 on a problem.
"""
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import oaiport as O  # noqa: E402

COMPAT = os.path.join(os.path.dirname(HERE), 'lean', 'compat_4_34.lean')

KEEP_KEYS = ('patches', 'external_theorems', 'frozen', 'pinned', 'extra_olean_modules', 'repaired',
             'instance_names', 'measured', 'bundles_import_statements', 'literal_patches')


def opt(argv, name, default=None):
    return argv[argv.index(name) + 1] if name in argv else default


def opts(argv, name):
    """Every value after each `name`, up to the next option."""
    out = []
    for i, a in enumerate(argv):
        if a == name:
            for b in argv[i + 1:]:
                if b.startswith('--'):
                    break
                out.append(b)
    return out


def positional(argv, valued, multi=()):
    skip = set()
    for i, a in enumerate(argv):
        if a in valued:
            skip.add(i + 1)
        if a in multi:
            for j in range(i + 1, len(argv)):
                if argv[j].startswith('--'):
                    break
                skip.add(j)
    return [a for i, a in enumerate(argv) if not a.startswith('--') and i not in skip]


def ws_of(argv):
    from p2mlib.workspace import workspace
    return opt(argv, '--ws') or workspace()


# ---------------------------------------------------------------- config

def merged_build_log(d, overhead):
    times = {}
    for f in sorted(glob.glob(os.path.join(d, 'build_elab*.log'))):
        for l in open(f, encoding='utf-8'):
            m = re.search(r'Built (\S+) \(([0-9.]+)s\)', l)
            if m:
                times[m.group(1)] = float(m.group(2))
    return ''.join('✔ [1/1] Built %s (%.1fs)\n' % (m, max(t - overhead, 0.1)) for m, t in times.items())


def bundle_names(ws, defmods):
    """{full name: module} of what each bundle declares, parsed from its source."""
    ext = {}
    for m in defmods:
        names, _ = O.bundle_decl_names(open(os.path.join(ws, *m.split('.')) + '.lean', encoding='utf-8').read())
        for n in names:
            ext[n] = m
    return ext


def bundle_constants(ws, defmods):
    """bundle_names, plus, for a bundle with an anonymous instance, every constant Lean lists for
    it: an anonymous instance's name is Lean's to generate (DiamondDistortion 2026-10-19: the
    published bundle's `instance : Nonempty T.Family` is SegmentSystem.instNonemptyFamily, which
    the port also declares)."""
    ext = {}
    for m in defmods:
        names, anon = O.bundle_decl_names(open(os.path.join(ws, *m.split('.')) + '.lean', encoding='utf-8').read())
        for n in names:
            ext[n] = m
        if anon:
            for n in lean_constants(ws, m):
                ext.setdefault(n, m)
    return ext


def make_config(d, folder, root, target, defmods=(), bundle_prefix=None, forced=(), budget=37,
                overhead=0.0, ws=None, old=None):
    d = os.path.abspath(d)
    defmods = list(defmods)
    # the port carries the StdSimplex shim (oai_port_modules.py) and the shim is published: its
    # declarations are external, so the carve imports the bundle instead of re-publishing them
    shim_bundle = os.path.join(ws, *O.STDSIMPLEX_BUNDLE.split('.')) + '.lean'
    if (os.path.exists(os.path.join(ws, 'Solutions', folder, O.STDSIMPLEX_MODULE + '.lean'))
            and os.path.exists(shim_bundle) and O.STDSIMPLEX_BUNDLE not in defmods):
        print('the port uses the StdSimplex shim: external definitions from', O.STDSIMPLEX_BUNDLE)
        defmods.append(O.STDSIMPLEX_BUNDLE)
    open(os.path.join(d, 'build_adj.log'), 'w', encoding='utf-8').write(merged_build_log(d, overhead))
    cfg = {'src': ws, 'roots': ['Solutions.%s.%s' % (folder, root)], 'prefix': 'Solutions.' + folder,
           'targets': [target], 'forced': list(forced), 'external': [target],
           'external_defs': dict(sorted(bundle_names(ws, defmods).items())),
           'work': d + '/work', 'out': d + '/out',
           'bundle_prefix': bundle_prefix or re.sub(r'\W', '', folder.upper())[:10],
           'budget': budget, 'piece_size': 700000, 'bundle_budget': budget, 'bundle_size': 650000,
           # measured -j1 piece time / estimate with these logs: 1.09-1.37 on WeakPinned's five
           # pieces and DiamondDistortion's (2026-10-19)
           'time_scale': 1.2, 'collapse_mathlib': True, 'chunker': 'schedule', 'statement_suffix': '',
           'build_logs': [d + '/build_adj.log'], 'jobs': 1}
    for k in KEEP_KEYS:
        if old and k in old:
            cfg[k] = old[k]
    return cfg


def cmd_config(argv):
    multi = ('--def', '--forced')
    pos = positional(argv, ('--bundle-prefix', '--budget', '--overhead', '--ws'), multi)
    if len(pos) != 4:
        sys.exit(__doc__)
    d, folder, root, target = pos
    ws = ws_of(argv)
    p = os.path.join(d, 'config.json')
    old = json.load(open(p)) if os.path.exists(p) else None
    cfg = make_config(d, folder, root, target, opts(argv, '--def'), opt(argv, '--bundle-prefix'),
                      opts(argv, '--forced'), float(opt(argv, '--budget', 37)),
                      float(opt(argv, '--overhead', 0.0)), ws, old)
    json.dump(cfg, open(p, 'w'), indent=1, ensure_ascii=False)
    print('%s: %d external definitions, budget %s' % (p, len(cfg['external_defs']), cfg['budget']))


# ---------------------------------------------------------------- external definitions

LEAN_NAMES = '''import {m}
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{m} | throwError "no module"
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then IO.println n
'''


def lean_constants(ws, m):
    """Every non-internal constant module `m` declares (one Lean run)."""
    while int(subprocess.run(['pgrep', '-xc', 'lean'], capture_output=True, text=True).stdout or 0) >= 3:
        time.sleep(5)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write(LEAN_NAMES.format(m=m))
    try:
        r = subprocess.run(['lake', 'env', 'lean', f.name], cwd=ws, capture_output=True, text=True)
    finally:
        os.remove(f.name)
    if r.returncode:
        sys.exit('listing %s failed:\n%s' % (m, (r.stdout + r.stderr)[-1500:]))
    return [l.strip() for l in r.stdout.split('\n') if l.strip() and 'lean-cap' not in l]


def graph_external_defs(names, owner, nodes):
    """{name: module} -> {graph node: module}: a child name maps to its owner node."""
    ext = {}
    for n, m in names.items():
        k = owner.get(n, n)
        if k in nodes:
            ext[k] = m
    return dict(sorted(ext.items()))


def cmd_ext_defs(argv):
    import importlib.util
    pos = positional(argv, ('--names', '--ws'), ('--def',))
    if len(pos) != 1:
        sys.exit(__doc__)
    spec = importlib.util.spec_from_file_location('carve_cli', os.path.join(HERE, 'carve.py'))
    cv = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cv)
    cfg = cv.load_config(pos[0])
    defmods = opts(argv, '--def') or sorted(set((cfg.get('external_defs') or {}).values()))
    if '--names' in argv:
        names = {}
        for l in open(opt(argv, '--names'), encoding='utf-8'):
            w = l.split()
            if w:
                names[w[0]] = w[1] if len(w) > 1 else defmods[0]
    elif '--lean' in argv:
        names = {n: m for m in defmods for n in lean_constants(cfg['src'], m)}
    else:
        names = bundle_constants(cfg['src'], defmods)
    g = cv.load_graph(cfg)
    raw = json.load(open(pos[0]))
    raw['external_defs'] = graph_external_defs(names, g.owner, g.nodes)
    json.dump(raw, open(pos[0], 'w'), indent=1, ensure_ascii=False)
    print(len(raw['external_defs']), 'external definitions')


# ---------------------------------------------------------------- patches

def filter_patches(patches, texts):
    """(kept, [(count, patch)] dropped): a patch is kept when its `old` occurs exactly `count`
    times over the texts (a list, or {name: text}), after the kept patches before it are applied
    (a later patch may amend an earlier one's output). A single-file-only patch
    (oaiport.single_file_only: `"route": "single"`, or a universe-list reordering for merge.py's
    `universe` line) is dropped as ('single-file only', patch)."""
    texts = list(texts.values()) if isinstance(texts, dict) else list(texts)
    keep, drop = [], []
    for p in patches:
        if O.single_file_only(p):
            drop.append(('single-file only', p))
            continue
        n = sum(t.count(p['old']) for t in texts)
        if n == p.get('count', 1):
            keep.append(p)
            texts = [t.replace(p['old'], p['new']) for t in texts]
        else:
            drop.append((n, p))
    return keep, drop


def port_filter_patches(patches, sources, compat_text, compat_ns='OAI', header='', stdsimplex='auto'):
    """filter_patches against the text oai_port_modules.py patches: the modules after its import,
    header, core and compat rewrites (oaiport.module_texts), never OpenAI's raw source
    (ComparatorModel 2026-10-24: the `| zero` case core_rewrites adds counted 0 there and was
    dropped; CubeShuffle: a patch the compat aliases made redundant was kept)."""
    return filter_patches(patches, O.module_texts(sources, 'Solutions.FilterPatches', compat_text,
                                                  compat_ns, header, stdsimplex))


def cmd_filter_patches(argv):
    pos = positional(argv, ('--compat-ns', '--compat', '--header', '--stdsimplex'))
    if len(pos) < 4:
        sys.exit(__doc__)
    src, lean_root, out, prefixes = pos[0], pos[1], pos[2], pos[3:]
    srcs = O.module_sources(lean_root, prefixes)
    compat = open(opt(argv, '--compat', COMPAT), encoding='utf-8').read()
    ns = None if '--root-compat' in argv else opt(argv, '--compat-ns', 'OAI')
    header = open(opt(argv, '--header'), encoding='utf-8').read() if '--header' in argv else ''
    try:
        keep, drop = port_filter_patches(json.load(open(src)), srcs, compat, ns, header,
                                         opt(argv, '--stdsimplex', 'auto'))
    except O.PortError as e:
        sys.exit(str(e))
    for n, p in drop:
        print('dropped (%s): %r' % (n if isinstance(n, str) else '%d occurrences' % n, p['old'][:70]))
    json.dump(keep, open(out, 'w'), ensure_ascii=False, indent=1)
    print('kept', len(keep), 'of', len(keep) + len(drop))


# ---------------------------------------------------------------- publishing

def publish_prep(d, source, tags):
    d = os.path.abspath(d)
    P = os.path.join(d, 'publish')
    for x in ('prose', 'explanations'):
        os.makedirs(os.path.join(P, x), exist_ok=True)
    for f in ('plan.json', 'times.json'):
        if not os.path.exists(os.path.join(d, 'work', f)):
            sys.exit('no work/%s: run carve.py plan/gen and carve_measure.py first' % f)
    if os.path.exists(os.path.join(P, 'out')):
        shutil.rmtree(os.path.join(P, 'out'))
    shutil.copytree(os.path.join(d, 'out'), os.path.join(P, 'out'))
    for f in ('plan.json', 'times.json'):
        shutil.copy(os.path.join(d, 'work', f), os.path.join(P, f))
    # the publish order, from the plan itself (HenonLaneEmden 2026-10-19: carve.py order had not
    # run, and a stale order.json could disagree with the plan)
    from p2mlib import carve as C
    plan = json.load(open(os.path.join(d, 'work', 'plan.json')))
    json.dump(C.publish_order(plan, plan.get('external', ())), open(os.path.join(P, 'order.json'), 'w'), indent=1)
    base = {'plan': P + '/plan.json', 'out': P + '/out', 'prose': P + '/prose',
            'explanations': P + '/explanations', 'state': P + '/run_state.json',
            'log': P + '/PROGRESS.log', 'source': source, 'tags': tags, 'jobs': 4}
    json.dump(base, open(os.path.join(P, 'run.json'), 'w'), indent=1, ensure_ascii=False)
    for i, k, nm in ((1, 'bundle', 'bundles'), (2, 'statement', 'statements'), (3, 'piece', 'pieces')):
        json.dump(dict(base, kinds=[k]), open(os.path.join(P, 'run_%d_%s.json' % (i, nm)), 'w'),
                  indent=1, ensure_ascii=False)
    files = sorted('out/lib/' + f for f in os.listdir(os.path.join(P, 'out', 'lib'))) + \
        sorted('out/solutions/' + f for f in os.listdir(os.path.join(P, 'out', 'solutions')))
    import hashlib
    man = ''.join('%s  %s\n' % (hashlib.sha1(open(os.path.join(P, f), 'rb').read()).hexdigest(), f)
                  for f in files)
    open(os.path.join(P, 'MANIFEST.sha1'), 'w').write(man)
    return P, man


def bundle_prose(plan, lib, template, extra_dir):
    """{bundle name: prose text}."""
    out = {}
    for b in plan['bundles']:
        n = b['name']
        txt = open(os.path.join(lib, 'Def_%s.lean' % n), encoding='utf-8').read()
        mods = sorted(set(m.split('.')[-1] for m in re.findall(r'^-- module (\S+)', txt, re.M)) - {'Compat'})
        imps = b['imports']
        imp = ('It also imports the bundle%s %s of this split.' % (
            's' if len(imps) > 1 else '', ', '.join('`%s`' % i for i in imps))) if imps \
            else 'It imports no other bundle of this split.'
        ex = os.path.join(extra_dir, 'extra_%s.md' % n)
        extra = open(ex, encoding='utf-8').read() if os.path.exists(ex) else ''
        out[n] = template.replace('{NAME}', n).replace('{MODULES}', ', '.join('`%s`' % m for m in mods)) \
            .replace('{IMPORTS}', imp).replace('{EXTRA}', extra)
    return out


def cmd_bundle_prose(argv):
    if len(argv) != 2:
        sys.exit(__doc__)
    P, tp = argv
    plan = json.load(open(os.path.join(P, 'plan.json')))
    for n, t in bundle_prose(plan, os.path.join(P, 'out', 'lib'), open(tp, encoding='utf-8').read(),
                             os.path.dirname(os.path.abspath(tp))).items():
        open(os.path.join(P, 'prose', n + '.md'), 'w', encoding='utf-8').write(t)
        print(n)


# ---------------------------------------------------------------- checking the text

IDENT = re.compile(r"[A-Za-z_][\w'.₀-₉ᵢ]*")
SKIP = {'theorem', 'lemma', 'def', 'fun', 'by', 'sorry', 'import', 'Type', 'Prop', 'True', 'False',
        'solution', 'type_of', 'set_option', 'rfl', 'simp', 'true', 'false'}


def rg_exe():
    # rg is the claude binary run with argv[0] = rg here; else a real rg on PATH
    for p in (os.environ.get('CLAUDE_CODE_EXECPATH'), os.path.expanduser('~/.local/bin/claude')):
        if p and os.path.exists(p):
            return p
    return shutil.which('rg')


def library_roots(ws):
    roots = [os.path.join(ws, '.lake', 'packages', 'mathlib', 'Mathlib')]
    try:
        tc = open(os.path.join(ws, 'lean-toolchain')).read().strip().replace('/', '--').replace(':', '---')
        roots.append(os.path.expanduser('~/.elan/toolchains/%s/src/lean' % tc))
    except OSError:
        pass
    return [r for r in roots if os.path.isdir(r)]


def stub_comments(texts):
    """Names of the stubs ({name: text}) holding a comment."""
    return sorted(n for n, t in texts.items() if re.search(r'/-|--', t))


def missing_names(md_text, local, in_library, skip=()):
    """The Lean-looking names in backticks found neither in `local` text nor by `in_library`."""
    md_text = re.sub(r'^---\n.*?\n---\n', '', md_text, flags=re.S)      # front matter: source URLs
    md_text = re.sub(r'^```.*?^```[ \t]*$', '', md_text, flags=re.M | re.S)   # fenced Lean: verbatim code
    bad = []
    for span in sorted(set(re.findall(r'`([^`\n]+)`', md_text))):
        if '/' in span or span.endswith('.lean'):
            continue
        for nm in IDENT.findall(span):
            nm = nm.rstrip('.')
            if len(nm) < 3 or nm in SKIP or nm in skip or nm in bad:
                continue
            last = nm.split('.')[-1]
            hit = any(re.search(r'(?<![\w])%s(?![\w\'])' % re.escape(x), local) for x in {nm, last}) \
                or in_library(last)
            if not hit:
                bad.append(nm)
    return bad


def imported_workspace_files(ws, files):
    """The workspace's Definitions/ and Theorems/ modules the files import (the published bundles
    and statements, an external target's among them) that are not among the files."""
    names = {os.path.basename(f) for f in files}
    out = []
    for f in files:
        mods = re.findall(r'^import ((?:Definitions|Theorems)\.\S+)', open(f, encoding='utf-8').read(), re.M)
        b = os.path.basename(f)
        if b.startswith('Sol_'):          # a solution's own statement (the external target's is published)
            mods.append('Theorems.Thm_' + b[4:-5])
        for m in mods:
            p = os.path.join(ws, *m.split('.')) + '.lean'
            if os.path.basename(p) not in names and p not in out and os.path.exists(p):
                out.append(p)
    return out


def cmd_check_text(argv):
    from p2mlib import explanation as E
    pos = positional(argv, ('--ws',), ('--search', '--allow'))
    if len(pos) != 1:
        sys.exit(__doc__)
    P = pos[0]
    gen = glob.glob(P + '/out/lib/*.lean') + glob.glob(P + '/out/solutions/*.lean')
    ws = ws_of(argv)
    extra = opts(argv, '--search') + imported_workspace_files(ws, gen)
    local = '\n'.join(open(f, encoding='utf-8').read() for f in gen + extra)
    skip = {re.sub(r'^(Def|Thm|Sol)_', '', os.path.basename(f)[:-5]) for f in gen + extra}
    skip |= set(opts(argv, '--allow'))
    roots, rg, seen = library_roots(ws), rg_exe(), {}

    def in_library(name):
        if name not in seen:
            seen[name] = bool(rg) and any(subprocess.run(['rg', '-q', '-w', '-F', name, r], executable=rg).returncode == 0
                                          for r in roots)
        return seen[name]
    bad = 0
    for f in sorted(glob.glob(P + '/prose/*.md') + glob.glob(P + '/explanations/*.md')):
        t = open(f, encoding='utf-8').read()
        if '/explanations/' in f:
            for pr in E.problems(t):
                bad += 1
                print('EXPLANATION %s: %s' % (os.path.basename(f), pr))
        for nm in missing_names(t, local, in_library, skip):
            bad += 1
            print('NOT FOUND %s: %s' % (os.path.basename(f), nm))
    stubs = {os.path.basename(f): open(f, encoding='utf-8').read() for f in glob.glob(P + '/out/lib/Thm_*.lean')}
    for n in stub_comments(stubs):
        bad += 1
        print('COMMENT IN STUB', n)
    if not rg:
        print('warning: no rg found, Mathlib and core not searched')
    print('%d problems' % bad)
    sys.exit(1 if bad else 0)


def cmd_prose_template(argv):
    from p2mlib import prosetemplate as T
    pos = positional(argv, ('--meta',))
    if len(pos) != 1:
        sys.exit(__doc__)
    meta = json.load(open(opt(argv, '--meta'), encoding='utf-8')) if '--meta' in argv else None
    rep = T.write_templates(pos[0], meta, force='--force' in argv)
    for r in rep['written']:
        print('wrote', r)
    for r in rep['kept']:
        print('kept (written prose; --force to replace)', r)
    for r in rep['needs_written']:
        print('needs written prose:', r)
    print('%d written, %d kept, %d need written prose; next: carve_prep.py check-text %s/publish' % (
        len(rep['written']), len(rep['kept']), len(rep['needs_written']), pos[0].rstrip('/')))


CMDS = {'config': cmd_config, 'ext-defs': cmd_ext_defs, 'filter-patches': cmd_filter_patches,
        'publish-prep': lambda a: print(publish_prep(a[0], a[1], a[2].split(','))[1]) if len(a) == 3 else sys.exit(__doc__),
        'bundle-prose': cmd_bundle_prose, 'prose-template': cmd_prose_template,
        'check-text': cmd_check_text}


def main(argv):
    if not argv or argv[0] not in CMDS:
        sys.exit(__doc__)
    CMDS[argv[0]](argv[1:])


if __name__ == '__main__':
    main(sys.argv[1:])
