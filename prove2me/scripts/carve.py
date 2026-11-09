#!/usr/bin/env python3
"""Split a large ported Lean development into published Definitions bundles, intermediate statements and one carved proof piece per statement.

usage: carve.py graph CONFIG.json                  # DeclGraph + LeanInfo of every module (cached)
       carve.py plan  CONFIG.json [-o PLAN.json]   # bundles, nodes, pieces; checked
       carve.py check CONFIG.json                  # re-check the plan against the graph
       carve.py gen   CONFIG.json [bundles|stubs|pieces|all] [NAME ...]
       carve.py order CONFIG.json                  # the publish DAG, as concurrent waves
       carve.py split CONFIG.json TIMES.json [--limit 60] [--only B1,B2]   # cut only the bundles
                                                   # measured over LIMIT s local (-j1), or only those
                                                   # named; the rest stay as they are. With --only, parts
                                                   # forming a chain leave the old name on the top part
                                                   # (importers unchanged); else the changed importers
                                                   # go into pipeline.json `thaw` once publish_early ran.
                                                   # The old plan: work/plan.pre_split.json (older
                                                   # copies plan.pre_split.N.json)
       carve.py split-piece CONFIG.json NODE[=K][,NODE[=K]...] [--parts K] [--no-gen]   # split slow pieces
                                                   # alone: promote lemmas each keeps into new
                                                   # statements until every part costs at most 1/K of
                                                   # it (default 2), then gen just those files; every
                                                   # other item stays as it is. Old plan:
                                                   # work/plan.pre_split_piece.json; prints
                                                   # `SPLIT_PIECES {"NODE": [new nodes]}`
       carve.py fold  CONFIG.json NODE ...         # NODEs stop being statements: their pieces go into
                                                   # every importer's piece (plan in place, config `folded`)

Use it when a port's closure is far over prove2.me's 1 MiB cap or 300 s verifier (Erdős 3: 4136
modules, 52 MB). It replaces the five per-mission carvers of 2026-10-07/08 (Kaplansky,
Deligne–Drinfeld, Catalan, Chowla, Erdős 3); the library is p2mlib/carve.py, the Lean side
lean/DeclGraph.lean and lean/LeanInfo.lean --idents, the tests tests/test_carve.py.

CONFIG.json (paths may use ~):
  {"src": "~/claude/prove2me_workspace",     # source root of the modules (default: workspace)
   "roots": ["Solutions.OAIErdos3.Main"],     # compiled modules to import (lake build them first)
   "prefix": "Solutions.OAIErdos3",           # the development's modules
   "targets": ["OAI.Erdos3.mainTheorem"],     # theorems to prove
   "forced": [],                              # extra nodes to publish
   "external": ["OAI.Erdos3.mainTheorem"],    # statements someone else already published
   "work": "DIR",                             # decl_graph.jsonl, plan.json, order.json
   "out": "DIR",                              # lib/ and solutions/ (OpenAI code: do not commit)
   "bundle_prefix": "OAIErdos3B",             # bundles OAIErdos3B000, B001, …
   "budget": 60, "piece_size": 700000,        # per piece: estimated seconds, bytes
   "bundle_budget": 90, "bundle_size": 650000, "band_width": 4,
   "build_logs": ["build.log"],               # `lake build` output: per-module times for costs
   "time_scale": 1.5,                         # verifier time / local build time
   "frozen": {"plan": "old_plan.json", "bundles": ["OAIErdos3B000"]},  # published: keep as is;
                                              # gen writes each byte for byte from its published
                                              # copy ("lib": DIR, else the workspace's
                                              # Definitions/, fetch_theorems.py) and refuses
                                              # without one; "repairs": the old carve's
                                              # work/repairs.json, to check the regenerated text;
                                              # "thawed": file names frozen but not live, which
                                              # gen generates (carve_pipeline sets it, q128)
   "collapse_mathlib": true,                  # `import Mathlib` instead of the module list
   "external_defs": {"OAI.Erdos3.HasAP": "Definitions.Def_ErdosReciprocal"},  # declarations
                                              # someone else's published bundle provides
   "external_theorems": {"AGT.brouwer_fixed_point": "Theorems.Thm_AGT_brouwer_fixed_point"},
                                              # someone else's published standalone theorems the
                                              # port's modules import (fetch_theorems.py --names):
                                              # handled like external_defs, never carved again
   "statement_suffix": "_s2",                 # published names <name>_s2 (a fresh split of a
                                              # development whose earlier split took the names)
   "statement_suffixes": {"A.b": "_m"},       # one statement published again as A.b_m (q151)
   "monomorphic": ["A.b"],                    # statement and piece written at universe 0 (q151)
   "chunker": "schedule",                     # bundles by declaration-level list scheduling;
                                              # "closure": grouped by what members depend on, so an
                                              # importer's chain is what it needs (q149, q153)
   "closure_slack": 5.5,                      # closure chunker: planned seconds a declaration may add
                                              # to a bundle's chain or its importers' (default budget/10)
                                              # (shallow); "bands" (default) cuts along modules
   "pinned": {"benign": ["OAI.Higman.IsBenign"]},  # groups of definitions, each its own small
                                              # bundle first (after frozen ones), closed under
                                              # dependencies: statements using only them import
                                              # only them; a non-definition is refused
   "bundles_import_statements": true,         # default: a target/forced theorem that definitions
                                              # need is published as a statement and the bundles
                                              # needing it import it (false: a CarveError)
   "patches": "patches.json",                 # [{literal_old, literal_new, why}] applied to every
                                              # generated file: proof fixes, never source edits
   "measured": {"plan": "work/plan_measured.json", "bundle_times": "work/bundle_times.json",
                "overhead": 5.0},                # local -j1 times of that plan's bundles: costs
                                                 # rescaled to them, so a re-plan splits the heavy
   "cost_factors": {"OAI.X.lemma": 4.0},      # a declaration's cost times this (carve_pipeline:
                                              # the declarations of a piece measured over its
                                              # plan, by that ratio, for a frozen re-plan)
   "promote_shared": true,                    # promote a theorem many pieces keep (make_plan)
   "kernel_lemmas_in_bundles": true,          # theorems proved by `decide` become bundle material:
                                              #   checked once, imported by the pieces (q148); do not
                                              #   use: closures grow past the verifier (q152)
   "promote_private": ["_private.M.0.OAI.X.lemma"],  # private theorems (graph node names) the
                                              # plan may promote to statements like public ones
                                              # (carve_pipeline: the private lemmas of a slow piece);
                                              # true: every private theorem (q152)
   "folded": ["OAI.X.lemma"],                 # statements merged into their importers' pieces after
                                              # planning (carve.fold_statements; e.g. a polymorphic
                                              # statement the verifier's CoeT fallback rejects)
   "no_promote": ["OAI.X.lemma"],             # theorems the plan never promotes to statements (q160:
                                              # the lemmas of accepted pieces, so a re-plan for one
                                              # slow piece splits only that one; carve_pipeline's
                                              # automatic split of a slow piece adds the lemmas of
                                              # the live pieces, less the slow ones', itself)
   "repaired": {"OAI.Erdos3.x": ["OAI.Erdos3.y"]},  # stubbed sorry a patch replaces: name -> what the patched proof uses (or a plain list)
                                              # (generation refuses a file still containing sorry)
   "instance_names": "work/instance_names.json"}  # {port name: name in a published bundle} for
                                              # anonymous local instances a frozen bundle kept
                                              # unnamed (Lean's name there differs from the
                                              # port's); consumers re-activate them by it

Steps. `graph` runs DeclGraph on the compiled roots (one Lean process) and LeanInfo --idents,
elaborating each module (`jobs` at a time, default 3, cached under ~/.cache/p2m/leaninfo by the
module's content and its imports' builds): it records what Lean resolved each identifier to and
the instances each command used, which the carver reads instead of guessing from text. It costs
about the module's own compile CPU time, so the first run is as slow as building the port again;
the identifiers it still had to read from text are listed at the end. `plan` writes the plan and refuses one `check_plan` faults: a definition
missing from the bundles a member needs (Erdős 3 B006 `A.space`, B024 `coord`), a bundle or
piece resting on `sorry` (B022). `gen` writes out/lib/Def_<bundle>.lean, out/lib/Thm_<slug>.lean
(statement stubs, `:= by sorry`) and out/solutions/Sol_<slug>.lean, with the cuts carve_measure
recorded in work/repairs.json re-applied and frozen bundles exactly as published, each piece with OpenAI's copy
of its target renamed `<name>_oai` and `theorem solution : type_of% @<name>_oai := @<name>_oai`
(without the rename, submissions came back WA). Compile each bundle locally, `-j1`, before
publishing it. `order` prints waves: everything in a wave publishes concurrently once the earlier
waves are published (bundles, then statements after their bundles, then pieces). Publishing and
submitting stay with the mission's own scripts and publish_standalone.py / submit_solution.py.

Lessons (references/openai-ports.md, "Splitting a large ported proof"): a piece under 100 s CPU (PIECE_CAP;
verifier-failures.md, "Proof submissions time out") passes the 300 s verifier; splitting only helps when it removes shared recomputation (a
definition re-elaborated by every piece costs every piece); no macro or syntax commands (the
carver refuses to keep one; notation is fine).
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p2mlib import carve as C  # noqa: E402
from p2mlib import leaninfo  # noqa: E402


def load_config(path):
    cfg = json.load(open(path))
    for k in ('src', 'work', 'out'):
        if k in cfg:
            cfg[k] = os.path.expanduser(cfg[k])
    cfg.setdefault('src', leaninfo.workspace())
    cfg.setdefault('work', os.path.join(os.path.dirname(os.path.abspath(path)), 'carve_work'))
    cfg.setdefault('out', os.path.dirname(os.path.abspath(path)))
    os.makedirs(cfg['work'], exist_ok=True)
    return cfg


def external_map(cfg):
    """external_defs and external_theorems together: both are someone else's published
    declarations, kept out of bundles and pieces and imported by the files that use them."""
    ext = dict(cfg.get('external_defs') or {})
    ext.update(cfg.get('external_theorems') or {})
    return ext


def also_modules(cfg):
    """Modules outside the prefix DeclGraph must report: those of the external theorems."""
    return sorted(set((cfg.get('external_theorems') or {}).values()))


def graph_path(cfg):
    return os.path.join(cfg['work'], 'decl_graph.jsonl')


def plan_path(cfg):
    return cfg.get('plan') or os.path.join(cfg['work'], 'plan.json')


def recorded_repairs(cfg):
    """carve_measure's recorded cuts (work/repairs.json), and those of the carve whose bundles are
    frozen here (`frozen.repairs`), {file name: [cut]}: gen re-applies them."""
    out = {}
    for p in (((cfg.get('frozen') or {}).get('repairs')), os.path.join(cfg['work'], 'repairs.json')):
        if p and os.path.exists(os.path.expanduser(p)):
            for f, cuts in json.load(open(os.path.expanduser(p), encoding='utf-8')).items():
                out.setdefault(f, [])
                out[f] += [c for c in cuts if c not in out[f]]
    return out


def published_frozen(cfg, plan, names=None):
    """{bundle: published text} of the frozen bundles gen is asked for, from `frozen.lib` or the
    workspace's Definitions/ (where fetch_theorems.py writes published bundles). A published
    bundle is frozen, so gen writes it byte for byte; without a copy it refuses. `frozen.thawed`
    (file names, set by carve_pipeline) are frozen but not live, e.g. stopped on the verifier: they
    are generated, with the post-carve patches (q128)."""
    fz = cfg.get('frozen') or {}
    dirs = [os.path.expanduser(fz['lib'])] if fz.get('lib') else []
    dirs.append(os.path.join(leaninfo.workspace(), 'Definitions'))
    out, missing = {}, []
    planned = {b['name'] for b in plan['bundles']}
    thawed = set(fz.get('thawed') or ())
    for b in fz.get('bundles', ()):
        if b not in planned or (names is not None and b not in names) or 'Def_%s.lean' % b in thawed:
            continue
        p = next((os.path.join(d, 'Def_%s.lean' % b) for d in dirs
                  if os.path.exists(os.path.join(d, 'Def_%s.lean' % b))), None)
        if p:
            out[b] = open(p, encoding='utf-8').read()
        else:
            missing.append(b)
    if missing:
        sys.exit('frozen bundle(s) %s: no published copy in %s. A published bundle is written exactly '
                 'as published: fetch it (fetch_theorems.py --names %s) or set frozen.lib to the '
                 'directory holding Def_<name>.lean' % (' '.join(missing), ' or '.join(dirs), ' '.join(missing)))
    return out


def published_frozen_stubs(cfg, plan, names=None):
    """{file name: published text} of the statements gen is asked for that have a copy in `frozen.lib`
    (publish_early keeps the live files there). A live statement cannot change, and a frozen re-plan
    of an overlap carve regenerated 13 of them with another import or `attribute [-instance]` line
    (oaiq-081, 2026-10-30), which stopped the re-split of two slow pieces."""
    fz = cfg.get('frozen') or {}
    if not fz.get('lib'):
        return {}
    lib = os.path.expanduser(fz['lib'])
    external = set(cfg.get('external', ())) | set(plan.get('external', ()))
    thawed = set(fz.get('thawed') or ())
    out = {}
    for n in plan['nodes']:
        if n in external or (names is not None and n not in names):
            continue
        fn = 'Thm_%s.lean' % C.slug(C.statement_name(plan, n))
        p = os.path.join(lib, fn)
        if os.path.exists(p) and fn not in thawed:
            out[fn] = open(p, encoding='utf-8').read()
    return out


def load_graph(cfg):
    if not os.path.exists(graph_path(cfg)):
        sys.exit('no %s: run `carve.py graph` first' % graph_path(cfg))
    g = C.Graph.load(graph_path(cfg), cfg['src'])
    C.mark_repaired(g, cfg.get('repaired') or [])
    names = cfg.get('instance_names') or {}
    if isinstance(names, str):
        names = json.load(open(os.path.expanduser(names), encoding='utf-8'))
    g.instance_names = names
    return g


def costs(cfg, g):
    times = {}
    for f in cfg.get('build_logs') or []:
        times.update(C.parse_build_log(open(os.path.expanduser(f), encoding='utf-8').read()))
    if not times:
        print('no build logs: costs by size (%d bytes/s)' % cfg.get('bytes_per_second', 2000))
        return apply_cost_factors(C.size_costs(g, cfg.get('bytes_per_second', 2000)), cfg)
    cost = C.module_costs(g, times, cfg.get('time_scale', 1.5), kernel=C.kernel_weights(g))
    m = cfg.get('measured')
    if m:
        mp = json.load(open(os.path.expanduser(m['plan'])))
        mt = json.load(open(os.path.expanduser(m['bundle_times'])))
        cost = C.calibrate_costs(cost, mp['bundles'], mt, cfg.get('time_scale', 1.5),
                                 m.get('overhead', 5.0))
        print('costs calibrated by %d measured bundles' % sum(1 for v in mt.values() if v.get('ok')))
    return apply_cost_factors(cost, cfg)


def bundle_theorems(cfg, g):
    """The theorems config `kernel_lemmas_in_bundles` makes bundle material: the computational leaves,
    proved by `decide` (C.kernel_weights) from definitions and other such leaves only, each then checked
    once in a bundle instead of in every piece using it. A proof that also uses a theorem of another kind
    stays a statement's business (q148: taking every `decide` proof pulled the analysis into bundles)."""
    if not cfg.get('kernel_lemmas_in_bundles'):
        return set()
    out = {k for k in C.kernel_weights(g) if g.nodes[k].theorem and not g.nodes[k].instance}
    while True:
        bad = {k for k in out if any(d != k and d in g.nodes and g.nodes[d].theorem and d not in out
                                     for d in g.nodes[k].deps)}
        if not bad:
            return out
        out -= bad


def apply_cost_factors(cost, cfg):
    """config `cost_factors` {declaration: factor}: the declarations of a piece measured over its
    plan cost that much more (carve_pipeline), so a frozen re-plan promotes lemmas inside it only."""
    f = cfg.get('cost_factors') or {}
    if not f:
        return cost
    out = dict(cost)
    for k, x in f.items():
        if k in out:
            out[k] = out[k] * x
    return out


def print_chains(g, P, cfg):
    """The heaviest bundle import chains of plan P, each with its verdict against the server's 300 s."""
    rows = C.chain_report(g, P)
    print('heaviest bundle import chains (planned s; what importing brings, and what its members need; '
          'a cold verifier worker builds the whole chain within the item\'s %d s):' % C.SERVER_COLD)
    for r in rows:
        print('  %7.1f s  %s (%d bundles; members need %.1f s): %s' % (
            r['chain'], r['bundle'], r['bundles'], r['needs'], C.chain_verdict(r['chain'])))
    if any(r['needs'] < r['chain'] / 2 for r in rows) and cfg.get('chunker') != 'closure':
        print('NOTE: chains well over their members\' need are bundle mixing; "chunker": "closure" removes it')
    if rows and rows[0]['chain'] > C.CHAIN_WARN:
        print('WARNING: chains over %d s planned; q154\'s measured chains ran 1.5x its plan (369 s planned, 576 s '
              'measured) and cold-worker retries cleared up to ~340 s local (q172). calibrate re-checks them '
              'measured; re-plan before publish_early if they stay far over' % C.CHAIN_WARN)


def keep_backup(path, tag):
    """The path to save the plan at `path` under before changing it: PLAN<tag>.json, an older copy there
    first moved to the first free PLAN<tag>.N.json (q172: a second split round overwrote the first's)."""
    base = path[:-5] + tag
    if os.path.exists(base + '.json'):
        i = 1
        while os.path.exists('%s.%d.json' % (base, i)):
            i += 1
        os.replace(base + '.json', '%s.%d.json' % (base, i))
    return base + '.json'


def changed_importer_files(P, Q, split):
    """The out/lib files (Def_*.lean, Thm_*.lean) of plan P's bundles and statements, other than the
    `split` bundles themselves, whose imports differ in plan Q."""
    old = {b['name']: b for b in P['bundles']}
    out = ['Def_%s.lean' % b['name'] for b in Q['bundles']
           if b['name'] in old and b['name'] not in split and b.get('imports') != old[b['name']].get('imports')]
    ext = set(Q.get('external') or ())
    out += ['Thm_%s.lean' % C.slug(C.statement_name(Q, n)) for n, st in sorted((Q.get('stubs') or {}).items())
            if n not in ext and n in (P.get('stubs') or {}) and st.get('bundles') != P['stubs'][n].get('bundles')]
    return sorted(out)


def thaw_importers(config_path, files):
    """Add `files` to pipeline.json `thaw` beside a carve_pipeline config once publish_early has frozen
    the plan (published/plan.json): a frozen file never posted is locked until thawed, so gen would keep
    its old imports (q172, OAIQ106E011's seven importers). False when there is no such carve."""
    d = os.path.dirname(os.path.abspath(config_path))
    pp = os.path.join(d, 'pipeline.json')
    if not (os.path.exists(pp) and os.path.exists(os.path.join(d, 'published', 'plan.json'))):
        return False
    p = json.load(open(pp))
    p['thaw'] = sorted(set(p.get('thaw') or ()) | set(files))
    tmp = pp + '.tmp'
    json.dump(p, open(tmp, 'w'), indent=1)
    os.replace(tmp, pp)
    return True


def bundles_to_split(bundles, times, limit, only=None):
    """The bundles `carve.py split` cuts: measured over `limit`, or (with `only`) just those named."""
    slow = C.slow_bundles(bundles, times, limit)
    return [n for n in slow if n in only] if only else slow


def unused_patches(patches, unused):
    """One line per post-carve patch (config `patches`) that matched no generated file."""
    return ['PATCH MATCHING NO GENERATED FILE: %r%s' % (
        pt['literal_old'][:160], ' -- ' + pt['why'] if pt.get('why') else '')
        for pt in patches if pt['literal_old'] in unused]


def report_fallbacks(g, limit=10):
    """Identifiers read from text because the elaborated port recorded nothing for them (a module
    with errors, a notation body): the text reading is a guess (p2mlib.carve.Graph.reading)."""
    fb = sorted(set(g.fallbacks))
    if fb:
        print('%d identifiers read from text (no record of what Lean resolved them to):' % len(fb))
        for f, line, tok in fb[:limit]:
            print('  %s:%d %s' % (f, line, tok))
        if len(fb) > limit:
            print('  ... %d more' % (len(fb) - limit))
    if g.lost_instances:
        print('%d local instances used but not re-emitted: %s' % (len(g.lost_instances), g.lost_instances[:limit]))


def report_duplicates(g, limit=20):
    """Theorems two modules declare under one full name (Lean imports both when the statements
    agree; p2mlib.carve.Graph._split_duplicates): which module's copy keeps the name and how the
    others are renamed in every carved file (oaiq-088/090/095/096: hand port patches before)."""
    dups = getattr(g, 'duplicates', ())
    if not dups:
        return
    print('%d theorem name(s) declared by more than one module; each copy is carved as its own '
          'declaration, the one most modules see under the name:' % len(dups))
    for nm, keep, new, guessed in dups[:limit]:
        print('  DUPLICATE %s: %s keeps it; %s' % (nm, keep, '; '.join(
            '%s renamed %s' % (m, n.rsplit('.', 1)[-1]) for m, n in new)))
    if len(dups) > limit:
        print('  ... %d more' % (len(dups) - limit))
    if any(gs for _, _, _, gs in dups):
        print('  (this decl graph predates DeclGraph\'s per-module copies: the other copies\' proofs '
              'are read from their source only; re-run `carve.py graph` for their exact dependencies)')


def warn_leaks(g, P, limit=30):
    """Instances a carved file shows a declaration its module never saw (C.instance_leaks): if a
    file then fails where the port compiled (a rewrite no longer matching, a different
    elaboration), look here first (RationalHitting 2026-10-24, witnessCharZero)."""
    lines = C.leak_summary(C.instance_leaks(g, P))
    if lines:
        print('WARNING: %d instances are visible in carved files to declarations whose modules never '
              'saw them (type class search may take another path there):' % len(lines))
        for l in lines[:limit]:
            print('  ' + l)
        if len(lines) > limit:
            print('  ... %d more (p2mlib.carve.instance_leaks)' % (len(lines) - limit))


def run_gen(cfg, g, P, kinds, names):
    """`gen`: write the plan's files (`names`: only those bundles and nodes); exits 1 on a file over the
    cap or a stale patch."""
    frozen_text = published_frozen(cfg, P, names) if 'bundles' in kinds else {}
    frozen_stubs = published_frozen_stubs(cfg, P, names) if 'stubs' in kinds else {}
    patches = json.load(open(os.path.expanduser(cfg['patches']))) if cfg.get('patches') else ()
    r = C.generate(g, P, cfg['out'], kinds,
                   names, cfg.get('external', ()), cfg.get('collapse_mathlib', True),
                   patches, repairs=recorded_repairs(cfg), frozen_text=frozen_text,
                   frozen_stubs=frozen_stubs, monomorphic=set(cfg.get('monomorphic', ())))
    for f in r['files']:
        print('%9d  %s' % (r['sizes'][f], f))
    for f, c in r['stale_repairs']:
        print('STALE REPAIR %s | %s' % (f, c.replace('\n', ' ')[:120]))
    for f in r['frozen_drift']:
        print('FROZEN %s: written as published; the generated text differs from it (the plan '
              'or a patch changed what this bundle would be; check what imports it)' % f)
    warn_leaks(g, P)
    report_fallbacks(g)
    for f in r['over_cap']:
        print('OVER 1 MiB', f)
    # a patch no generated file contains is stale (a collision suffix `_r<hex>_<n>` that changed
    # with the snapshot, a statement folded away): a full gen fails on it, as filter_patches does
    # for port patches (oaiq-123); a partial gen cannot tell
    stale = unused_patches(patches, r['patches_unused']) if names is None and len(kinds) == 3 else []
    why = {pt['literal_old']: pt.get('why') for pt in patches}
    # q128: a patch whose only match is a frozen file written as published reached no copy at all
    stale += ['PATCH ON A FROZEN FILE ONLY: %r%s matches %s, which is frozen (published or being '
              'published) and written as published, without the patch. A live item cannot change; '
              'one that is not live (stopped before it went live) takes patches once carve_pipeline '
              'lists it in config frozen.thawed' % (o[:160], ' -- ' + why[o] if why.get(o) else '', f)
              for o, f in r['patches_frozen']] if names is None and len(kinds) == 3 else []
    for line in stale:
        print(line)
    if r['over_cap'] or stale:
        sys.exit(1)


def split_many(g, P, specs, cost, cfg, parts=2.0, skip_unsplittable=False):
    """split-piece over `specs` ('NODE[=PARTS],...'): (new plan, {node: new statements}, {node: why} unsplittable).
    With skip_unsplittable a piece with nothing to promote is noted and the others split (carve_pipeline; q153
    2026-11-09: one single-declaration piece stopped a round of 176); otherwise its CarveError propagates."""
    Q, done, unsplittable = P, {}, {}
    for spec in specs.split(','):
        n, _, k = spec.partition('=')
        if n not in Q['pieces']:
            raise C.CarveError('%s has no piece in the plan' % n)
        keep = Q['pieces'][n]['keep']
        target = sum(cost.get(x, 0.0) for x in keep) / max(float(k) if k else parts, 1.0)
        try:
            Q, new = C.split_piece(g, Q, n, target, cost, cfg.get('chunker', 'bands'),
                                   cfg.get('promote_private', ()),
                                   sorted(set(cfg.get('folded', ())) | set(cfg.get('no_promote', ()))))
        except C.CarveError as e:
            if not skip_unsplittable or 'nothing in its piece' not in str(e):
                raise
            unsplittable[n] = str(e)
            print('  %-60s unsplittable: %s' % (n, e))
            continue
        done[n] = new
        for m in [n] + new:
            print('  %-60s %7.2f planned s, %d declarations%s' % (
                m, Q['pieces'][m]['cost'], len(Q['pieces'][m]['keep']), ' (new statement)' if m != n else ''))
    return Q, done, unsplittable


def main(argv):
    if len(argv) < 3:
        sys.exit(__doc__)
    from p2mlib import runlock
    runlock.hold(runlock.dir_key('carve', argv[2]), 'carve.py ' + ' '.join(argv[1:]))
    cmd, cfg = argv[1], load_config(argv[2])
    rest = argv[3:]
    if cmd == 'graph':
        C.run_decl_graph(graph_path(cfg), cfg['prefix'], cfg['roots'], also=also_modules(cfg))
        mods = sorted(C.load_decl_graph(graph_path(cfg))[1])
        # LeanInfo elaborates each module (about its compile time): in parallel, `jobs` at a time
        # (default 3; the lean-cap wrapper bounds it anyway); results are cached, so a rerun only
        # reads the cache
        from concurrent.futures import ThreadPoolExecutor, as_completed
        with ThreadPoolExecutor(int(cfg.get('jobs', 3))) as ex:
            futs = {ex.submit(C.module_info, cfg['src'], m): m for m in mods}
            for i, f in enumerate(as_completed(futs)):
                f.result()
                print('LeanInfo %d/%d %s' % (i + 1, len(mods), futs[f]), flush=True)
        g = load_graph(cfg)
        print('%d modules, %d declaration nodes' % (len(g.modules), len(g.nodes)))
        report_fallbacks(g)
        report_duplicates(g)
    elif cmd == 'split':
        g = load_graph(cfg)
        P = json.load(open(plan_path(cfg)))
        times = json.load(open(os.path.expanduser(rest[0])))
        limit = float(rest[rest.index('--limit') + 1]) if '--limit' in rest else 60.0
        only = rest[rest.index('--only') + 1].split(',') if '--only' in rest else None
        slow = bundles_to_split(P['bundles'], times, limit, only)
        if only and sorted(slow) != sorted(only):
            sys.exit('split --only: %s not measured over %g s (or not in the plan)' % (
                ', '.join(sorted(set(only) - set(slow))), limit))
        scale = cfg.get('time_scale', 1.5)
        overhead = cfg.get('import_overhead', 5.0)
        cost = C.calibrate_costs(costs(cfg, g), P['bundles'], times, scale, overhead)
        # calibrated costs leave out the import overhead, so the budget does too
        # --only (a stopped or late slow bundle): when the parts form a chain the top part keeps the old
        # name, so its importers keep their text (q172)
        Q = C.split_bundles(g, P, slow, cost, (limit - overhead) * scale, cfg.get('bundle_prefix'),
                            top_keeps_name=bool(only))
        probs = C.check_plan(g, Q)
        if probs:
            sys.exit('split plan inconsistent:\n' + '\n'.join(probs[:20]))
        backup = keep_backup(plan_path(cfg), '.pre_split')
        json.dump(P, open(backup, 'w'), indent=1)
        json.dump(Q, open(plan_path(cfg), 'w'), indent=1)
        old = {b['name'] for b in P['bundles']}
        for n in slow:
            print('split %s (%.0f s): %s' % (n, C.bundle_time(times, n)['secs'], ' '.join(
                b['name'] for b in Q['bundles'] if b['name'] == n or
                (b['name'] not in old and set(b['nodes']) <= set(next(x for x in P['bundles'] if x['name'] == n)['nodes'])))))
        print('%d bundles -> %d; old plan saved as %s' % (len(P['bundles']), len(Q['bundles']), backup))
        changed = changed_importer_files(P, Q, slow)
        if changed:
            print('importers whose imports change (%d): %s' % (len(changed), ' '.join(changed)))
            if only and thaw_importers(argv[2], changed):
                print('listed them in pipeline.json `thaw`: publish_early froze them, and gen must regenerate them')
    elif cmd == 'plan':
        g = load_graph(cfg)
        frozen = None
        if cfg.get('frozen'):
            frozen = (json.load(open(os.path.expanduser(cfg['frozen']['plan']))), cfg['frozen']['bundles'])
        # a folded statement is neither forced nor promoted: its importers' pieces are planned with
        # its proof inside them, as they will be after the fold (q160: forced live folded statements
        # made seven in-budget pieces that the fold summed into one of 271 s)
        folded = set(cfg.get('folded', ()))
        P = C.make_plan(g, cfg['targets'], [f for f in cfg.get('forced', ()) if f not in folded],
                        cfg.get('budget', 60),
                        cfg.get('piece_size', 700_000), cfg.get('bundle_budget', 90),
                        cfg.get('bundle_size', 650_000), cfg.get('band_width', 4), costs(cfg, g),
                        frozen, cfg.get('bundle_prefix', 'Bundle'),
                        external_defs=external_map(cfg),
                        statement_suffix=cfg.get('statement_suffix', ''),
                        external=cfg.get('external', ()),
                        chunker=cfg.get('chunker', 'bands'),
                        pinned=cfg.get('pinned'),
                        bundles_import_statements=cfg.get('bundles_import_statements', True),
                        promote_private=cfg.get('promote_private', ()),
                        bundle_theorems=bundle_theorems(cfg, g),
                        promote_shared=cfg.get('promote_shared', False),
                        closure_slack=cfg.get('closure_slack'),
                        exclude=sorted(folded | set(cfg.get('no_promote', ()))))
        if cfg.get('folded'):
            # a folded node the plan did not make a statement (it is `exclude`d from promotion) has
            # nothing to fold; it is still recorded as folded
            P = C.fold_statements(P, [n for n in cfg['folded'] if n in P['pieces']])
            P['folded'] = sorted(set(P.get('folded', [])) | set(cfg['folded']))
        if cfg.get('statement_suffixes'):
            P['statement_suffixes'] = {n: x for n, x in sorted(cfg['statement_suffixes'].items()) if n in P['pieces']}
        out = rest[rest.index('-o') + 1] if '-o' in rest else plan_path(cfg)
        json.dump(P, open(out, 'w'), indent=1, sort_keys=True)
        worst = sorted(((p['cost'], n) for n, p in P['pieces'].items()), reverse=True)[:5]
        print('%d bundles, %d nodes, %d over budget, %d using sorry -> %s' % (
            len(P['bundles']), len(P['nodes']), len(P['over']), len(P['sorry']), out))
        for c, n in worst:
            print('  %7.1f s  %s' % (c, n))
        print_chains(g, P, cfg)
        probs = C.check_plan(g, P)
        warn_leaks(g, P)
        report_duplicates(g)
        for k, us in sorted((P.get('max_only_universes') or {}).items()):
            print('WARNING: statement %s has universe(s) %s only under `max`: the verifier may answer '
                  'WA "stuck at solving universe constraint" (oaiq-124); fold it (carve.py fold) if '
                  'it is not a target, or restate it with every universe bare' % (k, ', '.join(us)))
        for p in probs[:40]:
            print('PROBLEM', p)
        if probs:
            sys.exit(1)
    elif cmd == 'fold':
        if not rest:
            sys.exit('fold: name the statements to fold')
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        Q = C.fold_statements(P, rest)
        probs = C.fold_problems(g, P, Q)
        if probs:
            sys.exit('folded plan inconsistent:\n' + '\n'.join(probs[:20]))
        json.dump(P, open(plan_path(cfg)[:-5] + '.pre_fold.json', 'w'), indent=1, sort_keys=True)
        json.dump(Q, open(plan_path(cfg), 'w'), indent=1, sort_keys=True)
        raw = json.load(open(argv[2]))
        raw['folded'] = sorted(set(raw.get('folded', [])) | set(rest))
        json.dump(raw, open(argv[2], 'w'), indent=1)
        changed = sorted(n for n, p in Q['pieces'].items() if p != P['pieces'].get(n))
        print('folded %s; pieces that change (resubmit them, --replaces their live proofs): %s' % (
            ' '.join(rest), ' '.join(changed)))
    elif cmd == 'check':
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        probs = C.check_plan(g, P)
        print_chains(g, P, cfg)
        print('\n'.join(probs) or 'plan OK')
        sys.exit(1 if probs else 0)
    elif cmd == 'gen':
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        what = rest[0] if rest and rest[0] in ('bundles', 'stubs', 'pieces', 'all') else 'all'
        names = set(rest[1:] if rest and rest[0] == what else rest) or None
        kinds = ('bundles', 'stubs', 'pieces') if what == 'all' else (what,)
        run_gen(cfg, g, P, kinds, names)
    elif cmd == 'split-piece':
        if not rest or rest[0].startswith('--'):
            sys.exit('split-piece: name the pieces (their nodes, comma-separated)')
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        parts = float(rest[rest.index('--parts') + 1]) if '--parts' in rest else 2.0
        cost = costs(cfg, g)
        try:
            Q, done, unsplittable = split_many(g, P, rest[0], cost, cfg, parts, '--skip-unsplittable' in rest)
        except C.CarveError as e:
            sys.exit('split-piece: %s' % e)
        if '--skip-unsplittable' in rest:
            print('UNSPLITTABLE_PIECES ' + json.dumps(unsplittable, sort_keys=True))
        if not done:
            print('SPLIT_PIECES {}')
            return
        probs = C.check_plan(g, Q)
        if probs:
            sys.exit('split-piece: plan inconsistent:\n' + '\n'.join(probs[:20]))
        backup = keep_backup(plan_path(cfg), '.pre_split_piece')
        json.dump(P, open(backup, 'w'), indent=1, sort_keys=True)
        json.dump(Q, open(plan_path(cfg), 'w'), indent=1, sort_keys=True)
        print('old plan saved as %s' % backup)
        if '--no-gen' not in rest:
            run_gen(cfg, g, Q, ('bundles', 'stubs', 'pieces'), set(done) | {m for v in done.values() for m in v})
        print('SPLIT_PIECES ' + json.dumps(done, sort_keys=True))
    elif cmd == 'order':
        order = C.publish_order(json.load(open(plan_path(cfg))), cfg.get('external', ()))
        json.dump(order, open(os.path.join(cfg['work'], 'order.json'), 'w'), indent=1)
        for i, w in enumerate(order['waves']):
            print('wave %d (%d): %s' % (i, len(w), ' '.join(w)))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main(sys.argv)
