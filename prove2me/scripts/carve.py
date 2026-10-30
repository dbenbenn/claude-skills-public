#!/usr/bin/env python3
"""Split a large ported Lean development into published Definitions bundles, intermediate statements and one carved proof piece per statement.

usage: carve.py graph CONFIG.json                  # DeclGraph + LeanInfo of every module (cached)
       carve.py plan  CONFIG.json [-o PLAN.json]   # bundles, nodes, pieces; checked
       carve.py check CONFIG.json                  # re-check the plan against the graph
       carve.py gen   CONFIG.json [bundles|stubs|pieces|all] [NAME ...]
       carve.py order CONFIG.json                  # the publish DAG, as concurrent waves
       carve.py split CONFIG.json TIMES.json [--limit 60] [--only B1,B2]   # cut only the bundles
                                                   # measured over LIMIT s local (-j1), or only those
                                                   # named; the rest stay as they are
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
                                              # work/repairs.json, to check the regenerated text
   "collapse_mathlib": true,                  # `import Mathlib` instead of the module list
   "external_defs": {"OAI.Erdos3.HasAP": "Definitions.Def_ErdosReciprocal"},  # declarations
                                              # someone else's published bundle provides
   "external_theorems": {"AGT.brouwer_fixed_point": "Theorems.Thm_AGT_brouwer_fixed_point"},
                                              # someone else's published standalone theorems the
                                              # port's modules import (fetch_theorems.py --names):
                                              # handled like external_defs, never carved again
   "statement_suffix": "_s2",                 # published names <name>_s2 (a fresh split of a
                                              # development whose earlier split took the names)
   "chunker": "schedule",                     # bundles by declaration-level list scheduling
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
   "promote_private": ["_private.M.0.OAI.X.lemma"],  # private theorems (graph node names) the
                                              # plan may promote to statements like public ones
                                              # (carve_pipeline: the private lemmas of a slow piece)
   "folded": ["OAI.X.lemma"],                 # statements merged into their importers' pieces after
                                              # planning (carve.fold_statements; e.g. a polymorphic
                                              # statement the verifier's CoeT fallback rejects)
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

Lessons (references/openai-ports.md, "Splitting a large ported proof"): a piece of about 60 s or less at `-j1`
passes the 300 s verifier; splitting only helps when it removes shared recomputation (a
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
    bundle is frozen, so gen writes it byte for byte; without a copy it refuses."""
    fz = cfg.get('frozen') or {}
    dirs = [os.path.expanduser(fz['lib'])] if fz.get('lib') else []
    dirs.append(os.path.join(leaninfo.workspace(), 'Definitions'))
    out, missing = {}, []
    planned = {b['name'] for b in plan['bundles']}
    for b in fz.get('bundles', ()):
        if b not in planned or (names is not None and b not in names):
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
    cost = C.module_costs(g, times, cfg.get('time_scale', 1.5))
    m = cfg.get('measured')
    if m:
        mp = json.load(open(os.path.expanduser(m['plan'])))
        mt = json.load(open(os.path.expanduser(m['bundle_times'])))
        cost = C.calibrate_costs(cost, mp['bundles'], mt, cfg.get('time_scale', 1.5),
                                 m.get('overhead', 5.0))
        print('costs calibrated by %d measured bundles' % sum(1 for v in mt.values() if v.get('ok')))
    return apply_cost_factors(cost, cfg)


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
        Q = C.split_bundles(g, P, slow, cost, (limit - overhead) * scale, cfg.get('bundle_prefix'))
        probs = C.check_plan(g, Q)
        if probs:
            sys.exit('split plan inconsistent:\n' + '\n'.join(probs[:20]))
        backup = plan_path(cfg)[:-5] + '.pre_split.json'
        json.dump(P, open(backup, 'w'), indent=1)
        json.dump(Q, open(plan_path(cfg), 'w'), indent=1)
        old = {b['name'] for b in P['bundles']}
        for n in slow:
            print('split %s (%.0f s): %s' % (n, C.bundle_time(times, n)['secs'], ' '.join(
                b['name'] for b in Q['bundles'] if b['name'] == n or
                (b['name'] not in old and set(b['nodes']) <= set(next(x for x in P['bundles'] if x['name'] == n)['nodes'])))))
        print('%d bundles -> %d; old plan saved as %s' % (len(P['bundles']), len(Q['bundles']), backup))
    elif cmd == 'plan':
        g = load_graph(cfg)
        frozen = None
        if cfg.get('frozen'):
            frozen = (json.load(open(os.path.expanduser(cfg['frozen']['plan']))), cfg['frozen']['bundles'])
        P = C.make_plan(g, cfg['targets'], cfg.get('forced', ()), cfg.get('budget', 60),
                        cfg.get('piece_size', 700_000), cfg.get('bundle_budget', 90),
                        cfg.get('bundle_size', 650_000), cfg.get('band_width', 4), costs(cfg, g),
                        frozen, cfg.get('bundle_prefix', 'Bundle'),
                        external_defs=external_map(cfg),
                        statement_suffix=cfg.get('statement_suffix', ''),
                        external=cfg.get('external', ()),
                        chunker=cfg.get('chunker', 'bands'),
                        pinned=cfg.get('pinned'),
                        bundles_import_statements=cfg.get('bundles_import_statements', True),
                        promote_private=cfg.get('promote_private', ()))
        if cfg.get('folded'):
            P = C.fold_statements(P, cfg['folded'])
        out = rest[rest.index('-o') + 1] if '-o' in rest else plan_path(cfg)
        json.dump(P, open(out, 'w'), indent=1, sort_keys=True)
        worst = sorted(((p['cost'], n) for n, p in P['pieces'].items()), reverse=True)[:5]
        print('%d bundles, %d nodes, %d over budget, %d using sorry -> %s' % (
            len(P['bundles']), len(P['nodes']), len(P['over']), len(P['sorry']), out))
        for c, n in worst:
            print('  %7.1f s  %s' % (c, n))
        probs = C.check_plan(g, P)
        warn_leaks(g, P)
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
        probs = C.check_plan(load_graph(cfg), json.load(open(plan_path(cfg))))
        print('\n'.join(probs) or 'plan OK')
        sys.exit(1 if probs else 0)
    elif cmd == 'gen':
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        what = rest[0] if rest and rest[0] in ('bundles', 'stubs', 'pieces', 'all') else 'all'
        names = set(rest[1:] if rest and rest[0] == what else rest) or None
        kinds = ('bundles', 'stubs', 'pieces') if what == 'all' else (what,)
        frozen_text = published_frozen(cfg, P, names) if 'bundles' in kinds else {}
        patches = json.load(open(os.path.expanduser(cfg['patches']))) if cfg.get('patches') else ()
        r = C.generate(g, P, cfg['out'], kinds,
                       names, cfg.get('external', ()), cfg.get('collapse_mathlib', True),
                       patches, repairs=recorded_repairs(cfg), frozen_text=frozen_text)
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
        stale = unused_patches(patches, r['patches_unused']) if names is None and what == 'all' else []
        for line in stale:
            print(line)
        if r['over_cap'] or stale:
            sys.exit(1)
    elif cmd == 'order':
        order = C.publish_order(json.load(open(plan_path(cfg))), cfg.get('external', ()))
        json.dump(order, open(os.path.join(cfg['work'], 'order.json'), 'w'), indent=1)
        for i, w in enumerate(order['waves']):
            print('wave %d (%d): %s' % (i, len(w), ' '.join(w)))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main(sys.argv)
