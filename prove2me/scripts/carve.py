#!/usr/bin/env python3
"""Split a large ported Lean development into published Definitions bundles, intermediate statements and one carved proof piece per statement.

usage: carve.py graph CONFIG.json                  # DeclGraph + LeanInfo of every module (cached)
       carve.py plan  CONFIG.json [-o PLAN.json]   # bundles, nodes, pieces; checked
       carve.py check CONFIG.json                  # re-check the plan against the graph
       carve.py gen   CONFIG.json [bundles|stubs|pieces|all] [NAME ...]
       carve.py order CONFIG.json                  # the publish DAG, as concurrent waves

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
   "frozen": {"plan": "old_plan.json", "bundles": ["OAIErdos3B000"]},  # published: keep as is
   "collapse_mathlib": true,                  # `import Mathlib` instead of the module list
   "instance_names": "work/instance_names.json"}  # {port name: name in a published bundle} for
                                              # anonymous local instances a frozen bundle kept
                                              # unnamed (Lean's name there differs from the
                                              # port's); consumers re-activate them by it

Steps. `graph` runs DeclGraph on the compiled roots (one Lean process) and LeanInfo, parse-only,
on each module (one at a time, cached under ~/.cache/p2m/leaninfo; slow the first time on a
4000-module port). `plan` writes the plan and refuses one `check_plan` faults: a definition
missing from the bundles a member needs (Erdős 3 B006 `A.space`, B024 `coord`), a bundle or
piece resting on `sorry` (B022). `gen` writes out/lib/Def_<bundle>.lean, out/lib/Thm_<slug>.lean
(statement stubs, `:= by sorry`) and out/solutions/Sol_<slug>.lean, each piece with OpenAI's copy
of its target renamed `<name>_oai` and `theorem solution : type_of% @<name>_oai := @<name>_oai`
(without the rename, submissions came back WA). Compile each bundle locally, `-j1`, before
publishing it. `order` prints waves: everything in a wave publishes concurrently once the earlier
waves are published (bundles, then statements after their bundles, then pieces). Publishing and
submitting stay with the mission's own scripts and publish_standalone.py / submit_solution.py.

Lessons (SKILL.md, "Splitting a large ported proof"): a piece of about 60 s or less at `-j1`
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


def graph_path(cfg):
    return os.path.join(cfg['work'], 'decl_graph.jsonl')


def plan_path(cfg):
    return cfg.get('plan') or os.path.join(cfg['work'], 'plan.json')


def load_graph(cfg):
    if not os.path.exists(graph_path(cfg)):
        sys.exit('no %s: run `carve.py graph` first' % graph_path(cfg))
    g = C.Graph.load(graph_path(cfg), cfg['src'])
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
        return C.size_costs(g, cfg.get('bytes_per_second', 2000))
    return C.module_costs(g, times, cfg.get('time_scale', 1.5))


def main(argv):
    if len(argv) < 3:
        sys.exit(__doc__)
    cmd, cfg = argv[1], load_config(argv[2])
    rest = argv[3:]
    if cmd == 'graph':
        C.run_decl_graph(graph_path(cfg), cfg['prefix'], cfg['roots'])
        mods = sorted(C.load_decl_graph(graph_path(cfg))[1])
        for i, m in enumerate(mods):
            C.module_info(cfg['src'], m)
            print('LeanInfo %d/%d %s' % (i + 1, len(mods), m), flush=True)
        g = load_graph(cfg)
        print('%d modules, %d declaration nodes' % (len(g.modules), len(g.nodes)))
    elif cmd == 'plan':
        g = load_graph(cfg)
        frozen = None
        if cfg.get('frozen'):
            frozen = (json.load(open(os.path.expanduser(cfg['frozen']['plan']))), cfg['frozen']['bundles'])
        P = C.make_plan(g, cfg['targets'], cfg.get('forced', ()), cfg.get('budget', 60),
                        cfg.get('piece_size', 700_000), cfg.get('bundle_budget', 90),
                        cfg.get('bundle_size', 650_000), cfg.get('band_width', 4), costs(cfg, g),
                        frozen, cfg.get('bundle_prefix', 'Bundle'))
        out = rest[rest.index('-o') + 1] if '-o' in rest else plan_path(cfg)
        json.dump(P, open(out, 'w'), indent=1, sort_keys=True)
        worst = sorted(((p['cost'], n) for n, p in P['pieces'].items()), reverse=True)[:5]
        print('%d bundles, %d nodes, %d over budget, %d using sorry -> %s' % (
            len(P['bundles']), len(P['nodes']), len(P['over']), len(P['sorry']), out))
        for c, n in worst:
            print('  %7.1f s  %s' % (c, n))
        probs = C.check_plan(g, P)
        for p in probs[:40]:
            print('PROBLEM', p)
        if probs:
            sys.exit(1)
    elif cmd == 'check':
        probs = C.check_plan(load_graph(cfg), json.load(open(plan_path(cfg))))
        print('\n'.join(probs) or 'plan OK')
        sys.exit(1 if probs else 0)
    elif cmd == 'gen':
        g, P = load_graph(cfg), json.load(open(plan_path(cfg)))
        what = rest[0] if rest and rest[0] in ('bundles', 'stubs', 'pieces', 'all') else 'all'
        names = set(rest[1:] if rest and rest[0] == what else rest) or None
        r = C.generate(g, P, cfg['out'], ('bundles', 'stubs', 'pieces') if what == 'all' else (what,),
                       names, cfg.get('external', ()), cfg.get('collapse_mathlib', True))
        for f in r['files']:
            print('%9d  %s' % (r['sizes'][f], f))
        for f in r['over_cap']:
            print('OVER 1 MiB', f)
        if r['over_cap']:
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
