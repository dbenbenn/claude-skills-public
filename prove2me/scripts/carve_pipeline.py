#!/usr/bin/env python3
"""The one driver for the module-route carve of a ported openai/math result; runs from a skill snapshot.

usage: carve_pipeline.py DIR [parameters] [--stop-after STEP] [--from STEP] [--redo STEP ...]
                         [--publish] [--upgrade | --snapshot REV] [--allow-dirty] [--list]

DIR is the carve directory. The first run needs the parameters, which are stored in DIR/pipeline.json
(a later run takes none; a different value is refused):
  --folder F            workspace folder Solutions/F for the ported modules
  --root-module M       OpenAI module of the goal's closure root (e.g. OAI.Analysis.Foo.Main)
  --target T            the published theorem to prove (repeat; the first is the config's target)
  --bundle-prefix P     bundle name prefix        [--budget 55]  seconds per piece
  --def Definitions.Def_X   (repeat) published bundles the ports import; default: the import lines
                        of the targets' statements in the workspace
  --forced NAME         (repeat) theorems published as statements of their own
  --patches FILE        single-file patches, filtered for the module route (carve_prep filter-patches)
  --compat-imports narrow|M1,M2   --stdsimplex auto|structure|subtype|off   (oai_port_modules options)
  --fetch [--commit SHA]  run oai_fetch first (DIR/src); else DIR/src/lean (--lean-src) must exist
  --meta FILE           oai_meta.json for the prose templates (default DIR/oai_meta.json)
  --config-set JSON     keys merged into config.json after `carve_prep config` (pinned, frozen, ...)
  --measure-flag=FLAG   (repeat) passed to carve_measure.py, e.g. --measure-flag=--drop-false-edges
  --tags T              publish-prep tags (default openai-math)

Steps (STEPS in p2mlib.carvepipeline): fetch, inputs (the targets' published statements and their Def_
bundles are fetched into the workspace when missing), filter_patches, port, build, wsbuild, config, graph,
extdefs, plan, gen, order, measure, calibrate, publish_prep, prose, check_text, dryrun (split_run.py without
--go: lookups only), and with --publish the real `split_run.py --go`. Each step is idempotent and
resumable: its result is recorded in DIR/pipeline_state.json, its output in DIR/logs/STEP.log, and the
first failure stops the run with the log's tail (re-run the same command to resume). --redo STEP
re-runs one step; --from STEP forgets it and everything after; --stop-after STEP stops there.

Stale steps: each step records content hashes of what it reads from another step (patches file and
sources -> filter_patches; port_patches.json and sources -> port; the ported modules -> build, config).
A resume that finds one changed prints `== stale: STEP ...` and re-runs that step and all later ones, so
editing the patches and running `--redo filter_patches` (or just resuming) re-ports; a --redo whose output
is unchanged leaves the later steps alone. Step `config` fails at once if DIR/oai_meta.json is missing or
its `prefixes` do not match the sources and the root module.

`calibrate` reads what `measure` found: an item (not frozen) measured over 1.6 x the budget raises
config `time_scale` to scale x (its measured seconds / its planned cost), forgets plan..measure and
runs them again (cached files are not re-measured), at most twice; then it stops and lists the
offenders. Nothing is published before it. See p2mlib.carvepipeline.calibration.

The driver re-executes itself from a read-only snapshot of the skill (p2mlib.snapshot) and calls
every sub-tool from that snapshot, so editing or pushing the live skill never affects a running
carve. The snapshot sha is recorded in the state file; a resume reuses it. --upgrade moves a resumed
carve to the current HEAD; --snapshot REV picks a revision; --allow-dirty snapshots an uncommitted
skills tree. Exit 3: another driver already runs this carve. Never write a job-dir driver script:
to change a tool, change the skill (tests first), push, and new runs pick it up."""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p2mlib import carvepipeline as C, snapshot


def parse(argv):
    ap = argparse.ArgumentParser(prog='carve_pipeline.py', usage=__doc__.split('\n\n')[0].replace('usage: ', ''))
    ap.add_argument('dir')
    ap.add_argument('--folder')
    ap.add_argument('--root-module')
    ap.add_argument('--target', action='append', dest='targets')
    ap.add_argument('--bundle-prefix')
    ap.add_argument('--def', action='append', dest='defs')
    ap.add_argument('--forced', action='append')
    ap.add_argument('--patches')
    ap.add_argument('--compat-imports')
    ap.add_argument('--stdsimplex')
    ap.add_argument('--budget', type=float)
    ap.add_argument('--lean-src')
    ap.add_argument('--fetch', action='store_true', default=None)
    ap.add_argument('--commit')
    ap.add_argument('--meta')
    ap.add_argument('--tags')
    ap.add_argument('--config-set', type=json.loads)
    ap.add_argument('--measure-flag', action='append', dest='measure_flags')
    ap.add_argument('--stop-after', choices=C.STEPS)
    ap.add_argument('--from', dest='frm', choices=C.STEPS)
    ap.add_argument('--redo', action='append', choices=C.STEPS, default=[])
    ap.add_argument('--publish', action='store_true')
    ap.add_argument('--upgrade', action='store_true')
    ap.add_argument('--snapshot')
    ap.add_argument('--allow-dirty', action='store_true')
    ap.add_argument('--list', action='store_true')
    return ap.parse_args(argv)


def choose_snapshot(a, state):
    """The snapshot this run uses: the one it is inside, else the recorded one (a resume), else HEAD."""
    here = snapshot.snapshot_root_of(os.path.abspath(__file__))
    rec = (state or {}).get('snapshot')
    if here:
        if rec and rec['sha'] != os.path.basename(here) and not a.upgrade:
            sys.exit('this carve ran from snapshot %s; running from %s. Use --upgrade to move it.' % (rec['sha'], os.path.basename(here)))
        return here
    if a.snapshot:
        return snapshot.snapshot(rev=a.snapshot, allow_dirty=a.allow_dirty)
    if rec and not a.upgrade:
        if os.path.isdir(rec['path']):
            return rec['path']
        return snapshot.snapshot(rev=rec['sha'].split('-dirty-')[0])
    return snapshot.snapshot(allow_dirty=a.allow_dirty)


def load_params(a):
    path = os.path.join(a.dir, 'pipeline.json')
    old = json.load(open(path)) if os.path.exists(path) else None
    given = {k: getattr(a, k) for k in C.PARAM_KEYS if getattr(a, k, None) not in (None, [])}
    if old is None:
        for need in ('folder', 'root_module', 'targets', 'bundle_prefix'):
            if not given.get(need):
                sys.exit('first run of %s needs --folder, --root-module, --target and --bundle-prefix (see usage)' % a.dir)
        os.makedirs(a.dir, exist_ok=True)
        json.dump(given, open(path, 'w'), indent=1)
        return given
    bad = [k for k, v in given.items() if old.get(k) != v]
    if bad:
        sys.exit('parameters differ from the stored %s: %s (edit that file to change them)' % (path, ', '.join(bad)))
    return old


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    a = parse(argv)
    a.dir = os.path.abspath(os.path.expanduser(a.dir))
    sp = os.path.join(a.dir, 'pipeline_state.json')
    state = json.load(open(sp)) if os.path.exists(sp) else None
    params = load_params(a)
    try:
        snap = choose_snapshot(a, state)
    except snapshot.DirtyTree as e:
        sys.exit(str(e))
    here = snapshot.snapshot_root_of(os.path.abspath(__file__))
    if here != snap:
        script = os.path.join(snap, 'prove2me', 'scripts', 'carve_pipeline.py')
        os.execv(sys.executable, [sys.executable, script, *argv])
    if a.list:
        for s in C.STEPS:
            print(s, (state or {}).get('steps', {}).get(s, {}).get('status', '-'))
        return 0
    C.lock(a.dir)
    p = C.Pipeline(a.dir, dict(params, go=a.publish), snap)
    p.state['snapshot'] = {'sha': os.path.basename(snap), 'path': snap}
    if a.frm:
        p.invalidate(a.frm)
    p.save()
    try:
        p.run(stop_after=a.stop_after, only_redo=set(a.redo))
    except C.StepFailed as e:
        print(e, file=sys.stderr)
        return 1
    print('pipeline ok (skill %s)' % os.path.basename(snap))
    return 0


if __name__ == '__main__':
    sys.exit(main())
