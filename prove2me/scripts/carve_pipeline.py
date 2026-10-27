#!/usr/bin/env python3
"""The one driver for the module-route carve of a ported openai/math result; runs from a skill snapshot.

usage: carve_pipeline.py DIR [parameters] [--stop-after STEP] [--from STEP] [--redo STEP ...]
                         [--publish] [--upgrade | --snapshot REV] [--allow-dirty] [--list] [--detach]
       carve_pipeline.py DIR --wait [MINUTES]

DIR is the carve directory. The first run needs the parameters, which are stored in DIR/pipeline.json
(a later run takes none; a different value is refused):
  --folder F            workspace folder Solutions/F for the ported modules
  --root-module M       OpenAI module of the goal's closure root (e.g. OAI.Analysis.Foo.Main)
  --target T            the published theorem to prove (repeat; the first is the config's target)
  --bundle-prefix P     bundle name prefix        [--budget 55]  seconds per piece
  --def Definitions.Def_X   (repeat) published bundles the ports import (a bare Def_X means
                        Definitions.Def_X); default: the import lines of the targets' statements
  --forced NAME         (repeat) theorems published as statements of their own
  --patches FILE        single-file patches, filtered for the module route (carve_prep filter-patches)
  --compat-imports narrow|M1,M2   --stdsimplex auto|structure|subtype|off   (oai_port_modules options)
  --fetch [--commit SHA]  run oai_fetch first: it copies the root's import closure into DIR/src/lean
                        from the local openai/math clone (~/claude/openai-math), the network only for
                        what the clone lacks. Else DIR/src/lean (or --lean-src) must exist and hold the
                        closure only: port and filter_patches refuse a tree with more than 50 OpenAI
                        modules outside it (a whole openai/math checkout ports every module)
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
offenders. A piece (a proof: resubmittable) measured under 200 s never counts: submit it as is and
split only after two real verifier timeouts. Another item is excused the same way by listing it
(`bundle:NAME`) in pipeline.json `accept_over`. Nothing is published before it. See p2mlib.carvepipeline.calibration.

Long runs: --detach starts the same run as its own systemd user unit (carve-<hash>, output appended to
DIR/logs/driver.log) and returns at once; --wait [MINUTES] (default 100) then blocks until that run
ends, printing its log's tail and exiting with its status, or exits 4 after MINUTES with the step it is
on. Arm --wait, not the driver, in a Bash background command: the harness kills a background command
at 2 h, which killed many drivers mid-build or mid-graph (oaiq-033..049); a killed wait costs nothing,
so re-arm it.

The driver re-executes itself from a read-only snapshot of the skill (p2mlib.snapshot) and calls
every sub-tool from that snapshot, so editing or pushing the live skill never affects a running
carve. The snapshot sha is recorded in the state file; a resume reuses it. --upgrade moves a resumed
carve to the current HEAD; --snapshot REV picks a revision; --allow-dirty snapshots an uncommitted
skills tree. Exit 3: another driver already runs this carve. Never write a job-dir driver script:
to change a tool, change the skill (tests first), push, and new runs pick it up."""
import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time

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
    ap.add_argument('--detach', action='store_true')
    ap.add_argument('--wait', type=float, nargs='?', const=100.0, default=None)
    a = ap.parse_args(argv)
    # a bare bundle name is its Definitions module (oaiq-042: `lake build Def_X` is no target)
    a.defs = [('Definitions.' + d if d.startswith('Def_') else d) for d in a.defs] if a.defs else a.defs
    return a


ENV_KEEP = ('PATH', 'HOME', 'USER', 'LANG', 'LC_ALL')
ENV_PREFIXES = ('P2M_', 'LEAN_', 'ELAN_')


def detach_command(d, argv, script, env):
    """(unit name, systemd-run command) that runs `script d argv` (minus --detach) as a user unit,
    its output and a final `== driver exit N` line appended to d/logs/driver.log."""
    unit = 'carve-' + hashlib.sha1(os.path.realpath(d).encode()).hexdigest()[:10]
    log = os.path.join(d, 'logs', 'driver.log')
    inner = ' '.join(shlex.quote(x) for x in [sys.executable, script, d] + [x for x in argv if x != '--detach'])
    sh = '%s >> %s 2>&1; echo "== driver exit $?" >> %s' % (inner, shlex.quote(log), shlex.quote(log))
    sets = ['--setenv=%s=%s' % (k, v) for k, v in sorted(env.items())
            if k in ENV_KEEP or k.startswith(ENV_PREFIXES)]
    return unit, ['systemd-run', '--user', '--unit=' + unit, '--collect', '--quiet', '-p', 'WorkingDirectory=' + d,
                  *sets, '/bin/sh', '-c', sh]


def wait_result(log_text):
    """The exit status of the last detached run in a driver.log, or None while it runs."""
    i = log_text.rfind('== detached')
    if i < 0:
        return None
    m = re.findall(r'^== driver exit (\d+)$', log_text[i:], re.M)
    return int(m[-1]) if m else None


def detach(a, argv):
    log = os.path.join(a.dir, 'logs', 'driver.log')
    os.makedirs(os.path.dirname(log), exist_ok=True)
    rest = list(argv)
    rest.remove(a.dir_arg)
    unit, cmd = detach_command(a.dir, rest, os.path.abspath(__file__), os.environ)
    with open(log, 'a') as f:
        f.write('== detached %s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
    if shutil.which('systemd-run'):
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode:
            sys.exit('systemd-run failed: %s' % (r.stderr or r.stdout).strip())
        where = 'unit %s' % unit
    else:
        subprocess.Popen(['/bin/sh', '-c', cmd[-1]], cwd=a.dir, start_new_session=True,
                         stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        where = 'a detached process'
    print('started %s; log %s\nwait with: %s %s --wait [MINUTES]   (exit 4: still running; re-arm)'
          % (where, log, os.path.abspath(__file__), a.dir))
    return 0


def wait(a):
    log = os.path.join(a.dir, 'logs', 'driver.log')
    end = time.time() + a.wait * 60
    while True:
        text = open(log, encoding='utf-8', errors='replace').read() if os.path.exists(log) else ''
        if '== detached' not in text:
            sys.exit('no detached run recorded in %s (start one with --detach)' % log)
        r = wait_result(text)
        if r is not None:
            print('\n'.join(text[text.rfind('== detached'):].rstrip().split('\n')[-25:]))
            return r
        if time.time() >= end:
            sp = os.path.join(a.dir, 'pipeline_state.json')
            st = json.load(open(sp)).get('steps', {}) if os.path.exists(sp) else {}
            done = [k for k in C.STEPS if st.get(k, {}).get('status') in ('done', 'skipped')]
            nxt = next((k for k in C.STEPS if k not in done), '?')
            print('still running after %g min: %d steps done, now on %s (log %s). Re-arm --wait.'
                  % (a.wait, len(done), nxt, log))
            return 4
        time.sleep(15)


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
    a.dir_arg = a.dir
    a.dir = os.path.abspath(os.path.expanduser(a.dir))
    if a.wait is not None:
        return wait(a)
    sp = os.path.join(a.dir, 'pipeline_state.json')
    state = json.load(open(sp)) if os.path.exists(sp) else None
    params = load_params(a)
    if a.detach:
        return detach(a, argv)
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
