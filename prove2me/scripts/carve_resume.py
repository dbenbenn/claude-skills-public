#!/usr/bin/env python3
"""Resume the carves a reboot or power cut interrupted: run at boot by the user unit carve-resume.service.

usage: carve_resume.py [--dry-run] [--roots DIR[:DIR...]] [--since EPOCH]

A carve's driver runs as a transient systemd user unit (carve_pipeline.py --detach) and its background publisher
as another (carve-pub-<hash>); transient units do not come back after a reboot. q153 (2026-11-09): three power
cuts in one afternoon, and each time nothing ran for hours until a person noticed. The OAI queue restarts its own
workers, not a carve taken over by hand.

A carve directory (DIR/*/*/ or DIR/*/ with logs/driver.log and pipeline.json; DIR defaults to ~/.claude/jobs) is
resumed when its last detached run has no `== driver exit` line, its unit is not active, there is no NO_RESUME file
in it, and its driver.log was written since --since (default: the start of the previous boot, from journalctl; a run
that was already dead before it is someone's to look at, not a reboot's). It is started again with the arguments
its --detach recorded (logs/detached.json, carve_pipeline.resume_argv: one-shot options and --upgrade left out, so
it stays on its recorded skill snapshot); a run from before that file gets --publish once publishing began.

Its publisher is restarted the same way when publish_early.log's last `background publisher` line has no
`== publisher exit` after it (on the snapshot and gating pipeline_state.json records), before the driver, so what
was released before the cut goes out at once.
"""
import importlib.util
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('carve_pipeline_cli', os.path.join(HERE, 'carve_pipeline.py'))
CPL = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CPL)

PUB_START = re.compile(r'^== \S+ background publisher ', re.M)
PUB_EXIT = re.compile(r'^== publisher exit ', re.M)
ONE_SHOT = {'--redo': 1, '--from': 1, '--split-piece': 1, '--upgrade': 0, '--detach': 0, '--claim-folder': 0,
            '--wait': 0, '--list': 0}


def resume_argv(argv):
    """The arguments a resumed run repeats: those a --detach run was started with, less the one-shot options
    (--redo/--from/--split-piece and their values, --claim-folder) and --upgrade (a resume stays on its snapshot)."""
    out, skip = [], 0
    for a in argv:
        if skip:
            skip -= 1
            continue
        if a in ONE_SHOT:
            skip = ONE_SHOT[a]
            continue
        out.append(a)
    return out


def unit_active(unit):
    return subprocess.run(['systemctl', '--user', 'is-active', '--quiet', unit]).returncode == 0


def previous_boot_start():
    """Epoch seconds the previous boot started (journalctl), or 24 h ago when unknown."""
    try:
        r = subprocess.run(['journalctl', '--list-boots', '--no-pager', '-o', 'json'], capture_output=True, text=True,
                           timeout=30)
        boots = json.loads(r.stdout)
        if len(boots) >= 2:
            return boots[-2]['first_entry'] / 1e6
    except Exception:
        pass
    return time.time() - 86400


def carve_dirs(roots):
    import glob
    seen = []
    for root in roots:
        root = os.path.expanduser(root)
        for pat in ('*/*', '*'):
            for d in sorted(glob.glob(os.path.join(root, pat))):
                if os.path.exists(os.path.join(d, 'logs', 'driver.log')) and \
                        os.path.exists(os.path.join(d, 'pipeline.json')) and d not in seen:
                    seen.append(d)
    return seen


def _state(d):
    try:
        return json.load(open(os.path.join(d, 'pipeline_state.json')))
    except (OSError, ValueError):
        return {}


def driver_action(d, since, active=unit_active):
    """{'resume': bool, 'why': str, 'argv': [...]} for the carve's driver."""
    log = os.path.join(d, 'logs', 'driver.log')
    text = open(log, errors='replace').read()
    m, rid = CPL.last_detached(text)
    if not m:
        return {'resume': False, 'why': 'never detached'}
    if CPL.wait_result(text) is not None:
        return {'resume': False, 'why': 'its last run ended'}
    if os.path.exists(os.path.join(d, 'NO_RESUME')):
        return {'resume': False, 'why': 'NO_RESUME'}
    if os.path.getmtime(log) < since:
        return {'resume': False, 'why': 'driver.log last written before the previous boot (dead before it)'}
    if active(CPL.unit_name(d)):
        return {'resume': False, 'why': 'its unit is active'}
    try:
        rec = json.load(open(os.path.join(d, 'logs', 'detached.json')))
    except (OSError, ValueError):
        rec = {}
    if rec.get('run_id') == rid and isinstance(rec.get('argv'), list):
        argv = resume_argv(rec['argv'])
    else:
        argv = ['--publish'] if _state(d).get('publishing_started') else []
    return {'resume': True, 'why': 'run %s has no exit line' % rid, 'argv': argv}


def publisher_action(d, since, active=unit_active):
    """{'resume': bool, 'why': str, 'gated': bool, 'snap': path} for the carve's background publisher."""
    log = os.path.join(d, 'logs', 'publish_early.log')
    if not os.path.exists(log):
        return {'resume': False, 'why': 'no publisher log'}
    text = open(log, errors='replace').read()
    starts, exits = list(PUB_START.finditer(text)), list(PUB_EXIT.finditer(text))
    if not starts or (exits and exits[-1].start() > starts[-1].start()):
        return {'resume': False, 'why': 'its last publisher ended'}
    if os.path.exists(os.path.join(d, 'NO_RESUME')):
        return {'resume': False, 'why': 'NO_RESUME'}
    dl = os.path.join(d, 'logs', 'driver.log')
    if os.path.getmtime(log) < since and (not os.path.exists(dl) or os.path.getmtime(dl) < since):
        return {'resume': False, 'why': 'not running at the previous boot'}
    if active(CPL.C.publisher_unit(d)):
        return {'resume': False, 'why': 'its unit is active'}
    st = _state(d)
    snap = (st.get('snapshot') or {}).get('path')
    if not snap:
        return {'resume': False, 'why': 'no recorded skill snapshot'}
    return {'resume': True, 'why': 'its last publisher has no exit line', 'snap': snap,
            'gated': bool((st.get('publisher') or {}).get('gated'))}


START_PUBLISHER = ('import json, sys; sys.path.insert(0, ".")\n'
                   'from p2mlib import carvepipeline as CP\n'
                   'd, snap, gated = sys.argv[1], sys.argv[2], sys.argv[3] == "1"\n'
                   'p = CP.Pipeline(d, json.load(open(d + "/pipeline.json")), snap)\n'
                   'print("already running") if p.publisher_running() else p.start_publisher(gated=gated)\n')


def start(kind, d, a):
    """Start the carve's publisher (on its snapshot) or its driver (carve_pipeline.py --detach)."""
    if kind == 'publisher':
        subprocess.run([sys.executable, '-c', START_PUBLISHER, d, a['snap'], '1' if a['gated'] else '0'],
                       cwd=os.path.join(a['snap'], 'prove2me'), check=False)
    else:
        subprocess.run([sys.executable, os.path.join(HERE, 'carve_pipeline.py'), d] + a['argv'] + ['--detach'],
                       check=False)


def main(argv):
    dry = '--dry-run' in argv
    roots = (argv[argv.index('--roots') + 1] if '--roots' in argv else '~/.claude/jobs').split(':')
    since = float(argv[argv.index('--since') + 1]) if '--since' in argv else previous_boot_start()
    for d in carve_dirs(roots):
        p, r = publisher_action(d, since, unit_active), driver_action(d, since, unit_active)
        for kind, a in (('publisher', p), ('driver', r)):
            if not a['resume']:
                continue
            what = 'restart publisher' if kind == 'publisher' else 'resume driver'
            print('%s %s %s: %s%s' % ('would' if dry else '==', what, d, a['why'],
                                      (' (argv %s)' % ' '.join(a['argv'])) if kind == 'driver' else ''), flush=True)
            if dry:
                continue
            if kind == 'driver':
                with open(os.path.join(d, 'logs', 'driver.log'), 'a') as f:
                    f.write('== %s resumed by carve_resume after a reboot (%s)\n'
                            % (time.strftime('%Y-%m-%d %H:%M:%S'), a['why']))
            start(kind, d, a)


if __name__ == '__main__':
    main(sys.argv[1:])
