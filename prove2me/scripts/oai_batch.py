#!/usr/bin/env python3
"""Port and check many published OAI goals locally, one single-file port each (never submits).

usage: oai_batch.py --dir JOB_DIR [--jobs 3] [--only NAME ...] [--redo] [--section ID]

JOB_DIR layout (created as needed):
  targets.json      [[bytes, theorem name, goal id prefix, mission id, root module, modules], ...]
  patches/<tag>.json  optional per-goal patches ({old, new, count, why}) for oai_port.py
  src/<tag>/lean/   the fetched OpenAI closure (oai_fetch.py)
  run/<tag>/        Sol_*.lean, Chk_*.lean, check.log, result.json (oai_port.py)
  results/<tag>.json  the port's result plus the goal's theorem_id
For each target: the statement and bundles are fetched first (fetch_theorems.py, before any Lean);
a goal that is not Open or not generated from the release commit is skipped. `--jobs` ports run at
once (each holds a lean-cap slot). The monitoring page section (default `oai-goals`) shows counts.
Classification: ready (0 errors, no sorryAx, <= 70 s CPU), slow, needs porting, skipped."""
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.expanduser('~/.claude/skills/monitor'))
import p2m  # noqa: E402
from oai_fetch import COMMIT  # noqa: E402


def tag_of(name):
    return re.sub(r'[^A-Za-z0-9]+', '_', name.replace('OAI.', '', 1)).strip('_').lower()


def classify(r):
    if r.get('skip'):
        return 'skipped'
    if r.get('submitted'):
        return r.get('verdict') or 'submitted'
    if r.get('errors') == 0 and r.get('axioms') and 'sorryAx' not in r['axioms']:
        return 'ready' if r['secs'] <= 70 else 'slow'
    return 'needs porting'


def one(d, t):
    _bytes, name, _gid, _mid, root, _mods = t
    tag = tag_of(name)
    ts = [x for x in (p2m.call('GET', '/theorems?theorem_name=' + name).get('theorems') or [])
          if x.get('theorem_name') == name]
    if not ts:
        return tag, {'target': name, 'skip': 'not found'}
    info = p2m.call('GET', '/theorems/' + ts[0]['theorem_id'])
    if info.get('status') != 'Open':
        return tag, {'target': name, 'skip': 'status ' + str(info.get('status'))}
    if COMMIT[:7] not in (info.get('preamble') or ''):
        return tag, {'target': name, 'skip': 'not generated from %s' % COMMIT[:7]}
    bundles = re.findall(r'^import Definitions\.(\S+)', info.get('preamble') or '', re.M)
    src = os.path.join(d, 'src', tag)
    r = subprocess.run([sys.executable, os.path.join(HERE, 'oai_fetch.py'), src, root],
                       capture_output=True, text=True)
    if r.returncode:
        return tag, {'target': name, 'skip': 'fetch failed: ' + (r.stdout + r.stderr)[-300:]}
    args = [sys.executable, os.path.join(HERE, 'oai_port.py'), name, root, os.path.join(src, 'lean'),
            os.path.join(d, 'run', tag)]
    for b in bundles:
        args += ['--bundle', b]
    pf = os.path.join(d, 'patches', tag + '.json')
    if os.path.exists(pf):
        args += ['--patches', pf]
    r = subprocess.run(args, capture_output=True, text=True)
    out = r.stdout + r.stderr
    m = [l for l in out.split('\n') if l.startswith('{')]
    if not m:
        return tag, {'target': name, 'error': out[-800:]}
    res = json.loads(m[-1])
    res['theorem_id'] = ts[0]['theorem_id']
    return tag, res


def publish_section(d, targets, sid, state='running'):
    try:
        import section
    except ImportError:
        return
    res_dir = os.path.join(d, 'results')
    cls = {}
    for t in targets:
        p = os.path.join(res_dir, tag_of(t[1]) + '.json')
        c = classify(json.load(open(p))) if os.path.exists(p) else 'todo'
        cls[c] = cls.get(c, 0) + 1
    n = len(targets)
    section.publish(sid, title='OpenAI goals: single-file ports', state=state, heartbeat_secs=900,
                    phases=[{'name': 'Ported and checked locally', 'done': n - cls.get('todo', 0), 'total': n},
                            {'name': 'Ready (0 errors, under 70 s)', 'done': cls.get('ready', 0), 'total': n,
                             'note': '%d slow, %d need porting fixes, %d skipped' % (
                                 cls.get('slow', 0), cls.get('needs porting', 0), cls.get('skipped', 0))}],
                    processes=[{'label': 'port batch', 'match': r'oai_batch\.py|oai_port\.py'}])


def main(argv):
    if '--dir' not in argv:
        sys.exit(__doc__)
    d = os.path.abspath(argv[argv.index('--dir') + 1])
    jobs = int(argv[argv.index('--jobs') + 1]) if '--jobs' in argv else 3
    sid = argv[argv.index('--section') + 1] if '--section' in argv else 'oai-goals'
    res_dir = os.path.join(d, 'results')
    os.makedirs(res_dir, exist_ok=True)
    targets = [tuple(t) for t in json.load(open(os.path.join(d, 'targets.json')))]
    only = None
    if '--only' in argv:
        only = [a for a in argv[argv.index('--only') + 1:] if not a.startswith('--')]
    todo = [t for t in targets if (not only or t[1] in only)
            and ('--redo' in argv or not os.path.exists(os.path.join(res_dir, tag_of(t[1]) + '.json')))]
    names = [t[1] for t in todo]
    for i in range(0, len(names), 25):     # statements and bundles, before any Lean runs
        subprocess.run([sys.executable, os.path.join(HERE, 'fetch_theorems.py'), '--names'] + names[i:i + 25],
                       capture_output=True)
    publish_section(d, targets, sid)
    with cf.ThreadPoolExecutor(jobs) as ex:
        for tag, res in ex.map(lambda t: one(d, t), todo):
            json.dump(res, open(os.path.join(res_dir, tag + '.json'), 'w'), indent=1)
            print(tag, classify(res), res.get('secs'), res.get('errors'), res.get('skip') or '', flush=True)
            publish_section(d, targets, sid)
    publish_section(d, targets, sid, state='waiting')


if __name__ == '__main__':
    main(sys.argv[1:])
