#!/usr/bin/env python3
"""Publish a section of the machine monitoring page (http://<hostname>:8765/, the `monitor` skill).

A section is one JSON file, MONITOR_HOME/sections/<id>.json (default ~/claude/monitor). The monitor
reads every file there every 30 s; it keeps the history of each phase and works out rates and ETAs,
so a producer only writes its current counts.

From Python:

    sys.path.insert(0, os.path.expanduser('~/.claude/skills/monitor'))
    import section
    section.publish('erdos3-v2', title='Erdős 3 v2', state='running',
                    phases=[{'name': 'Bundles', 'done': 235, 'total': 311, 'note': '7 in flight'}],
                    processes=[{'label': 'publisher', 'match': r'split_run\\.py'}])

From a shell (merges into the existing file; phases are matched by name):

    python3 ~/.claude/skills/monitor/section.py set erdos3-v2 --title 'Erdős 3 v2' \\
        --phase 'Bundles=235/311:running:7 in flight' --process 'publisher=split_run\\.py'
    python3 ~/.claude/skills/monitor/section.py set erdos3-v2 --state done
    python3 ~/.claude/skills/monitor/section.py remove erdos3-v2
"""
import argparse
import json
import os
import re
import sys
import time

STATES = ('running', 'waiting', 'paused', 'done', 'failed')
ID = re.compile(r'^[a-z0-9][a-z0-9-]{0,63}$')


def home_dir(home=None):
    return home or os.environ.get('MONITOR_HOME') or os.path.expanduser('~/claude/monitor')


def path_of(sid, home=None):
    return os.path.join(home_dir(home), 'sections', sid + '.json')


def validate(sec):
    """Every problem with a section dict, as a list of strings (empty: fine)."""
    p = []
    if not isinstance(sec.get('title'), str) or not sec.get('title').strip():
        p.append('title: a non-empty string')
    if not isinstance(sec.get('updated'), (int, float)):
        p.append('updated: a unix time')
    if sec.get('state') not in STATES:
        p.append('state: one of ' + ', '.join(STATES))
    for k in ('heartbeat_secs', 'expires_secs'):
        if k in sec and not (isinstance(sec[k], (int, float)) and sec[k] > 0):
            p.append(k + ': a positive number of seconds')
    for i, ph in enumerate(sec.get('phases', [])):
        if not isinstance(ph, dict) or not isinstance(ph.get('name'), str) or not ph.get('name'):
            p.append('phases[%d].name: a non-empty string' % i)
            continue
        for k in ('done', 'total'):
            if not isinstance(ph.get(k), (int, float)) or isinstance(ph.get(k), bool) or ph.get(k) < 0:
                p.append('phases[%d].%s: a number >= 0' % (i, k))
        if ph.get('state', 'running') not in STATES:
            p.append('phases[%d].state: one of %s' % (i, ', '.join(STATES)))
    for k in ('alerts',):
        if not all(isinstance(a, str) for a in sec.get(k, [])):
            p.append(k + ': strings')
    for i, pr in enumerate(sec.get('processes', [])):
        try:
            re.compile(pr['match'])
            assert isinstance(pr['label'], str)
        except (re.error, KeyError, TypeError, AssertionError):
            p.append('processes[%d]: {"label": str, "match": a Python regex}' % i)
    for i, ln in enumerate(sec.get('links', [])):
        if not (isinstance(ln, dict) and isinstance(ln.get('label'), str) and isinstance(ln.get('url'), str)):
            p.append('links[%d]: {"label": str, "url": str}' % i)
    return p


def write(sid, sec, home=None):
    """Validate and write atomically; raises ValueError on any problem."""
    if not ID.match(sid or ''):
        raise ValueError('id %r: lowercase letters, digits and dashes' % sid)
    probs = validate(sec)
    if probs:
        raise ValueError('section %s: %s' % (sid, '; '.join(probs)))
    f = path_of(sid, home)
    os.makedirs(os.path.dirname(f), exist_ok=True)
    with open(f + '.tmp', 'w') as o:
        json.dump(sec, o, ensure_ascii=False, indent=1)
    os.replace(f + '.tmp', f)
    return f


def publish(sid, title, state='running', phases=(), alerts=(), processes=(), links=(), note='', owner='',
            heartbeat_secs=300, expires_secs=86400, home=None, now=None):
    """Write the whole section. A phase is {'name', 'done', 'total'} plus optional 'state' and 'note'.
    heartbeat_secs: how often this producer updates; three missed updates mark the section stale.
    expires_secs: a done or failed section leaves the page this long after its last update."""
    sec = {'title': title, 'updated': int(now if now is not None else time.time()), 'state': state,
           'note': note, 'owner': owner, 'heartbeat_secs': heartbeat_secs, 'expires_secs': expires_secs,
           'alerts': list(alerts), 'processes': list(processes), 'links': list(links),
           'phases': [dict({'state': 'running', 'note': ''}, **p) for p in phases]}
    return write(sid, sec, home)


def remove(sid, home=None):
    try:
        os.remove(path_of(sid, home))
    except FileNotFoundError:
        pass


def parse_phase(spec):
    """'NAME=DONE/TOTAL[:STATE[:NOTE]]' -> phase dict (the note may contain colons)."""
    m = re.match(r'^([^=]+)=(\d+(?:\.\d+)?)/(\d+(?:\.\d+)?)(?::([a-z]+))?(?::(.*))?$', spec)
    if not m:
        raise argparse.ArgumentTypeError('phase %r: NAME=DONE/TOTAL[:STATE[:NOTE]]' % spec)
    num = lambda x: float(x) if '.' in x else int(x)
    return {'name': m.group(1).strip(), 'done': num(m.group(2)), 'total': num(m.group(3)),
            'state': m.group(4) or 'running', 'note': m.group(5) or ''}


def pair(kind, a, b):
    def f(spec):
        if '=' not in spec:
            raise argparse.ArgumentTypeError('%s %r: LABEL=VALUE' % (kind, spec))
        x, y = spec.split('=', 1)
        return {a: x, b: y}
    return f


def main(argv=None):
    ap = argparse.ArgumentParser(description='Publish a section of the monitoring page.')
    ap.add_argument('--home', help='monitor home (default $MONITOR_HOME or ~/claude/monitor)')
    sub = ap.add_subparsers(dest='cmd', required=True)
    s = sub.add_parser('set', help='create or update a section (merges into the existing file)')
    s.add_argument('id')
    s.add_argument('--title')
    s.add_argument('--state', choices=STATES)
    s.add_argument('--note')
    s.add_argument('--owner', help='who runs it, e.g. "Claude session 777b33f5"')
    s.add_argument('--phase', action='append', type=parse_phase, default=[], help='NAME=DONE/TOTAL[:STATE[:NOTE]]')
    s.add_argument('--drop-phase', action='append', default=[], metavar='NAME')
    s.add_argument('--alert', action='append', default=[])
    s.add_argument('--clear-alerts', action='store_true')
    s.add_argument('--process', action='append', type=pair('process', 'label', 'match'), default=[],
                   help='LABEL=REGEX matched against process command lines')
    s.add_argument('--link', action='append', type=pair('link', 'label', 'url'), default=[], help='LABEL=URL')
    s.add_argument('--heartbeat', type=int, metavar='SECS')
    s.add_argument('--expires', type=int, metavar='SECS')
    r = sub.add_parser('remove', help='take a section off the page')
    r.add_argument('id')
    sub.add_parser('list', help='list sections')
    a = ap.parse_args(argv)
    if a.cmd == 'remove':
        remove(a.id, a.home)
        return
    if a.cmd == 'list':
        d = os.path.join(home_dir(a.home), 'sections')
        for f in sorted(os.listdir(d)) if os.path.isdir(d) else []:
            if f.endswith('.json'):
                try:
                    x = json.load(open(os.path.join(d, f)))
                    print('%-24s %-8s %s' % (f[:-5], x.get('state'), x.get('title')))
                except ValueError:
                    print('%-24s MALFORMED' % f[:-5])
        return
    try:
        sec = json.load(open(path_of(a.id, a.home)))
    except FileNotFoundError:
        if not a.title:
            ap.error('a new section needs --title')
        sec = {'heartbeat_secs': 300, 'expires_secs': 86400, 'note': '', 'owner': ''}
    for k in ('title', 'state', 'note', 'owner'):
        if getattr(a, k) is not None:
            sec[k] = getattr(a, k)
    sec.setdefault('state', 'running')
    if a.heartbeat:
        sec['heartbeat_secs'] = a.heartbeat
    if a.expires:
        sec['expires_secs'] = a.expires
    phases = [p for p in sec.get('phases', []) if p['name'] not in a.drop_phase]
    for p in a.phase:
        i = next((j for j, q in enumerate(phases) if q['name'] == p['name']), None)
        if i is None:
            phases.append(p)
        else:
            phases[i] = p
    sec['phases'] = phases
    sec['alerts'] = ([] if a.clear_alerts else sec.get('alerts', [])) + a.alert
    procs = {p['label']: p for p in sec.get('processes', [])}
    procs.update({p['label']: p for p in a.process})
    sec['processes'] = list(procs.values())
    links = {x['label']: x for x in sec.get('links', [])}
    links.update({x['label']: x for x in a.link})
    sec['links'] = list(links.values())
    sec['updated'] = int(time.time())
    try:
        print(write(a.id, sec, a.home))
    except ValueError as e:
        ap.error(str(e))


if __name__ == '__main__':
    main(sys.argv[1:])
