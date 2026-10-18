#!/usr/bin/env python3
"""The careyaibox monitoring page (the `monitor` skill): one process that samples the machine every
30 s, reads the section files projects write (see section.py), and serves the page on port 8765.

State lives in MONITOR_HOME (default ~/claude/monitor): sections/*.json (written by producers),
state/resources.json and state/history.json (48 h of samples), state/status.json (what the page
shows; handy for reading from a shell). No Claude involvement: it runs as the systemd user unit
monitor.service."""
import datetime
import json
import os
import re
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import section as S

HERE = os.path.dirname(os.path.abspath(__file__))
PORT = int(os.environ.get('MONITOR_PORT', '8765'))
INTERVAL = 30
KEEP = 48 * 3600
CLK = os.sysconf('SC_CLK_TCK')
G = 2 ** 30
HEALTH_FLAGS = os.path.expanduser('~/.local/state/lean-health.flags')


# ---- the machine ---------------------------------------------------------------------------

def parse_psi(texts):
    """{'cpu': text, 'memory': text, 'io': text} from /proc/pressure -> avg10 percentages
    [cpu some, memory some, memory full, io some, io full], or None."""
    out = []
    try:
        for r, kinds in (('cpu', ('some',)), ('memory', ('some', 'full')), ('io', ('some', 'full'))):
            lines = {l.split()[0]: l for l in texts[r].splitlines() if l.strip()}
            for k in kinds:
                out.append(float(lines[k].split()[1].split('=')[1]))
    except (KeyError, IndexError, ValueError):
        return None
    return out


def read_psi():
    try:
        return parse_psi({r: open('/proc/pressure/' + r).read() for r in ('cpu', 'memory', 'io')})
    except OSError:
        return None


def pressure_alerts(psi, free_gib):
    """The conditions under which the machine feels frozen. Full = every non-idle task waited."""
    a = []
    if psi:
        if psi[2] > 5:
            a.append('memory stalls %.0f%% (full)' % psi[2])
        if psi[4] > 20:
            a.append('I/O stalls %.0f%% (full)' % psi[4])
        if psi[0] > 50:
            a.append('CPU stalls %.0f%%' % psi[0])
    if free_gib is not None and free_gib < 4:
        a.append('only %.1f GiB memory free' % free_gib)
    return a


def classify(args, groups):
    """'lean' for Lean and lake; else the id of the first section with a matching pattern; else None.
    groups: [(section id, [regex, ...])]."""
    a0 = args.split()[0] if args.split() else ''
    if re.match(r'(\S*/)?(lean|lake)$', a0):
        return 'lean'
    for sid, pats in groups:
        if any(re.search(p, args) for p in pats):
            return sid
    return None


def proc_table(groups):
    """Every process that belongs to a group, with its own memory (Pss_Anon: shared pages split, file
    cache excluded), memory-mapped files (Pss_File), CPU ticks, age and working directory."""
    boot = time.time() - float(open('/proc/uptime').read().split()[0])
    out = []
    for d in os.listdir('/proc'):
        if not d.isdigit():
            continue
        try:
            args = open('/proc/%s/cmdline' % d, 'rb').read().replace(b'\0', b' ').decode(errors='replace').strip()
            g = classify(args, groups)
            if not g:
                continue
            p = {'pid': d, 'args': args, 'group': g, 'anon': 0, 'file': 0}
            for l in open('/proc/%s/smaps_rollup' % d):
                if l.startswith('Pss_Anon:'):
                    p['anon'] = int(l.split()[1]) * 1024
                elif l.startswith('Pss_File:'):
                    p['file'] = int(l.split()[1]) * 1024
            st = open('/proc/%s/stat' % d).read().rsplit(')', 1)[1].split()
            p['ticks'] = int(st[11]) + int(st[12])
            p['age'] = time.time() - (boot + int(st[19]) / CLK)
            try:
                p['cwd'] = os.readlink('/proc/%s/cwd' % d)
            except OSError:
                p['cwd'] = ''
            out.append(p)
        except (OSError, ValueError, IndexError):
            continue
    return out


def read_meminfo():
    mi = {}
    for l in open('/proc/meminfo'):
        k, v = l.split(':')
        mi[k] = int(v.split()[0]) * 1024
    return mi


def read_stat():
    cpu = [int(x) for x in open('/proc/stat').readline().split()[1:]]
    return [sum(cpu[:8]), cpu[3] + cpu[4]]


def machine_row(now, procs, meminfo, stat, prev, ncpu=None, clk=CLK):
    """{'t', 'total', 'mem': {group: GiB, 'rest': GiB}, 'cpu': {group: cores, 'rest': cores} or None}.
    Memory in use = MemTotal - MemAvailable; the rest is what no group accounts for."""
    ncpu = ncpu or os.cpu_count()
    used = meminfo['MemTotal'] - meminfo['MemAvailable']
    procs = [p for p in procs if p['group']]
    mem = {'lean': 0}
    for p in procs:
        mem[p['group']] = mem.get(p['group'], 0) + p['anon']
    row = {'t': now, 'total': round(meminfo['MemTotal'] / G, 1),
           'mem': dict({g: round(v / G, 2) for g, v in mem.items()}, rest=round(max(0, used - sum(mem.values())) / G, 2)),
           'cpu': None}
    if prev and now > prev['t']:
        dt = now - prev['t']
        cpu = {g: 0.0 for g in mem}
        for p in procs:
            cpu[p['group']] += max(0, p['ticks'] - prev['ticks'].get(p['pid'], p['ticks'])) / clk / dt
        dtot, didle = stat[0] - prev['stat'][0], stat[1] - prev['stat'][1]
        busy = (dtot - didle) / dtot * ncpu if dtot > 0 else 0.0
        row['cpu'] = dict({g: round(v, 2) for g, v in cpu.items()}, rest=round(max(0.0, busy - sum(cpu.values())), 2))
    return row, {'t': now, 'ticks': {p['pid']: p['ticks'] for p in procs}, 'stat': stat}


def cores_of(p, prev, now):
    if not prev or now <= prev['t'] or p['pid'] not in prev['ticks']:
        return None
    return round(max(0, p['ticks'] - prev['ticks'][p['pid']]) / CLK / (now - prev['t']), 2)


def short_path(p):
    h = os.path.expanduser('~')
    return '~' + p[len(h):] if p.startswith(h) else p


def proc_view(p, prev, now, label):
    return {'what': label, 'pid': int(p['pid']), 'age_min': round(p.get('age', 0) / 60, 1),
            'cores': cores_of(p, prev, now), 'own_gib': round(p['anon'] / G, 2),
            'shared_gib': round(p['file'] / G, 2), 'cwd': short_path(p.get('cwd', ''))}


def lean_view(procs, prev, now):
    out = []
    for p in procs:
        if p['group'] != 'lean':
            continue
        a = p['args'].split()
        what = os.path.basename(a[0]) + (' ' + ' '.join(os.path.basename(x) for x in a[1:3]) if len(a) > 1 else '')
        out.append(proc_view(p, prev, now, what[:80]))
    return sorted(out, key=lambda r: -r['own_gib'])


def health_flags(path, now, window=86400):
    """Lean health flags (lean-health.timer) from the last day, as 'date FLAG: ...' lines."""
    try:
        text = open(path, errors='replace').read()
    except OSError:
        return []
    out, stamp, recent = [], '', False
    for l in text.splitlines():
        m = re.match(r'^=== (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d)', l)
        if m:
            stamp = m.group(1)
            try:
                recent = now - datetime.datetime.strptime(stamp, '%Y-%m-%d %H:%M:%S').timestamp() <= window
            except ValueError:
                recent = False
        elif recent and l.startswith('FLAG:'):
            out.append(stamp + ' ' + l)
    return out


# ---- the sections ----------------------------------------------------------------------------

def load_sections(d, now):
    """(sections, problems): every valid section file, newest state, marked stale when a running or
    waiting one missed three heartbeats; done/failed ones past expires_secs are left off."""
    secs, problems = [], []
    for f in sorted(os.listdir(d)) if os.path.isdir(d) else []:
        if not f.endswith('.json'):
            continue
        sid = f[:-5]
        try:
            sec = json.load(open(os.path.join(d, f)))
            assert isinstance(sec, dict)
        except (OSError, ValueError, AssertionError) as e:
            problems.append('section file %s: unreadable (%s)' % (f, str(e)[:80]))
            continue
        bad = validate_id(sid) + S.validate(sec)
        if bad:
            problems.append('section file %s: %s' % (f, '; '.join(bad)))
            continue
        age = now - sec['updated']
        if sec['state'] in ('done', 'failed') and age > sec.get('expires_secs', 86400):
            continue
        sec = dict(sec, id=sid, age_secs=int(age),
                   stale=sec['state'] in ('running', 'waiting') and age > 3 * sec.get('heartbeat_secs', 300))
        secs.append(sec)
    rank = lambda s: (0 if s.get('alerts') or s['state'] == 'failed' else 1 if s['state'] != 'done' else 2, s['title'].lower())
    return sorted(secs, key=rank), problems


def validate_id(sid):
    return [] if S.ID.match(sid) else ['file name: lowercase letters, digits and dashes']


def track(hist, sections, now):
    """Keeps each phase's [t, done] history (a point when it changes, or every 10 min) and adds
    rate_per_min and eta (unix time) to running phases, from the last 30 minutes."""
    live = {s['id']: {p['name'] for p in s.get('phases', [])} for s in sections}
    for sid in list(hist):
        if sid not in live:
            del hist[sid]
            continue
        for name in list(hist[sid]):
            if name not in live[sid]:
                del hist[sid][name]
    for s in sections:
        for p in s.get('phases', []):
            h = hist.setdefault(s['id'], {}).setdefault(p['name'], [])
            if not h or h[-1][1] != p['done'] or now - h[-1][0] >= 600:
                h.append([now, p['done']])
            h[:] = [x for x in h if x[0] >= now - KEEP]
            if p.get('state', 'running') != 'running':
                continue
            w = [x for x in h if x[0] >= now - 1800]
            if len(w) < 2:
                w = h[-2:]
            if len(w) >= 2 and w[-1][0] > w[0][0] and w[-1][1] > w[0][1]:
                rate = (w[-1][1] - w[0][1]) / (w[-1][0] - w[0][0])
                p['rate_per_min'] = round(rate * 60, 2)
                if p['total'] > p['done']:
                    p['eta'] = int(now + (p['total'] - p['done']) / rate)


def build_status(now, sections, problems, system, flags, lean):
    psi = system['psi'][-1][1:] if system.get('psi') else None
    alerts = pressure_alerts(psi, system.get('free_gib'))
    alerts += ['Lean health: ' + f for f in flags]
    for s in sections:
        alerts += ['%s: %s' % (s['title'], a) for a in s.get('alerts', [])]
    alerts += problems
    for s in sections:
        if s['stale']:
            alerts.append('%s: no update for %d min (has its producer stopped?)' % (s['title'], s['age_secs'] // 60))
    return {'updated': now, 'host': socket.gethostname(), 'alerts': alerts,
            'system': dict(system, lean=lean, health_flags=flags), 'sections': sections}


# ---- the loop and the server -----------------------------------------------------------------

def load_json(p, default):
    try:
        return json.load(open(p))
    except (OSError, ValueError):
        return default


def save_json(p, x):
    with open(p + '.tmp', 'w') as o:
        json.dump(x, o, ensure_ascii=False)
    os.replace(p + '.tmp', p)


class State:
    status = b'{}'


def step(home, now=None):
    now = int(now or time.time())
    sd, st = os.path.join(home, 'sections'), os.path.join(home, 'state')
    os.makedirs(sd, exist_ok=True)
    os.makedirs(st, exist_ok=True)
    res = load_json(os.path.join(st, 'resources.json'), {})
    hist = load_json(os.path.join(st, 'history.json'), {})
    secs, problems = load_sections(sd, now)
    groups = [(s['id'], [p['match'] for p in s.get('processes', [])]) for s in secs if s.get('processes')]
    procs = proc_table(groups)
    mi = read_meminfo()
    prev = res.get('prev')
    row, res['prev'] = machine_row(now, procs, mi, read_stat(), prev)
    row['load1'] = float(open('/proc/loadavg').read().split()[0])
    res['machine'] = [r for r in res.get('machine', []) if r['t'] >= now - KEEP] + [row]
    psi = read_psi()
    if psi:
        res['psi'] = [r for r in res.get('psi', []) if r[0] >= now - KEEP] + [[now] + psi]
    labels = res.get('labels', {})
    labels.update({s['id']: s['title'] for s in secs})
    seen = {g for r in res['machine'] for g in r['mem']}
    res['labels'] = {g: l for g, l in labels.items() if g in seen}
    track(hist, secs, now)
    for s in secs:
        s['history'] = hist.get(s['id'], {})
        pats = [(p['label'], p['match']) for p in s.get('processes', [])]
        s['running'] = [proc_view(p, prev, now, next((l for l, m in pats if re.search(m, p['args'])), '?'))
                        for p in procs if p['group'] == s['id']]
    system = {'machine': res['machine'], 'psi': res.get('psi', []), 'labels': res['labels'],
              'free_gib': round(mi['MemAvailable'] / G, 1), 'cores_total': os.cpu_count()}
    status = build_status(now, secs, problems, system, health_flags(HEALTH_FLAGS, now), lean_view(procs, prev, now))
    save_json(os.path.join(st, 'resources.json'), res)
    save_json(os.path.join(st, 'history.json'), hist)
    save_json(os.path.join(st, 'status.json'), status)
    State.status = json.dumps(status, ensure_ascii=False).encode()


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        path = self.path.split('?', 1)[0]
        if path in ('/', '/index.html'):
            body, ctype = open(os.path.join(HERE, 'www', 'index.html'), 'rb').read(), 'text/html; charset=utf-8'
        elif path == '/status.json':
            body, ctype = State.status, 'application/json'
        else:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header('Content-Type', ctype)
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *a):
        pass


def main():
    home = S.home_dir()
    st = load_json(os.path.join(home, 'state', 'status.json'), None)
    if st:
        State.status = json.dumps(st, ensure_ascii=False).encode()
    srv = ThreadingHTTPServer(('', PORT), Handler)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    while True:
        try:
            step(home)
        except Exception as e:                 # one bad sample must not take the page down
            print('sample failed: %r' % e, flush=True)
        time.sleep(INTERVAL)


if __name__ == '__main__':
    main()
