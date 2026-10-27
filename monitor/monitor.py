#!/usr/bin/env python3
"""The machine monitoring page (the `monitor` skill): one process that samples the machine every
30 s, reads the section files projects write (see section.py), and serves the page on port 8765.

State lives in MONITOR_HOME (default ~/claude/monitor): sections/*.json (written by producers),
state/resources.json and state/history.json (48 h of samples), state/status.json (what the page
shows; handy for reading from a shell). No Claude involvement: it runs as the systemd user unit
monitor.service."""
import datetime
import glob
import json
import os
import re
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import agents as AG
import section as S

HERE = os.path.dirname(os.path.abspath(__file__))
PORT = int(os.environ.get('MONITOR_PORT', '8765'))
INTERVAL = 30
KEEP = 48 * 3600
CLK = os.sysconf('SC_CLK_TCK')
G = 2 ** 30
STATIC = {'.js': 'text/javascript', '.css': 'text/css', '.html': 'text/html; charset=utf-8', '.svg': 'image/svg+xml',
          '.png': 'image/png', '.ico': 'image/x-icon'}    # served from www/ (uPlot 1.6.30, MIT, is in www/vendor)
SEGMENT = re.compile(r'^[A-Za-z0-9][A-Za-z0-9._-]*$')
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
        a.append('only %.1f GiB of memory and swap free' % free_gib)
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


# The charts' categories (dbenbenn 2026-10-27: one group per section gave ~100 "Headless agent"
# entries): where a process lives, not which section claims it. The rest is the remainder.
CATS = ('lean', 'queue', 'claude')
CAT_LABELS = {'lean': 'Lean', 'queue': 'Queue workers', 'claude': 'Claude sessions', 'rest': 'Rest of the machine'}
QUEUE_UNIT = re.compile(r'/(headless-[^/\s]*|oai-queue|carve-[^/\s]*)\.service\s*$', re.M)


def _argv0(args):
    a = args.split()
    return a[0] if a else ''


def category(args, cgroup, ancestors):
    """'lean' (Lean, lake, anything in lean.slice), 'queue' (in the queue supervisor's, a headless
    agent's or a detached carve driver's unit), 'claude' (under an interactive `claude`), or None.
    ancestors: the command lines of the process's parents, nearest first."""
    if re.match(r'(\S*/)?(lean|lake|lake\.orig)$', _argv0(args)) or '/lean.slice/' in cgroup:
        return 'lean'
    if QUEUE_UNIT.search(cgroup):
        return 'queue'
    # the CLI is `claude`, or the versioned binary it runs (~/.local/share/claude/versions/2.1.310)
    if any(re.match(r'(\S*/)?claude$|\S*/claude/versions/[\w.-]+$', _argv0(x)) for x in [args] + list(ancestors)):
        return 'claude'
    return None


def fold_row(row):
    """A history row from before the categories, its per-section groups folded into them."""
    for k in ('mem', 'cpu'):
        d = row.get(k)
        if d is None:
            continue
        out = {c: 0.0 for c in CATS}
        for g, v in d.items():
            if g in CATS or g == 'rest':
                out[g] = out.get(g, 0.0) + v
            else:
                c = 'queue' if g.startswith(('headless-', 'oaiq', 'oai-queue', 'carve')) else 'claude'
                out[c] += v
        row[k] = {g: round(v, 2) for g, v in out.items()}
    return row


def inboxes(path, now):
    """[{label, dir, count, items, oldest_s}] for each directory listed in PATH (a JSON list of
    {label, dir, ignore}): what is waiting for someone, so the page can say so."""
    try:
        conf = json.load(open(path))
    except (OSError, ValueError):
        return []
    out = []
    for c in conf:
        d = os.path.expanduser(c['dir'])
        e = {'label': c.get('label', d), 'dir': d, 'count': 0, 'items': [], 'oldest_s': None}
        if not os.path.isdir(d):
            e['missing'] = True
            out.append(e)
            continue
        names = sorted(f for f in os.listdir(d) if not f.startswith('.') and f not in c.get('ignore', ())
                       and os.path.isfile(os.path.join(d, f)))
        if names:
            e.update(count=len(names), items=names[:10],
                     oldest_s=int(now - min(os.path.getmtime(os.path.join(d, f)) for f in names)))
        out.append(e)
    return out


def proc_table(groups):
    """Every process in a chart category or a section, with its own memory (Pss_Anon: shared pages
    split, file cache excluded), memory-mapped files (Pss_File), CPU ticks, age and working directory."""
    boot = time.time() - float(open('/proc/uptime').read().split()[0])
    info = {}
    for d in os.listdir('/proc'):
        if not d.isdigit():
            continue
        try:
            args = open('/proc/%s/cmdline' % d, 'rb').read().replace(b'\0', b' ').decode(errors='replace').strip()
            ppid = open('/proc/%s/stat' % d).read().rsplit(')', 1)[1].split()[1]
            cg = open('/proc/%s/cgroup' % d).read()
        except (OSError, ValueError, IndexError):
            continue
        info[d] = (args, ppid, cg)

    def ancestors(d):
        out, seen = [], set()
        while d in info and d not in seen and len(out) < 64:
            seen.add(d)
            d = info[d][1]
            if d in info:
                out.append(info[d][0])
        return out
    out = []
    for d, (args, _, cg) in info.items():
        try:
            g = classify(args, groups)
            cat = category(args, cg, ancestors(d))
            if not g and not cat:
                continue
            p = {'pid': d, 'args': args, 'group': g, 'cat': cat, 'anon': 0, 'file': 0}
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


USER_CG = '/sys/fs/cgroup/user.slice/user-%d.slice/user@%d.service' % (os.getuid(), os.getuid())


def cgroup_usage(base=USER_CG):
    """{'lean': {cgroup: usage_usec}, 'queue': {...}}: CPU time of the Lean slots' slice and of the queue's
    units, exited processes included (per-process ticks miss every Lean compile that lives only
    seconds: lean.slice used 3.66 cores while they showed 1.01, 2026-10-27)."""
    out = {'lean': {}, 'queue': {}}
    paths = [('lean', os.path.join(base, 'lean.slice'))] + \
        [('queue', p) for p in glob.glob(os.path.join(base, 'app.slice', '*.service'))
         if QUEUE_UNIT.search('/' + os.path.basename(p))]
    for cat, p in paths:
        try:
            for l in open(os.path.join(p, 'cpu.stat')):
                if l.startswith('usage_usec'):
                    out[cat][p] = int(l.split()[1])
        except (OSError, ValueError, IndexError):
            continue
    return out


def machine_row(now, procs, meminfo, stat, prev, ncpu=None, clk=CLK, cg=None):
    """{'t', 'total', 'mem': {category: GiB, 'rest': GiB}, 'cpu': {category: cores, 'rest': cores} or None}.
    Memory in use = MemTotal - MemAvailable; the rest is what no category accounts for. CPU of a
    category with cgroup usage (`cg`, from cgroup_usage) comes from it: a unit seen for the first time
    counts from 0, one gone since the last sample drops out; the others' from their processes' ticks."""
    ncpu = ncpu or os.cpu_count()
    used = meminfo['MemTotal'] - meminfo['MemAvailable']
    procs = [p for p in procs if p.get('cat')]
    mem = {c: 0 for c in CATS}
    for p in procs:
        mem[p['cat']] += p['anon']
    row = {'t': now, 'total': round(meminfo['MemTotal'] / G, 1),
           'mem': dict({g: round(v / G, 2) for g, v in mem.items()}, rest=round(max(0, used - sum(mem.values())) / G, 2)),
           'cpu': None}
    if prev and now > prev['t']:
        dt = now - prev['t']
        cpu = {g: 0.0 for g in mem}
        for p in procs:
            cpu[p['cat']] += max(0, p['ticks'] - prev['ticks'].get(p['pid'], p['ticks'])) / clk / dt
        if cg and prev.get('cg'):
            for cat, units in cg.items():
                old = prev['cg'].get(cat, {})
                cpu[cat] = sum(max(0, v - old.get(u, 0)) for u, v in units.items()) / 1e6 / dt
        dtot, didle = stat[0] - prev['stat'][0], stat[1] - prev['stat'][1]
        busy = (dtot - didle) / dtot * ncpu if dtot > 0 else 0.0
        row['cpu'] = dict({g: round(v, 2) for g, v in cpu.items()}, rest=round(max(0.0, busy - sum(cpu.values())), 2))
    return row, {'t': now, 'ticks': {p['pid']: p['ticks'] for p in procs}, 'stat': stat, 'cg': cg}


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
        if p.get('cat') != 'lean':
            continue
        a = p['args'].split()
        what = os.path.basename(a[0]) + (' ' + ' '.join(os.path.basename(x) for x in a[1:3]) if len(a) > 1 else '')
        out.append(proc_view(p, prev, now, what[:80]))
    return sorted(out, key=lambda r: -r['own_gib'])


HEALTH_EVERY = 600         # lean-health.timer's interval
NUM = re.compile(r'(?<!pid )\b\d+(?:\.\d+)?\b')     # a flag's measurements; pids name it
RACE = re.compile(r"race: '([^']*)' started by pid (\d+) .* while pid (\d+) is already on it")


def severity(text):
    """Orders reports of one flag, worst last: by their numbers; for 'only N GiB free', fewer is worse."""
    nums = tuple(float(x) for x in NUM.findall(text))
    return tuple(-x for x in nums) if text.startswith('only ') else nums


def add_report(eps, t, text, gap):
    """Counts a report of `text` at time t into the episode of the same flag (its numbers aside)
    last seen at most `gap` s before, or opens a new one. An episode keeps the latest text and the worst."""
    key = NUM.sub('#', text)
    e = next((e for e in reversed(eps) if e['key'] == key and t - e['last'] <= gap), None)
    if e is None:
        eps.append({'key': key, 'text': text, 'worst': text, 'first': t, 'last': t, 'n': 1})
        return
    e.update(text=text, last=t, n=e['n'] + 1)
    if severity(text) > severity(e['worst']):
        e['worst'] = text


def pid_running(pid, needle):
    """pid is alive and still the job it was (its command line mentions needle)."""
    try:
        return needle in open('/proc/%s/cmdline' % pid, 'rb').read().decode(errors='replace')
    except OSError:
        return False


def health_flags(path, now, alive=pid_running, home=os.path.expanduser('~'), window=86400):
    """Lean health flags (lean-health.timer, and lean-cap's race reports) from the last day, as episodes
    {text, worst, first, last, n, active}. Active: a race while both jobs still run; an OOM kill for
    an hour; any other flag while the latest check (every 10 min) still reports it."""
    try:
        text = open(path, errors='replace').read()
    except OSError:
        return []
    eps, t = [], None
    for l in text.splitlines():
        m = re.match(r'^=== (\d{4}-\d\d-\d\d \d\d:\d\d:\d\d)', l)
        if m:
            try:
                t = datetime.datetime.strptime(m.group(1), '%Y-%m-%d %H:%M:%S').timestamp()
            except ValueError:
                t = None
        elif t is not None and now - t <= window and l.startswith('FLAG:'):
            add_report(eps, t, l[len('FLAG:'):].strip().replace(home + '/', '~/'), gap=2.5 * HEALTH_EVERY)
    for e in eps:
        race = RACE.search(e['text'])
        if race:
            target = race.group(1)
            needle = re.split(r'[|/.]', target[:-5] if target.endswith('.lean') else target)[-1]
            e['active'] = alive(race.group(2), needle) and alive(race.group(3), needle)
        elif 'OOM' in e['text']:
            e['active'] = now - e['last'] <= 3600
        else:
            e['active'] = now - e['last'] <= 1.5 * HEALTH_EVERY
    return eps


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


def build_status(now, sections, problems, system, flags, lean, trouble=None):
    """alerts: machine trouble going on now (the page's top banner and its red icon). Trouble from the
    last day that has stopped is listed as cleared: Lean health episodes that are no longer active
    (flags, from health_flags) and stall/low-memory episodes, which `trouble` keeps across samples
    (updated in place). A section's own alerts and staleness show in that section; unreadable section
    files are listed apart as problems."""
    trouble = [] if trouble is None else trouble
    psi = system['psi'][-1][1:] if system.get('psi') else None
    free = system.get('free_gib')
    if free is not None:
        free += system.get('swap_free_gib', 0)   # with swap, low free RAM alone is normal under load
    now_alerts = pressure_alerts(psi, free)
    for a in now_alerts:
        add_report(trouble, now, a, gap=600)
    trouble[:] = [e for e in trouble if now - e['last'] <= 86400]
    since = lambda t: time.strftime('%H:%M', time.localtime(t))
    alerts = now_alerts + ['Lean health: %s (since %s)' % (e['text'], since(e['first'])) for e in flags if e['active']]
    cleared = [dict(what='machine', **e) for e in trouble if e['last'] < now] + \
              [dict(what='Lean health', **e) for e in flags if not e['active']]
    cleared = [{k: e[k] for k in ('what', 'first', 'last', 'n')} | {'text': e['worst']}
               for e in sorted(cleared, key=lambda e: -e['last'])]
    return {'updated': now, 'host': socket.gethostname(), 'alerts': alerts, 'cleared': cleared, 'problems': problems,
            'system': dict(system, lean=lean), 'sections': sections}


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
    costs = {}                      # agent -> [[t, cost]], from the sampler
    agents = (0, b'{}')             # (time, body) cache of /agents.json


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
    row, res['prev'] = machine_row(now, procs, mi, read_stat(), prev, cg=cgroup_usage())
    row['load1'] = float(open('/proc/loadavg').read().split()[0])
    res['machine'] = [fold_row(r) for r in res.get('machine', []) if r['t'] >= now - KEEP] + [row]
    psi = read_psi()
    if psi:
        res['psi'] = [r for r in res.get('psi', []) if r[0] >= now - KEEP] + [[now] + psi]
    res['labels'] = dict(CAT_LABELS)
    track(hist, secs, now)
    costs = load_json(os.path.join(st, 'agent_costs.json'), {})
    AG.record_costs(costs, AG.AGENTS_DIR, now)
    quota = AG.update_quota(load_json(os.path.join(st, 'quota.json'), {}), AG.AGENTS_DIR, now)
    State.costs = costs
    for s in secs:
        s['history'] = hist.get(s['id'], {})
        pats = [(p['label'], p['match']) for p in s.get('processes', [])]
        s['running'] = [proc_view(p, prev, now, next((l for l, m in pats if re.search(m, p['args'])), '?'))
                        for p in procs if p['group'] == s['id']]
    system = {'machine': res['machine'], 'psi': res.get('psi', []), 'labels': res['labels'],
              'free_gib': round(mi['MemAvailable'] / G, 1), 'cores_total': os.cpu_count(),
              'swap_free_gib': round(mi.get('SwapFree', 0) / G, 1), 'swap_total_gib': round(mi.get('SwapTotal', 0) / G, 1)}
    res['trouble'] = res.get('trouble', [])
    status = build_status(now, secs, problems, system, health_flags(HEALTH_FLAGS, now), lean_view(procs, prev, now),
                          trouble=res['trouble'])
    status['inboxes'] = inboxes(os.path.join(home, 'inboxes.json'), now)
    status['quota'] = {'series': quota['series'], 'columns': ['t', 'five_hour %', 'five_hour resets', 'seven_day %', 'seven_day resets']}
    save_json(os.path.join(st, 'resources.json'), res)
    save_json(os.path.join(st, 'history.json'), hist)
    save_json(os.path.join(st, 'agent_costs.json'), costs)
    save_json(os.path.join(st, 'quota.json'), quota)
    save_json(os.path.join(st, 'status.json'), status)
    State.status = json.dumps(status, ensure_ascii=False).encode()


def www_file(path):
    """(bytes, content type) for a request path under www/ (an allowlisted extension, plain path
    segments, nothing resolving outside www/), or None. /page/<name>.html is www/<name>.html."""
    if path.startswith('/page/'):
        path = '/' + path[len('/page/'):]
    segs = path.strip('/').split('/') if path != '/' else ['index.html']
    ext = os.path.splitext(segs[-1])[1]
    if ext not in STATIC or not all(SEGMENT.match(x) for x in segs):
        return None
    www = os.path.realpath(os.path.join(HERE, 'www'))
    p = os.path.realpath(os.path.join(www, *segs))
    if not p.startswith(www + os.sep) or not os.path.isfile(p):
        return None
    return open(p, 'rb').read(), STATIC[ext]


def agent_file(path, query):
    """(status, body, content type, extra headers) for /agent/<name>/<file>[?from=N&max=M]."""
    parts = path.strip('/').split('/')
    p = AG.safe_path(AG.AGENTS_DIR, parts[1], parts[2]) if len(parts) == 3 else None
    if not p:
        return 404, b'not found', 'text/plain', {}
    q = dict(x.split('=', 1) for x in query.split('&') if '=' in x)
    try:
        start, limit = int(q.get('from', '0')), min(int(q.get('max', AG.MAX_BYTES)), AG.MAX_BYTES)
    except ValueError:
        return 400, b'bad range', 'text/plain', {}
    if parts[2] == 'transcript.jsonl':
        body, s, e, size = AG.read_range(p, start, limit)
        return 200, body, 'text/plain; charset=utf-8', {'X-Start': s, 'X-End': e, 'X-Size': size}
    size = os.path.getsize(p)
    with open(p, 'rb') as f:
        body = f.read(min(limit, AG.MAX_BYTES))
    return 200, body, AG.FILES[parts[2]] + '; charset=utf-8', {'X-Start': 0, 'X-End': len(body), 'X-Size': size}


def agents_body(now=None):
    now = now or time.time()
    if now - State.agents[0] > 5:
        reg = load_json(os.path.join(AG.AGENTS_DIR, 'queue', 'registry.json'), None)
        State.agents = (now, json.dumps(AG.agents_json(AG.AGENTS_DIR, now, reg, State.costs), ensure_ascii=False).encode())
    return State.agents[1]


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        path, _, query = self.path.partition('?')
        extra = {}
        try:
            code, ctype = 200, 'application/json'
            if path == '/status.json':
                body = State.status
            elif path == '/agents.json':
                body = agents_body()
            elif path.startswith('/agent/'):
                code, body, ctype, extra = agent_file(path, query)
            else:
                f = www_file(path)
                if not f:
                    self.send_error(404)
                    return
                body, ctype = f
        except Exception as e:                 # a bad request must not kill the thread's connection silently
            code, body, ctype = 500, repr(e).encode(), 'text/plain'
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(body)))
        for k, v in extra.items():
            self.send_header(k, str(v))
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
