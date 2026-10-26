"""The monitor's headless-agent views (no tokens): the agents summary, carve-pipeline phases, the safe
file server behind the log viewer, and the subscription-quota sampler.

Everything is read from files under ~/claude/headless-agents/<name>/ (meta.json, state.json, usage.json,
last_text.txt, transcript.jsonl, brief.md; written by claude-private/tools/headless-agent) and from the
carve directories those agents work in (pipeline_state.json from carve_pipeline.py, run_state.json from
split_run)."""
import datetime
import glob
import json
import os
import re
import time

AGENTS_DIR = os.environ.get('AGENTS_DIR', os.path.expanduser('~/claude/headless-agents'))
JOBS_DIR = os.environ.get('JOBS_DIR', os.path.expanduser('~/.claude/jobs'))
PORTS_DIR = os.environ.get('PORTS_DIR', os.path.expanduser('~/claude/p2m-standalone/openai-ports'))
KEEP = 48 * 3600
QUOTA_KEEP = 7 * 86400
FINISHED_WINDOW = 24 * 3600
FILES = {'transcript.jsonl': 'text/plain', 'state.json': 'application/json', 'usage.json': 'application/json',
         'meta.json': 'application/json', 'brief.md': 'text/plain'}
MAX_BYTES = 512 * 1024
NAME = re.compile(r'^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$')

# the compact stages shown on the bar, and the carve_pipeline.py steps each one covers
STAGES = [('fetch', ['fetch', 'filter_patches']), ('port', ['port']), ('build', ['build', 'wsbuild', 'config']),
          ('graph', ['graph', 'extdefs']), ('plan', ['plan']), ('gen', ['gen', 'order']),
          ('measure', ['measure', 'calibrate']), ('prose', ['publish_prep', 'prose']),
          ('check', ['check_text', 'dryrun']), ('publish', ['publish'])]


# ---- safe file serving -----------------------------------------------------------------------

def safe_path(root, name, fname):
    """The real path of root/name/fname if name is a plain directory name, fname is on the allowlist
    and the resolved file stays inside root/name (no symlink out); else None."""
    if not NAME.match(name or '') or fname not in FILES:
        return None
    d = os.path.join(os.path.realpath(root), name)
    if os.path.islink(d) or not os.path.isdir(d):
        return None
    p = os.path.realpath(os.path.join(d, fname))
    if os.path.dirname(p) != d or not os.path.isfile(p):
        return None
    return p


def read_range(path, start, limit=MAX_BYTES):
    """(bytes, start, end, size) holding whole lines only. start < 0 counts from the end; a range that
    begins mid-line skips to the next line; the last, unfinished line is left for the next read
    (poll again from `end`). A single line longer than the cap is skipped."""
    size = os.path.getsize(path)
    start = max(0, size + start) if start < 0 else min(start, size)
    with open(path, 'rb') as f:
        mid = False
        if start > 0:
            f.seek(start - 1)
            mid = f.read(1) != b'\n'
        data = f.read(min(limit, size - start))
    capped = start + len(data) < size
    if mid:
        i = data.find(b'\n')
        if i < 0:
            return b'', start, (start + len(data) if capped else start), size
        data, start = data[i + 1:], start + i + 1
    j = data.rfind(b'\n')
    if j < 0:
        return b'', start, (start + len(data) if capped else start), size
    data = data[:j + 1]
    return data, start, start + len(data), size


# ---- the summary -----------------------------------------------------------------------------

def load(p, default=None):
    try:
        return json.load(open(p))
    except (OSError, ValueError):
        return default


def parse_time(s):
    for fmt in ('%Y-%m-%dT%H:%M:%S%z', '%Y-%m-%dT%H:%M:%S'):
        try:
            return datetime.datetime.strptime(s, fmt).timestamp()
        except (ValueError, TypeError):
            pass
    return None


def stage_status(stage_steps, steps):
    got = [steps[s]['status'] for s in stage_steps if s in steps]
    if not got:
        return 'pending'
    if 'failed' in got:
        return 'failed'
    if 'running' in got:
        return 'running'
    if len(got) == len(stage_steps) and all(g in ('done', 'skipped') for g in got):
        return 'done'
    return 'partial' if any(g in ('done', 'skipped') for g in got) else 'pending'


def pipeline_view(state):
    """{'stages': [{name, status}], 'current'} from one pipeline_state.json."""
    steps = state.get('steps', {}) if isinstance(state, dict) else {}
    stages = [{'name': n, 'status': stage_status(ss, steps)} for n, ss in STAGES]
    cur = next((s['name'] for s in stages if s['status'] in ('running', 'failed')), None) \
        or next((s['name'] for s in stages if s['status'] != 'done'), None)
    return {'stages': stages, 'current': cur}


def items_live(run_state):
    """(live, total) bundles and pieces in a split_run run_state.json; the statement: rows repeat pieces."""
    rows = [v for k, v in (run_state or {}).items() if k.startswith(('bundle:', 'piece:')) and isinstance(v, dict)]
    return sum(1 for v in rows if v.get('state') == 'live'), len(rows)


def carve_dirs(name, jobs=None, ports=None):
    """Directories with a pipeline_state.json that belong to agent `name`: the job dir (to depth 3)
    and the ports dir of the same name."""
    jobs, ports = jobs or JOBS_DIR, ports or PORTS_DIR
    found = []
    for base in (os.path.join(jobs, name), os.path.join(ports, name)):
        for depth in range(0, 4):
            found += [os.path.dirname(p) for p in glob.glob(os.path.join(base, *['*'] * depth, 'pipeline_state.json'))]
    return sorted(set(found))


def phases_for(name, jobs=None, ports=None):
    """None when the agent has no carve state yet, else {'dirs': [{name, stages, current, live, total}]}."""
    out = []
    for d in carve_dirs(name, jobs, ports):
        st = load(os.path.join(d, 'pipeline_state.json'))
        if not isinstance(st, dict):
            continue
        v = pipeline_view(st)
        live = total = None
        for rs in (d, os.path.join(d, 'publish'), os.path.join(d, 'work')):
            r = load(os.path.join(rs, 'run_state.json'))
            if isinstance(r, dict):
                live, total = items_live(r)
                break
        out.append(dict(v, name=os.path.basename(d), live=live, total=total,
                        mtime=int(os.path.getmtime(os.path.join(d, 'pipeline_state.json')))))
    return {'dirs': out} if out else None


def goals_for(name, registry):
    """[{name, id, url}] for a queue agent (batch `name`), from the queue's registry.json."""
    out = []
    for b in (registry or {}).get('batches', {}).values():
        if b.get('name') != name:
            continue
        for mod in b.get('modules', []):
            g = registry.get('groups', {}).get(mod, {})
            for goal in g.get('goals', []):
                tid = g.get('ids', {}).get(goal)
                out.append({'name': goal, 'id': tid, 'url': 'https://prove2.me/theorems/' + tid if tid else None})
    return out


def summarize(name, root, now, registry=None, cost_hist=None, jobs=None, ports=None):
    d = os.path.join(root, name)
    meta, st, us = (load(os.path.join(d, f), {}) for f in ('meta.json', 'state.json', 'usage.json'))
    try:
        last = open(os.path.join(d, 'last_text.txt'), errors='replace').read().strip().replace('\n', ' ')[:300]
    except OSError:
        last = ''
    try:
        tmtime = os.path.getmtime(os.path.join(d, 'transcript.jsonl'))
    except OSError:
        tmtime = None
    key = st.get('apiKeySource', 'none')
    started = parse_time(st.get('started') or meta.get('launched'))
    ended = parse_time(st.get('ended'))
    return {'name': name, 'model': st.get('model') or meta.get('model'), 'mode': st.get('mode') or meta.get('mode'),
            'auth': 'subscription' if key in (None, 'none') else 'key', 'state': st.get('state', 'unknown'),
            'note': st.get('note', ''), 'started': started, 'ended': ended,
            'cost': us.get('estimated_cost_usd'), 'cost_exact': us.get('cost_is_exact'),
            'budget': meta.get('budget_usd'), 'cost_series': (cost_hist or {}).get(name, []),
            'last_text': last, 'active': int(tmtime) if tmtime else None,
            'goals': goals_for(name, registry), 'phases': phases_for(name, jobs, ports)}


def agents_json(root, now, registry=None, cost_hist=None, jobs=None, ports=None):
    """Running first, then agents that finished in the last 24 h (newest first)."""
    rows = []
    for n in sorted(os.listdir(root)) if os.path.isdir(root) else []:
        if not NAME.match(n) or not os.path.isfile(os.path.join(root, n, 'state.json')):
            continue
        rows.append(summarize(n, root, now, registry, cost_hist, jobs, ports))
    running = [r for r in rows if r['state'] == 'running']
    recent = [r for r in rows if r['state'] != 'running'
              and now - (r['ended'] or r['active'] or r['started'] or 0) <= FINISHED_WINDOW]
    key = lambda r: -(r['ended'] or r['active'] or r['started'] or 0)
    return {'updated': int(now), 'running': sorted(running, key=lambda r: -(r['started'] or 0)),
            'recent': sorted(recent, key=key), 'hidden': len(rows) - len(running) - len(recent)}


def record_costs(hist, root, now):
    """hist[name] = [[t, cost]] (a point when the cost changes), 48 h; drops agents that left."""
    names = set()
    for n in sorted(os.listdir(root)) if os.path.isdir(root) else []:
        us = load(os.path.join(root, n, 'usage.json'))
        if not isinstance(us, dict) or us.get('estimated_cost_usd') is None:
            continue
        names.add(n)
        h = hist.setdefault(n, [])
        if not h or h[-1][1] != us['estimated_cost_usd']:
            h.append([int(now), us['estimated_cost_usd']])
        h[:] = [x for x in h if x[0] >= now - KEEP] or h[-1:]    # an idle agent keeps its last cost
    for n in list(hist):
        if n not in names or not hist[n]:
            del hist[n]


# ---- subscription quota ----------------------------------------------------------------------

FIRST_READ = 256 * 1024


def quota_event(text):
    """The last rate_limit_event's unified windows in text (complete JSON lines):
    {'five_hour': (util %, resetsAt), 'seven_day': (...)} or None. Utilization is a 0..1 fraction."""
    found = None
    for line in text.splitlines():
        if '"rate_limit_event"' not in line:
            continue
        try:
            w = json.loads(line)['rate_limit_info']['unifiedWindows']
            cur = {k: (round(float(w[k]['utilization']) * 100, 2), int(w[k]['resetsAt'])) for k in ('five_hour', 'seven_day')}
        except (ValueError, KeyError, TypeError):
            continue
        found = cur
    return found


def update_quota(q, root, now):
    """q = {'offsets': {path: pos}, 'series': [[t, five %, five reset, seven %, seven reset]]}.
    Reads only the new bytes of each transcript that grew; the event from the most recently written
    file wins. Appends a sample when the windows changed or 10 minutes passed. Returns q."""
    offs = q.setdefault('offsets', {})
    best = None
    for p in glob.glob(os.path.join(root, '*', 'transcript.jsonl')):
        try:
            size, mtime = os.path.getsize(p), os.path.getmtime(p)
        except OSError:
            continue
        pos = offs.get(p)
        if pos is not None and size <= pos:
            offs[p] = min(pos, size)
            continue
        start = pos if pos is not None else max(0, size - FIRST_READ)
        try:
            with open(p, 'rb') as f:
                f.seek(start)
                data = f.read(size - start)
        except OSError:
            continue
        j = data.rfind(b'\n')
        offs[p] = start + j + 1 if j >= 0 else start
        ev = quota_event(data[:j + 1].decode(errors='replace')) if j >= 0 else None
        if ev and (best is None or mtime > best[0]):
            best = (mtime, ev)
    for p in list(offs):
        if not os.path.exists(p):
            del offs[p]
    series = q.setdefault('series', [])
    if best:
        ev = best[1]
        row = [int(now), ev['five_hour'][0], ev['five_hour'][1], ev['seven_day'][0], ev['seven_day'][1]]
        if not series or series[-1][1:] != row[1:] or now - series[-1][0] >= 600:
            series.append(row)
    series[:] = [r for r in series if r[0] >= now - QUOTA_KEEP]
    return q
