"""A carve's section on the machine monitoring page (the `monitor` skill, http://<host>:8765/).

carve_pipeline.py publishes one section per carve, id `carve-<hash>` (the hash of its systemd unit
carve-<hash>), titled with the queue worker (when the carve lies under ~/.claude/jobs/<worker>/ or
openai-ports/<worker>/), the carve directory and its root module. Its phases, each with done/total:
the steps (done of this mode's steps), the module build (DIR/build.log, `[N/T]` lines), a running
step's own `LeanInfo N/T` progress (graph, plan), the measured items of the plan (bundles and
statements, then pieces in overlap mode: the current run's lines in logs/measure*.log, or
work/times.json once the step is done) and the items live on the platform (publish/run_state.json
against publish/plan.json, whoever publishes them). `processes` match the driver, the background
publisher and the carve's Lean processes, so the page shows liveness.

How it stays current, and why here: a daemon thread of the driver (Reporter) re-reads the carve's
own files every INTERVAL s, and at once when pipeline_state.json changes (every step boundary
saves it), so none of the tools (oai_build_modules, carve_measure, split_run's loop) needed a
monitor call: their progress is already in the files they write. The driver marks the section
done or failed with its stopping reason when it ends (also on SIGTERM/SIGHUP/SIGINT, through
runlock.at_stop). A background publisher (overlap mode) can outlive its driver: split_run --go runs
a Reporter in role 'publisher' that refreshes the counts only while no driver holds the carve,
keeping the driver's final state, note and alerts.

Never a dependency: the section library is the monitor skill's section.py beside this skill (in the
same snapshot), or P2M_MONITOR_SECTION (empty or `off`: no section); when it is missing every call is
a no-op, and every failure is swallowed (counted in Reporter.errors). Tests point MONITOR_HOME at a
tmp dir."""
import hashlib
import importlib.util
import json
import os
import re
import threading
import time

from . import runlock
from .carvepipeline import OVERLAP_ONLY as _OVERLAP_ONLY, STEPS as _STEPS

INTERVAL = 60          # seconds between refreshes during a long step
POLL = 5               # seconds between looks at pipeline_state.json (a step boundary)
HEARTBEAT = 180        # three missed refreshes (and a bit) before the page calls it stale
PUB_SEP = ' | publisher: '
MEASURE_LINE = re.compile(r'^(bundle|statement|piece)\s+[\d.]+ s (ok|FAIL) (\S+)', re.M)
BUILD_LINE = re.compile(r'^([✔✖]) \[(\d+)/(\d+)\] (?:\w+ )?(\S+)', re.M)
COUNT_LINE = re.compile(r'^LeanInfo (\d+)/(\d+)\s', re.M)
KIND_LABEL = {'bundle': 'bundles', 'statement': 'statements', 'piece': 'pieces'}


def section_id(d):
    """`carve-<hash>`: the hash of the carve's systemd unit (carve_pipeline.unit_name)."""
    return 'carve-' + hashlib.sha1(os.path.realpath(d).encode()).hexdigest()[:10]


def worker_of(d):
    """The queue worker that owns carve dir d: the directory below ~/.claude/jobs/ or openai-ports/."""
    parts = os.path.realpath(d).split(os.sep)
    for i, p in enumerate(parts[:-1]):
        if p == 'openai-ports' or (p == 'jobs' and i and parts[i - 1] == '.claude'):
            return parts[i + 1]
    return None


def tilde(p):
    h = os.path.expanduser('~')
    return '~' + p[len(h):] if p == h or p.startswith(h + os.sep) else p


def section_lib():
    """The monitor skill's section module, or None (no monitor: every call is a no-op)."""
    p = os.environ.get('P2M_MONITOR_SECTION')
    if p is None:
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        p = os.path.join(root, 'monitor', 'section.py')
    if not p or p == 'off' or not os.path.isfile(p):
        return None
    try:
        spec = importlib.util.spec_from_file_location('_p2m_monitor_section', p)
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        return m if callable(getattr(m, 'publish', None)) else None
    except Exception:
        return None


class Files:
    """Reads JSON and text files, parsing each again only when its mtime or size changed."""

    def __init__(self):
        self._c = {}

    def _get(self, path, parse):
        try:
            st = os.stat(path)
        except OSError:
            return None
        key = (st.st_mtime_ns, st.st_size, parse)
        c = self._c.get(path)
        if c and c[0] == key:
            return c[1]
        try:
            with open(path, encoding='utf-8', errors='replace') as f:
                v = json.load(f) if parse == 'json' else f.read()
        except (OSError, ValueError):
            v = None
        self._c[path] = (key, v)
        return v

    def json(self, path):
        return self._get(path, 'json')

    def text(self, path):
        return self._get(path, 'text')


def last_run(text):
    """The part of a step log after its last `==== TIME STEP (skill SHA)` header (all of it without one)."""
    if not text:
        return ''
    i = text.rfind('\n==== ')
    return text[i + 1:] if i >= 0 else text


def planned(plan, external=()):
    """{kind: set of names} a carve's plan publishes: its bundles, and its statements and pieces that are
    not external (someone else's)."""
    plan = plan or {}
    ext = set(plan.get('external') or ()) | set(external or ())
    return {'bundle': {b['name'] for b in plan.get('bundles') or () if isinstance(b, dict) and 'name' in b},
            'statement': {n for n in plan.get('stubs') or {} if n not in ext},
            'piece': {n for n in plan.get('pieces') or {} if n not in ext}}


def kinds_note(got, plan_sets, kinds):
    return ', '.join('%s %d/%d' % (KIND_LABEL[k], len(got.get(k, ())), len(plan_sets[k])) for k in kinds if plan_sets[k])


def phase_state(status):
    return {'done': 'done', 'skipped': 'done', 'running': 'running', 'failed': 'failed'}.get(status, 'waiting')


class Carve:
    """What the page shows for one carve, read from its files."""

    def __init__(self, d, files=None):
        self.d = os.path.abspath(d)
        self.f = files or Files()

    def path(self, *p):
        return os.path.join(self.d, *p)

    def obj(self, *p):
        v = self.f.json(self.path(*p))
        return v if isinstance(v, dict) else {}

    def params(self):
        return self.obj('pipeline.json')

    def state(self):
        return self.obj('pipeline_state.json')

    def config(self):
        return self.obj('config.json')

    def steps(self, go=None):
        """This mode's steps; without --publish (go False) the publishing steps are left out."""
        ov = bool(self.params().get('overlap'))
        s = list(_STEPS) if ov else [x for x in _STEPS if x not in _OVERLAP_ONLY]
        if go is False:
            s = [x for x in s if x not in ('publish', 'publish_early')]
        return s

    def current(self, go=None):
        """(step, its status) the driver is on: a running or failed one, else the first not finished."""
        recs = self.state().get('steps') or {}
        steps = self.steps(go)
        for s in steps:
            if (recs.get(s) or {}).get('status') in ('running', 'failed'):
                return s, recs[s]['status']
        for s in steps:
            if (recs.get(s) or {}).get('status') not in ('done', 'skipped'):
                return s, (recs.get(s) or {}).get('status')
        return None, None

    def title(self):
        p = self.params()
        w = worker_of(self.d)
        return '%s%s: %s' % ('%s carve ' % w if w else 'Carve ', tilde(self.d),
                             p.get('root_module') or (p.get('targets') or ['?'])[0])

    def processes(self):
        d = re.escape(self.d)
        tail = re.escape(os.sep.join(self.d.split(os.sep)[-2:]))
        # not the workers' `carve_pipeline.py DIR --wait` processes, which only watch
        out = [{'label': 'driver', 'match': r'^(?!.*\s--wait\b).*carve_pipeline\.py\s+(?:%s|\S*%s)/?(?:\s|$)' % (d, tail)},
               {'label': 'publisher', 'match': r'split_run\.py\s.*%s' % re.escape(self.path('logs', 'publish_early.log'))}]
        # measure compiles under the carve dir; build and graph compile the port in WORKSPACE/Solutions/FOLDER
        where = [d + '/']
        if self.params().get('folder'):
            where.append(r'Solutions[/.]%s[/.]' % re.escape(self.params()['folder']))
        out.append({'label': 'lean', 'match': r'(?:^|/)(?:lean|leaninfo|lake)\s.*(?:%s)' % '|'.join(where)})
        return out

    # -- phases -------------------------------------------------------------------------------
    def phases(self, go=None):
        recs = self.state().get('steps') or {}
        steps = self.steps(go)
        st = lambda s: (recs.get(s) or {}).get('status')
        out = []
        cur, cur_status = self.current(go)
        n_done = sum(1 for s in steps if st(s) in ('done', 'skipped'))
        out.append({'name': 'Steps', 'done': n_done, 'total': len(steps),
                    'state': 'done' if cur is None else ('failed' if cur_status == 'failed' else 'running'),
                    'note': 'now %s' % cur if cur else 'all done'})
        b = self.build_phase(st('build'))
        if b:
            out.append(b)
        if cur and cur not in ('build', 'measure', 'measure_pieces'):
            g = self.count_phase(cur)
            if g:
                out.append(g)
        out += self.measure_phases(st)
        p = self.publish_phase()
        if p:
            out.append(p)
        return out

    def build_phase(self, status):
        text = self.f.text(self.path('build.log'))
        rows = BUILD_LINE.findall(text or '')
        if not rows:
            return None
        failed = sum(1 for r in rows if r[0] == '✖')
        done, total = int(rows[-1][1]), int(rows[-1][2])
        if status in ('done', 'skipped'):
            done = total
        note = 'last %s' % rows[-1][3].rsplit('.', 1)[-1]
        if failed:
            note = '%d failed; %s' % (failed, note)
        return {'name': 'Build (modules)', 'done': done, 'total': total, 'state': phase_state(status), 'note': note}

    def count_phase(self, step):
        """A running step's own `LeanInfo N/T` (graph, plan) progress in its log, or None."""
        rows = COUNT_LINE.findall(last_run(self.f.text(self.path('logs', step + '.log'))))
        if not rows:
            return None
        return {'name': '%s (modules)' % step.capitalize(), 'done': int(rows[-1][0]), 'total': int(rows[-1][1]),
                'state': 'running', 'note': 'LeanInfo readings'}

    def work_plan_times(self):
        cfg = self.config()
        work = os.path.expanduser(cfg.get('work') or self.path('carve_work'))
        work = work if os.path.isabs(work) else self.path(work)
        plan = os.path.expanduser(cfg.get('plan') or os.path.join(work, 'plan.json'))
        plan = plan if os.path.isabs(plan) else self.path(plan)
        return self.f.json(plan), os.path.join(work, 'times.json'), cfg

    def measure_phases(self, st):
        plan, times_path, cfg = self.work_plan_times()
        if not plan:
            return []
        sets = planned(plan, cfg.get('external'))
        groups = ([('measure', 'Measure bundles+statements', ('bundle', 'statement')),
                   ('measure_pieces', 'Measure pieces', ('piece',))] if self.params().get('overlap')
                  else [('measure', 'Measure', ('bundle', 'statement', 'piece'))])
        out = []
        for step, name, kinds in groups:
            total = sum(len(sets[k]) for k in kinds)
            if not total:
                continue
            status = st(step)
            got, failed = {k: set() for k in kinds}, 0
            if status in ('done', 'skipped'):
                for key, r in (self.f.json(times_path) or {}).items():
                    k, _, n = key.partition(':')
                    if k in got and n in sets[k]:
                        got[k].add(n)
                        failed += not (isinstance(r, dict) and r.get('ok'))
            elif status:
                last = {}
                for k, ok, n in MEASURE_LINE.findall(last_run(self.f.text(self.path('logs', step + '.log')))):
                    if k in got and n in sets[k]:
                        last[(k, n)] = ok
                for (k, n), ok in last.items():
                    got[k].add(n)
                    failed += ok == 'FAIL'
            note = kinds_note(got, sets, kinds)
            if failed:
                note += '; %d failed' % failed
            out.append({'name': name, 'done': sum(len(v) for v in got.values()), 'total': total,
                        'state': phase_state(status), 'note': note})
        return out

    def publish_phase(self):
        plan = self.f.json(self.path('publish', 'plan.json'))
        if not plan:
            return None
        sets = planned(plan)
        rs = self.f.json(self.path('publish', 'run_state.json')) or {}
        got, inflight, stopped = {k: set() for k in sets}, 0, 0
        for key, v in rs.items():
            k, _, n = key.partition(':')
            if k not in sets or n not in sets[k] or not isinstance(v, dict):
                continue
            s = v.get('state')
            if s == 'live':
                got[k].add(n)
            elif s == 'inflight':
                inflight += 1
            elif s not in (None, 'todo'):
                stopped += 1
        total = sum(len(v) for v in sets.values())
        if not total:
            return None
        done = sum(len(v) for v in got.values())
        note = kinds_note(got, sets, ('bundle', 'statement', 'piece'))
        if inflight:
            note += '; %d in flight' % inflight
        if stopped:
            note += '; %d stopped' % stopped
        if self.params().get('overlap') and sets['piece'] and not os.path.exists(self.path('publish', 'release.json')):
            note += '; pieces held until released'
        if not rs:
            state = 'waiting'
        else:
            state = 'done' if done == total else 'running'
        return {'name': 'Publish (live)', 'done': done, 'total': total, 'state': state, 'note': note}

    # -- liveness ---------------------------------------------------------------------------
    def driver_alive(self):
        return bool(runlock.peek(runlock.dir_key('pipeline', self.d), 'carve_pipeline'))

    def publisher_alive(self):
        return bool(runlock.peek(runlock.dir_key('publish', self.path('publish', 'run.json')), 'split_run'))


class Reporter:
    """Keeps a carve's section current from a daemon thread. role 'driver': carve_pipeline's own (start,
    finish); role 'publisher': split_run --go's, which writes only while no driver holds the carve."""

    def __init__(self, d, go=None, role='driver', pipeline=None, lib=None, home=None, interval=INTERVAL, poll=POLL):
        self.carve = Carve(d)
        self.d, self.go, self.role, self.pipeline, self.home = self.carve.d, go, role, pipeline, home
        self.lib = lib if lib is not None else section_lib()
        self.sid = section_id(self.d)
        self.interval, self.poll = interval, poll
        self.errors, self.last_error = 0, None
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = None
        self._finished = False

    # -- composing ---------------------------------------------------------------------------
    def owner(self):
        w = worker_of(self.d)
        return '%sdriver unit %s' % ('queue worker %s, ' % w if w else '', self.sid)

    def links(self):
        w = worker_of(self.d)
        if w and os.path.isdir(os.path.join(os.path.expanduser('~/claude/headless-agents'), w)):
            return [{'label': 'worker log', 'url': '/page/agent.html?name=' + w}]
        return []

    def running_note(self):
        c = self.carve
        cur, status = c.current(self.go)
        steps = c.steps(self.go)
        st = c.state()
        if cur is None:
            note = 'all steps done'
        else:
            rec = (st.get('steps') or {}).get(cur) or {}
            note = 'step %s (%d of %d)%s' % (cur, steps.index(cur) + 1, len(steps),
                                             ', since %s %s' % (rec['started'][11:16], time.strftime('%Z')) if rec.get('started') and status == 'running' else '')
        waiting = getattr(self.pipeline, 'waiting', None) if self.pipeline is not None else None
        if waiting:
            note += ': waiting for %s' % waiting
        elif c.publisher_alive() and cur not in ('publish',):
            note += '; background publisher running'
        extra = []
        if st.get('replans'):
            extra.append('re-plans %d' % st['replans'])
        if st.get('bundle_splits'):
            extra.append('bundle splits %d' % st['bundle_splits'])
        if st.get('piece_replans'):
            extra.append('piece re-plans %d' % st['piece_replans'])
        return note + (' (%s)' % ', '.join(extra) if extra else ''), bool(waiting)

    def compose(self, final=None):
        """The section's fields, or None when this reporter must not write (a publisher while a driver runs)."""
        c = self.carve
        sec = {'title': c.title(), 'phases': c.phases(self.go), 'processes': c.processes(), 'owner': self.owner(),
               'links': self.links(), 'heartbeat_secs': max(HEARTBEAT, 3 * self.interval), 'alerts': []}
        if self.role == 'publisher':
            if c.driver_alive():
                return None
            old = self.read_existing() or {}
            base = (old.get('note') or '').split(PUB_SEP)[0] or 'driver not running'
            sec['state'] = old.get('state') if old.get('state') in ('done', 'failed') else 'running'
            sec['alerts'] = list(old.get('alerts') or [])
            sec['note'] = base + PUB_SEP + (final[1] if final else 'still publishing')
            if final and sec['state'] == 'running':
                sec['state'] = final[0]
            return sec
        if final:
            state, reason = final
            sec['state'] = state
            sec['note'] = reason
            sec['phases'][0]['state'] = state
            if state == 'failed':
                sec['alerts'] = [reason[:600]]
                if c.publisher_alive():
                    sec['note'] += '; the background publisher still runs'
            return sec
        sec['note'], waiting = self.running_note()
        sec['state'] = 'waiting' if waiting else 'running'
        return sec

    def read_existing(self):
        try:
            return json.load(open(self.lib.path_of(self.sid, self.home)))
        except Exception:
            return None

    def refresh(self, final=None):
        """Write the section now; never raises."""
        if self.lib is None:
            return False
        with self._lock:
            try:
                sec = self.compose(final)
                if sec is None:
                    return False
                self.lib.publish(self.sid, home=self.home, **sec)
                return True
            except Exception as e:
                self.errors += 1
                self.last_error = repr(e)
                return False

    # -- the thread ---------------------------------------------------------------------------
    def start(self):
        """Publish once and keep the section current from a daemon thread; never raises."""
        if self.lib is None:
            return self
        try:
            self.refresh()
            self._thread = threading.Thread(target=self._loop, name='carve-monitor', daemon=True)
            self._thread.start()
            if self.role == 'driver':
                runlock.at_stop(self._on_signal)
        except Exception as e:
            self.errors += 1
            self.last_error = repr(e)
        return self

    def _mtime(self):
        try:
            return os.stat(os.path.join(self.d, 'pipeline_state.json')).st_mtime_ns
        except OSError:
            return None

    def _loop(self):
        seen, last = self._mtime(), time.time()
        while not self._stop.wait(self.poll):
            try:
                m = self._mtime()
                if m != seen or time.time() - last >= self.interval:
                    seen, last = m, time.time()
                    self.refresh()
            except Exception:
                self.errors += 1

    def stop(self):
        self._stop.set()
        t = self._thread
        if t is not None and t is not threading.current_thread():
            t.join(timeout=5)

    def finish(self, state, reason):
        """Stop the thread and write the final state (done or failed) with the stopping reason."""
        if self._finished:
            return
        self._finished = True
        try:
            self.stop()
        except Exception:
            pass
        self.refresh(final=(state, reason))

    def _on_signal(self, signum):
        cur = self.carve.current(self.go)[0]
        name = {15: 'SIGTERM', 1: 'SIGHUP', 2: 'SIGINT'}.get(signum, 'signal %s' % signum)
        self.finish('failed', 'driver stopped by %s%s' % (name, ' at ' + cur if cur else ''))


def stop_reason(err):
    """'stopped at STEP: why' from a StepFailed message: its first line, the next one when the first ends in
    a colon, the last line of the log tail when the first only says the tool exited non-zero, and how many
    items the message lists (`piece:X ...` lines)."""
    msg = str(err).strip()
    lines = [l.strip() for l in msg.splitlines() if l.strip()] or ['failed']
    first, rest = lines[0], lines[1:]
    m = re.match(r"step '(\w+)'(?: failed)?:?\s*(.*)$", first)
    where, why = (m.group(1), m.group(2)) if m else (None, first)
    if why.startswith('(exit'):
        tail = [l for l in rest if not l.startswith(('(exit', '$ ', '==== '))]
        why = why.split(';')[0] + (': ' + tail[-1] if tail else '')
    elif why.endswith(':') and rest:
        why += ' ' + rest[0]
    n = sum(1 for l in rest if re.match(r'(?:over: |needs a person: )?(?:bundle|statement|piece):\S', l))
    if n > 1:
        why += ' (%d items listed)' % n
    return ('stopped at %s: %s' % (where, why or 'failed') if where else 'stopped: ' + why)[:600]


def publisher_reporter(run_json):
    """split_run --go's Reporter for the carve its RUN.json lies in (role publisher), or None."""
    try:
        p = os.path.dirname(os.path.abspath(run_json))
        while True:
            if os.path.isfile(os.path.join(p, 'pipeline.json')):
                break
            q = os.path.dirname(p)
            if q == p:
                return None
            p = q
        return Reporter(p, role='publisher').start()
    except Exception:
        return None
