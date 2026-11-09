"""Publish a carved split (`carve.py plan` + `gen`) in waves, and keep publishing until done or stuck.

Items come from `carve.publish_order`: `bundle:NAME` (POST /submit-definition), `statement:NODE`
(POST /submit-problem, in batches) and `piece:NODE` (POST /verify). An item goes once everything it
imports is live; bundles go first, but while a statement or piece is ready bundles hold at most
`jobs` - 1 slots (q172: retrying bundles kept 827 ready statements unsent for 5 hours). Every result goes through `verdicts.classify` / `decide`: transients retry
unchanged, own timeouts split after two, WA/CE stop for a person, and a stopped item holds back
only what depends on it.

Text: `prose/<NAME>.md` for a bundle, `prose/<slug(statement name)>.md` for a statement (front
matter `title:`, optional `source:`), `explanations/<slug>.md` for a piece (checked by
`explanation.problems`). An item whose files are missing or fail a check is blocked, never posted.

State (`state` file, written after every post and result) makes a run resumable: live items are
never re-posted, in-flight jobs and submissions are polled again. A proof submission still PENDING
`stale_pending_hours` (config, default 3) after it was sent is lost: the piece is sent again, its
`also` reason naming the lost submission (our own PENDING proof would trip the live-proof guard), and
reconcile never adopts a lost one; after LOST_CAP resends the piece gives up for a person (oaiq-050,
2026-11-02: one submission stayed PENDING for 40 hours while its neighbours had verdicts in 2 minutes,
and the goal waited on it). Every run starts with
`reconcile`: each bundle and statement already on the platform under its name is adopted when its
text is the one we generated (prose not needed), and one with other text stops the whole run
before anything is posted (LiveMismatch), which is what makes extending a published carve safe;
a piece whose exact source is a live proof of its statement is adopted too. Terminal states (`split`, `stop`, `give_up`,
`raise_heartbeats`) wait for a person; `reset(item)` clears one.

The piece gate (`release` in the config, carve_pipeline's overlap mode): pieces are held, neither sent,
looked up, blocked nor counted unsendable, until the file `release` names says {"plan_sha": sha1 of the
plan file, "pieces": "all" | [item, ...]} for the plan this run loaded (re-read every pass, so a
running publisher picks the release up; a release written for another plan releases nothing, since
a re-planned piece may import a statement this run does not know). With nothing left to send but
held pieces, the run ends. With `gate_items` in the config (carve_pipeline streaming the bundles and
statements as they are measured, publish/run_stream.json), bundles and statements are held the same
way until the release's `items` ("all" | [item, ...]) lists them; a missing release, or one for
another plan, holds them all.

The platform is an object with `theorem_id(name)`, `existing(kind, name)` (the live statement or
bundle under that name: adopted only when its text is ours, whitespace aside, else the item stops
as "name taken"), `submit_definition(body) -> job`,
`submit_problems([problem]) -> [job]`, `job(id) -> record`, `verify(theorem_id, path, explanation)
-> submission`, `verdict(submission) -> record`, and optionally `disproved(names) -> [name]` (a
piece importing someone else's Disproved statement stops unsent); `LiveApi` is the real one, tests
pass a fake.
Erdős 3 v1 (2026-10-08..16) is why: per-mission loops retried one piece 740 times and re-carved
published bundles."""
import hashlib
import json
import os
import time

from . import carve as C
from . import explanation as E
from . import verdicts as V
from .mission import front_matter

FINAL_JOB = {'PUBLISHED', 'FAILED', 'ERROR'}
TERMINAL = {'split', 'stop', 'give_up', 'raise_heartbeats'}
RAISED_HEARTBEATS = 1000000
STALE_PENDING_HOURS = 3
LOST_CAP = 2             # resends of a lost submission before giving up for a person
RELEASE_OPEN_HOURS = 2   # an `open` release older than this is taken as final (its driver died)
RECONCILE_THREADS = 8    # platform lookups at once when a run starts (reconcile)
BATCH = 10
PIECE_JOBS = 32          # proofs in flight at once (config `piece_jobs`), apart from `jobs` for bundles and statements:
                         # a proof only queues on the verifier; dbenbenn 2026-11-06 ("no good reason to rate limit
                         # proofs") after q153 sent 4 at a time with ~700 waiting
PROVED_TTL = 600         # seconds a platform theorem status read for the bundle gate is reused


def _ws(s):
    return ' '.join((s or '').split())


def split_statement(text):
    """(import lines as a set, the rest whitespace-normalized) of a statement file or record."""
    lines = (text or '').split('\n')
    return ({l.strip() for l in lines if l.strip().startswith('import ')},
            _ws('\n'.join(l for l in lines if not l.strip().startswith('import '))))


def same_as_ours(kind, rec, text):
    """Is the live record `rec` the item we generated as `text` (whitespace aside)? A fake's
    {'same': True} stands for a record known to be ours."""
    if rec.get('same'):
        return True
    if kind == 'bundle':
        return _ws(rec.get('definition')) == _ws(text)
    ours = split_statement(text)
    theirs = (split_statement(rec.get('preamble'))[0], _ws(rec.get('formal_statement')))
    return ours == theirs


class LiveMismatch(RuntimeError):
    """A bundle or statement of the plan is live under its name with other text: nothing is posted."""


def _first_difference(ours, theirs):
    a, b = (ours or '').split('\n'), (theirs or '').split('\n')
    for i, (x, y) in enumerate(zip(a, b)):
        if _ws(x) != _ws(y):
            return 'line %d: ours %r, live %r' % (i + 1, x.strip()[:80], y.strip()[:80])
    return 'ours has %d lines, live %d' % (len(a), len(b))


class Runner:
    def __init__(self, cfg, api, sleep=time.sleep, poll_every=20, clock=time.time):
        self.cfg, self.api, self.sleep, self.poll_every, self.clock = cfg, api, sleep, poll_every, clock
        self.plan = json.load(open(cfg['plan'], encoding='utf-8'))
        self.ext = set(self.plan.get('external', []))
        order = C.publish_order(self.plan, self.ext)
        self.deps = order['deps']
        self.items = [x for w in order['waves'] for x in w]
        self.state = json.load(open(cfg['state'])) if os.path.exists(cfg['state']) else {}
        self.blocked = {}
        # `kinds`: only these item kinds are sent (say ['bundle'] for a first wave); `max_items`:
        # stop sending new items after this many in one run (in-flight ones are still followed)
        self.kinds = set(cfg.get('kinds') or ('bundle', 'statement', 'piece'))
        self.max_items = cfg.get('max_items')
        self.sent = 0
        self.plan_sha = hashlib.sha1(open(cfg['plan'], 'rb').read()).hexdigest()
        self._released = None
        self._items = 'all'      # the bundles and statements the gate lets go (released(), with `gate_items`)
        self._restart_changed()

    def file_sha(self, item):
        f = self.info(item)
        if not os.path.exists(f['file']):
            return None
        h = hashlib.sha1(open(f['file'], 'rb').read())
        if f.get('comparison') and os.path.exists(f['comparison']):
            h.update(b'\0' + open(f['comparison'], 'rb').read())   # writing one answers a refusal
        return h.hexdigest()

    def _restart_changed(self):
        """A terminal item (it waits for a person) whose file changed since it was sent starts over:
        that change is the person's answer, e.g. a re-split after verifier timeouts (oaiq-065, oaiq-071
        edited run_state.json by hand). So does a live piece whose file changed once its comparisons
        note exists (a fold, oaiq-124). States from before `sha` was recorded are left alone."""
        for x, st in list(self.state.items()):
            if x in self.items and not x.startswith('bundle:') and st.get('state') is not None:
                # renamed since it was sent (config `statement_suffixes`, q151): the state is keyed by node, so
                # the old name's statement or proof would count as this item's; states from before `name` was
                # recorded were sent under the node's plan-wide name
                n = x.split(':', 1)[1]
                was = st.get('name') or (C.pubname(n) if n in self.ext else
                                         C.pubname(n) + (self.plan.get('statement_suffix') or ''))
                now = self.info(x)['name']
                if was != now:
                    self.state.pop(x)
                    self.log(x, 'restart', 'published name changed from %s: sending it under the new one' % was)
                    continue
            if x in self.items and st.get('state') in TERMINAL and st.get('sha') and st['sha'] != self.file_sha(x):
                was = st['state']
                self.state.pop(x)
                self.log(x, 'restart', 'text changed since it stopped (%s): sending it again' % was)
            elif x in self.items and x.startswith('piece:') and st.get('state') == 'live' and st.get('sha') \
                    and st['sha'] != self.file_sha(x) and os.path.exists(self.info(x)['comparison']):
                # a live piece regenerated on purpose (`carve.py fold`: the folded statement's proof now
                # inline, oaiq-124) goes again once comparisons/<slug>.md says why, as its old proof is
                # live; without a note a changed live piece stays as it is
                self.state.pop(x)
                self.log(x, 'restart', 'text changed since it went live and a comparison answers its '
                         'live proof: sending it again')

    # ------------------------------------------------------------------ the piece gate
    def released(self):
        """The pieces the gate lets go: 'all', a set of items, or None (pieces held). Without a
        `release` in the config every piece goes. With `gate_items`, the bundles and statements it lets
        go are set aside in self._items the same way (held() reads them); without, all of them."""
        path = self.cfg.get('release')
        gate = bool(self.cfg.get('gate_items'))
        self._items = None if gate else 'all'
        if not path:
            self._items = 'all'
            return 'all'
        try:
            r = json.load(open(os.path.expanduser(path), encoding='utf-8'))
        except (OSError, ValueError):
            return None
        if not isinstance(r, dict) or r.get('plan_sha') != self.plan_sha:
            return None
        if gate:
            self._items = 'all' if r.get('items') == 'all' else set(r.get('items') or ())
        return 'all' if r.get('pieces') == 'all' else set(r.get('pieces') or ())

    def held(self, item, rel=None):
        rel = self.released() if rel is None else rel
        if not item.startswith('piece:'):
            it = self._items
            return not (it == 'all' or (it and item in it))
        return not (rel == 'all' or (rel and item in rel))

    # ------------------------------------------------------------------ items and their files
    def info(self, item):
        kind, n = item.split(':', 1)
        out, prose = self.cfg['out'], self.cfg['prose']
        if kind == 'bundle':
            return {'kind': kind, 'name': n, 'file': os.path.join(out, 'lib', 'Def_%s.lean' % n),
                    'text': os.path.join(prose, '%s.md' % n)}
        name = C.statement_name(self.plan, n)
        s = C.slug(name)
        if kind == 'statement':
            return {'kind': kind, 'name': name, 'file': os.path.join(out, 'lib', 'Thm_%s.lean' % s),
                    'text': os.path.join(prose, '%s.md' % s)}
        cmp_dir = self.cfg.get('comparisons') or os.path.join(os.path.dirname(self.cfg['explanations']), 'comparisons')
        return {'kind': kind, 'name': name, 'file': os.path.join(out, 'solutions', 'Sol_%s.lean' % s),
                'text': os.path.join(self.cfg['explanations'], '%s.md' % s), 'node': n,
                'comparison': os.path.join(cmp_dir, '%s.md' % s)}

    def check(self, item):
        """None if the item's files are ready to send, else why not."""
        f = self.info(item)
        for p in (f['file'], f['text']):
            if not os.path.exists(p):
                return 'missing ' + p
        # the platform's soundness guard (WLTime 2026-10-23: `prelude` in a bundle, compile_error)
        from .leantext import guard_problems, guard_message
        # the guard reads the whole file (0.08 s for a 650 KB bundle): once per file version, not every pass
        # (q153: ready() spent 8 s a pass on 262 ready items)
        key = (f['file'], os.path.getmtime(f['file']), os.path.getsize(f['file']))
        cache = self.__dict__.setdefault('_guard', {})
        if key not in cache:
            cache[key] = guard_problems(open(f['file'], encoding='utf-8').read())
        bad = cache[key]
        if bad:
            return 'the soundness guard would refuse %s: %s' % (os.path.basename(f['file']), guard_message(bad))
        text = open(f['text'], encoding='utf-8').read()
        if f['kind'] == 'piece':
            bad = E.problems(text)
            return 'explanation: ' + '; '.join(bad) if bad else None
        fields, body = front_matter(text)
        if not fields.get('title') or not body.strip():
            return 'prose needs a title and a statement: ' + f['text']
        if len(fields['title']) > 200:
            return 'title over 200 characters: ' + f['text']
        return None

    def prose(self, item):
        f = self.info(item)
        fields, body = front_matter(open(f['text'], encoding='utf-8').read())
        return fields['title'].strip(), body.strip(), fields.get('source', self.cfg.get('source', '')).strip()

    # ------------------------------------------------------------------ state
    def st(self, item):
        return self.state.setdefault(item, {'state': 'todo', 'history': {}})

    def save(self):
        for x, st in self.state.items():          # the name each item was sent under (_restart_changed)
            if x in self.items and not x.startswith('bundle:') and isinstance(st, dict) and 'name' not in st:
                st['name'] = self.info(x)['name']
        tmp = self.cfg['state'] + '.tmp'
        json.dump(self.state, open(tmp, 'w'), indent=1, sort_keys=True)
        os.replace(tmp, self.cfg['state'])

    def log(self, item, action, what):
        name = self.info(item)['name']
        with open(self.cfg['log'], 'a', encoding='utf-8') as f:
            f.write('%s  %s  %s  %s\n' % (time.strftime('%Y-%m-%d %H:%M'), name, action, what))

    def note(self, action, what):
        """A line of the run itself, not of one item."""
        with open(self.cfg['log'], 'a', encoding='utf-8') as f:
            f.write('%s  -  %s  %s\n' % (time.strftime('%Y-%m-%d %H:%M'), action, what))

    def live(self, item):
        return self.state.get(item, {}).get('state') == 'live'

    def ready(self):
        self.blocked = {}
        out = []
        rel = self._released = self.released()
        for x in self.items:
            s = self.state.get(x, {}).get('state', 'todo')
            if s != 'todo' or x.split(':', 1)[0] not in self.kinds or self.held(x, rel):
                continue
            stopped = [d for d in self.deps[x] if self.state.get(d, {}).get('state') in TERMINAL
                       and not self.proved_on_platform(d)]
            if stopped:
                self.blocked[x] = 'waits on stopped ' + ', '.join(stopped)
                continue
            if not all(self.live(d) or self.proved_on_platform(d) for d in self.deps[x]):
                continue
            # a bundle imports statements: the platform wants them Proved, and our live proof may be only a sketch
            # whose own imports are Open (q153 2026-11-09: OAIQ098G362 refused, nine bundles behind it)
            unproved = [d for d in self.deps[x] if x.startswith('bundle:') and d.startswith('piece:')
                        and not self.statement_proved(d)]
            if unproved:
                self.blocked[x] = 'waits until Proved: ' + ', '.join(unproved)
                continue
            why = self.check(x)
            if why:
                self.blocked[x] = why
            else:
                out.append(x)
        # bundles first: their chain is the critical path, so they never wait for a slot behind
        # statements or pieces
        rank = {'bundle': 0, 'statement': 1, 'piece': 2}
        return sorted(out, key=lambda x: rank[x.split(':', 1)[0]])

    def statement_proved(self, item):
        """Is the statement of piece `item` Proved on the platform (each looked up at most every PROVED_TTL
        seconds, and only once it is Proved for good)?"""
        status = getattr(self.api, 'theorem_status', None)
        if status is None:
            return True                    # an API without statuses: our live proof is all we can know
        cache = self.__dict__.setdefault('_stmt_proved', {})
        hit = cache.get(item)
        if hit and (hit[1] or self.clock() - hit[0] < PROVED_TTL):
            return hit[1]
        n = item.split(':', 1)[1]
        tid = self.state.get('statement:' + n, {}).get('id') if n not in self.ext \
            else self.api.theorem_id(self.info(item)['name'])
        try:
            ok = bool(tid) and status(tid) == 'Proved'
        except Exception:
            ok = False
        cache[item] = (self.clock(), ok)
        return ok

    def proved_on_platform(self, item):
        """Is the statement of `item` (a piece another item waits for: a bundle importing its statement) Proved
        on the platform although our proof did not go live: someone else's proof settled it (comparisons
        "Same as", or the live-proof guard refused ours)? A bundle needs the statement Proved, not our proof
        (q153, 2026-11-06: four bundles waited on pieces dphz had proved; they were set live by hand). Only
        stopped pieces are looked up, each at most every PROVED_TTL seconds."""
        if not item.startswith('piece:') or self.state.get(item, {}).get('state') not in TERMINAL:
            return False
        status = getattr(self.api, 'theorem_status', None)
        if status is None:
            return False
        cache = self.__dict__.setdefault('_proved', {})
        hit = cache.get(item)
        if hit and self.clock() - hit[0] < PROVED_TTL:
            return hit[1]
        n = item.split(':', 1)[1]
        tid = self.state.get('statement:' + n, {}).get('id') if n not in self.ext \
            else self.api.theorem_id(self.info(item)['name'])
        try:
            ok = bool(tid) and status(tid) == 'Proved'
        except Exception:
            ok = False
        cache[item] = (self.clock(), ok)
        return ok

    def unsendable(self):
        """{item: why} for every item still to send (any wave, not only the ready ones) whose files are
        missing or fail a check: what a live run would block on (oaiq-047: 12 forced statements had no
        prose; the dry run, which checked only what it would send at once, was clean)."""
        out = {}
        rel = self.released()
        for x in self.items:
            if self.state.get(x, {}).get('state', 'todo') != 'todo' or x.split(':', 1)[0] not in self.kinds \
                    or self.held(x, rel):
                continue
            why = self.check(x)
            if why:
                out[x] = why
        return out

    # ------------------------------------------------------------------ what is already live
    def reconcile(self, write=True):
        """Look up every bundle and statement not yet live in the state: one live under its name
        with our text is adopted (no prose needed: it was published by an earlier run or carve);
        one with other text is collected. Returns ({item: id} adopted, [mismatch]). With `write`,
        adoptions go into the state and the log, and a mismatch raises LiveMismatch before
        anything is posted. Boone-Higman (2026-10-24): a carve extended after its first bundles
        were live started from a fresh state, and its run would have re-posted them."""
        adopted, bad, self.proved_elsewhere = {}, [], {}
        proofs = getattr(self.api, 'live_proofs', None)
        rel = self.released()
        if write:
            # q150: 2-3 s a lookup, so a restart with many unsent items is silent for minutes
            n = sum(1 for x in self.items if self.state.get(x, {}).get('state') not in ('live', 'inflight')
                    and not self.held(x, rel))
            if n:
                self.note('reconcile', 'looking up %d items not yet live on the platform before sending anything '
                          '(a few seconds each, %d at once)' % (n, RECONCILE_THREADS))
        todo = []
        for x in self.items:
            if self.state.get(x, {}).get('state') in ('live', 'inflight') or self.held(x, rel):
                continue
            f = self.info(x)
            if not os.path.exists(f['file']) or (x.startswith('piece:') and proofs is None):
                continue
            todo.append((x, f))

        def look(xf):
            x, f = xf
            if x.startswith('piece:'):
                lost = set(self.state.get(x, {}).get('lost', []))
                return [r for r in proofs(f['name']) if r.get('id') not in lost]
            return self.api.existing(x.split(':', 1)[0], f['name'])

        # each lookup is a few seconds of HTTP: RECONCILE_THREADS at once (q153, 2026-11-07: a restart of the
        # publisher with 1,800 released items unsent would have looked them up one by one for over an hour)
        if len(todo) > 1:
            from concurrent.futures import ThreadPoolExecutor
            with ThreadPoolExecutor(max_workers=RECONCILE_THREADS) as pool:
                found = list(pool.map(look, todo))
        else:
            found = [look(xf) for xf in todo]
        for (x, f), rec in zip(todo, found):
            kind = x.split(':', 1)[0]
            if kind == 'piece':
                # our exact source already live is adopted; someone else's live proof is reported
                # (a run's post_verify refuses the item then, for a person to compare)
                text = _ws(open(f['file'], encoding='utf-8').read())
                mine = [r for r in rec if _ws(r.get('content')) == text]
                if mine:
                    adopted[x] = mine[0]['id']
                elif rec:
                    self.proved_elsewhere[x] = ['%s (%s, %s)' % (r.get('id'), r.get('status'), r.get('author') or '?')
                                                for r in rec]
                continue
            if not rec:
                continue
            text = open(f['file'], encoding='utf-8').read()
            if same_as_ours(kind, rec, text):
                adopted[x] = rec['id']
                continue
            theirs = rec.get('definition') if kind == 'bundle' else \
                (rec.get('preamble') or '') + '\n\n' + (rec.get('formal_statement') or '')
            bad.append({'item': x, 'kind': kind, 'name': f['name'], 'id': rec.get('id'),
                        'author': rec.get('author') or '?', 'file': f['file'],
                        'diff': _first_difference(text, theirs) if theirs else 'live text not served'})
        if write:
            for x, i in adopted.items():
                self.st(x).update(state='live', id=i)
                self.log(x, 'adopt', i)
            if adopted:
                self.save()
            if bad:
                for m in bad:
                    self.log(m['item'], 'LIVE TEXT DIFFERS', 'id %s by %s; %s' % (m['id'], m['author'], m['diff']))
                raise LiveMismatch(mismatch_message(bad))
        return adopted, bad

    def reset(self, item):
        self.state.pop(item, None)
        self.save()

    # ------------------------------------------------------------------ one pass
    def _result(self, item, rec, action):
        st = self.st(item)
        kind = V.classify(rec.get('status'), rec.get('error_message') or rec.get('error'))
        dec = V.decide(kind, st['history'], item.split(':', 1)[0])
        st['history'][kind] = st['history'].get(kind, 0) + 1
        st.pop('job', None)
        st.pop('sid', None)
        if dec == 'done':
            st['state'] = 'live'
            st['id'] = rec.get('theorem_id') or rec.get('definition_id') or rec.get('submission_id') or st.get('id')
            self.log(item, action, '%s %s' % (rec.get('status'), st['id']))
        elif dec == 'raise_heartbeats' and self._raise_heartbeats(item):
            # the person's fix every time (oaiq-055: four Lech bundles), done once; a second heartbeat
            # timeout waits for a person as before
            st['state'] = 'todo'
            st['last'] = (rec.get('error_message') or rec.get('error') or '')[:500]
            self.log(item, action, '%s heartbeat timeout: raised maxHeartbeats to %d, sending again' % (
                rec.get('status'), RAISED_HEARTBEATS))
        else:
            st['state'] = 'todo' if dec == 'retry' else dec
            st['last'] = (rec.get('error_message') or rec.get('error') or '')[:500]
            # nothing is ever split here: a terminal state waits for a person (v1's automatic
            # splitter re-split items for days)
            why = {'split': ('NEEDS A PERSON: own compile timeout %d times; consider splitting' % (
                       st['history'].get('own_timeout', 0)) if kind == 'own_timeout' else
                       'killed for memory %d times: carve_pipeline splits it (calibrate_pieces)' % (
                           st['history'].get('hidden', 0) + st['history'].get('dependency_oom', 0))),
                   'stop': 'NEEDS A PERSON: %s' % (
                       'hidden: the platform cut the log before the error (see verdicts.py); compare a '
                       'local verifier-flags compile, then retry or split' if kind == 'hidden' else kind),
                   'give_up': 'NEEDS A PERSON: transient cap reached',
                   'raise_heartbeats': 'NEEDS A PERSON: heartbeat timeout'}.get(dec, dec)
            self.log(item, action, '%s %s  -> %s' % (rec.get('status'), st['last'][:200], why))
        self.save()

    def _raise_heartbeats(self, item):
        """Add `set_option maxHeartbeats N` after a bundle's or piece's imports, unless it already sets
        it; True when the file changed. Statements are left alone (their text is split into preamble
        and formal statement on the platform)."""
        f = self.info(item)
        if f['kind'] == 'statement' or not os.path.exists(f['file']):
            return False
        text = open(f['file'], encoding='utf-8').read()
        if 'set_option maxHeartbeats' in text:
            return False
        lines = text.split('\n')
        last = max((i for i, l in enumerate(lines) if l.startswith('import ')), default=-1)
        lines[last + 1:last + 1] = ['', 'set_option maxHeartbeats %d' % RAISED_HEARTBEATS]
        with open(f['file'], 'w', encoding='utf-8') as out:
            out.write('\n'.join(lines))
        # overlap mode keeps the published text in published/lib, which `gen` writes frozen bundles from
        # (oaiq-122: without this a re-plan regenerated the old text and the names step stopped)
        fz = self.cfg.get('frozen_lib')
        q = os.path.join(os.path.expanduser(fz), os.path.basename(f['file'])) if fz else None
        if q and os.path.exists(q):
            with open(q, 'w', encoding='utf-8') as out:
                out.write('\n'.join(lines))
        return True

    def _fetch_all(self, fn, args):
        """[fn(a) for a in args], RECONCILE_THREADS at once (each a few seconds of HTTP; q153: with ~45 jobs in
        flight, polling and the lookups before posting one by one held a pass to minutes)."""
        if len(args) < 2:
            return [fn(a) for a in args]
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=RECONCILE_THREADS) as pool:
            return list(pool.map(fn, args))

    def poll(self):
        live_now = [(x, self.state[x]) for x in self.items
                    if self.state.get(x) and self.state[x].get('state') == 'inflight']
        recs = self._fetch_all(lambda xs: self.api.job(xs[1]['job']) if 'job' in xs[1] else self.api.verdict(xs[1]['sid']),
                               live_now)
        for (x, st), rec in zip(live_now, recs):
            if st.get('state') != 'inflight':
                continue
            if 'job' in st:
                if rec.get('status') in FINAL_JOB:
                    self._result(x, rec, 'publish')
                else:
                    self._check_lost_job(x, st)
            else:
                if rec.get('status') and rec.get('status') != 'PENDING':
                    rec.setdefault('submission_id', st['sid'])
                    self._result(x, rec, 'verdict')
                else:
                    self._check_lost(x, st)

    def _check_lost(self, x, st):
        """A submission PENDING past the limit is lost: send the piece again, or give up after
        LOST_CAP resends. A state from before `sent` was recorded is timed from this poll."""
        now = self.clock()
        if 'sent' not in st:
            st['sent'] = now
            self.save()
            return
        hours = float(self.cfg.get('stale_pending_hours', STALE_PENDING_HOURS))
        if now - st['sent'] < hours * 3600:
            return
        n = st['history'].get('lost', 0)
        st['history']['lost'] = n + 1
        sid = st.pop('sid')
        st.pop('sent')
        st['lost'] = st.get('lost', []) + [sid]
        st['last'] = 'no verdict after %.1f h: submission %s lost' % (hours, sid)
        if n < LOST_CAP:
            st['state'] = 'todo'
            self.log(x, 'verdict', '%s, sending again' % st['last'])
        else:
            st['state'] = 'give_up'
            self.log(x, 'verdict', 'NEEDS A PERSON: %s (%d resends lost too)' % (st['last'], n))
        self.save()

    def _check_lost_job(self, x, st):
        """A publish job (bundle or statement) unfinished past the limit is lost, like a submission: q172
        (2026-11-05), two definition jobs stayed COMPILING for 8 hours, held two of the run's slots, and with
        something in flight the run never ended. If the item is live under its name with our text meanwhile it
        is adopted; else it is sent again, and after LOST_CAP resends it waits for a person."""
        now = self.clock()
        if 'sent' not in st:
            st['sent'] = now
            self.save()
            return
        hours = float(self.cfg.get('stale_pending_hours', STALE_PENDING_HOURS))
        if now - st['sent'] < hours * 3600:
            return
        f = self.info(x)
        rec = self.api.existing(f['kind'], f['name'])
        if rec and os.path.exists(f['file']) and same_as_ours(f['kind'], rec, open(f['file'], encoding='utf-8').read()):
            st.pop('job')
            st.pop('sent')
            st.update(state='live', id=rec['id'])
            self.log(x, 'publish', 'job unfinished after %.1f h, but live under its name: adopted %s' % (hours, rec['id']))
            self.save()
            return
        n = st['history'].get('lost', 0)
        st['history']['lost'] = n + 1
        job = st.pop('job')
        st.pop('sent')
        st['lost'] = st.get('lost', []) + [job]
        st['last'] = 'no result after %.1f h: publish job %s lost' % (hours, job)
        if n < LOST_CAP:
            st['state'] = 'todo'
            self.log(x, 'publish', '%s, sending again' % st['last'])
        else:
            st['state'] = 'give_up'
            self.log(x, 'publish', 'NEEDS A PERSON: %s (%d resends lost too)' % (st['last'], n))
        self.save()

    def inflight(self):
        return sum(1 for s in self.state.values() if s.get('state') == 'inflight')

    def submit(self, items):
        # bundles and statements share `jobs` slots; proofs have their own `piece_jobs` (PIECE_JOBS)
        jobs = self.cfg.get('jobs', 8)
        pjobs = self.cfg.get('piece_jobs', PIECE_JOBS)
        busy_of = lambda pred: sum(1 for x, s in self.state.items() if s.get('state') == 'inflight' and pred(x))
        pieces = [x for x in items if x.startswith('piece:')]
        items = [x for x in items if not x.startswith('piece:')]
        room = jobs - busy_of(lambda x: not x.startswith('piece:'))
        if jobs >= 2 and any(x.startswith('statement:') for x in items):
            # one slot stays for statements while any are ready: bundles go first, but q172 had four bundles
            # cycling through cold-worker retries while 827 ready statements waited 5 hours
            busy = busy_of(lambda x: x.startswith('bundle:'))
            nb = max(0, min(room, jobs - 1 - busy))
            bundles = [x for x in items if x.startswith('bundle:')]
            items = bundles[:nb] + [x for x in items if not x.startswith('bundle:')]
        items = items[:max(room, 0)] + pieces[:max(pjobs - busy_of(lambda x: x.startswith('piece:')), 0)]
        if self.max_items is not None:
            items = items[:max(self.max_items - self.sent, 0)]
        self.sent += len(items)
        stmts = []
        # the name lookup each bundle and statement gets before it is posted (_submit_one), all at once
        look = [x for x in items if not x.startswith('piece:')]
        def lookup(x):
            try:
                return self.api.existing(x.split(':', 1)[0], self.info(x)['name'])
            except Exception as e:                   # raised again in _submit_one, whose handler retries it
                return e
        self._prefetched = dict(zip(look, self._fetch_all(lookup, look)))
        for x in items:
            try:
                self._submit_one(x, stmts)
            except Exception as e:                       # a refused post: this item waits for a person
                st = self.st(x)
                hist = st.setdefault('history', {})
                if V.classify(None, str(e)) == 'transient' and V.decide('transient', hist) == 'retry':
                    # the platform's server error, not the item (q151): send it again on a later pass
                    hist['transient'] = hist.get('transient', 0) + 1
                    st.update(state='todo', last=str(e)[:500])
                    self.log(x, 'transient', str(e)[:200])
                    self.save()
                    continue
                st.update(state='stop', last=str(e)[:500], sha=self.file_sha(x))
                self.log(x, 'refused', str(e)[:200])
                self.save()
        for i in range(0, len(stmts), BATCH):
            batch = stmts[i:i + BATCH]
            try:
                self._submit_statements(batch)
            except Exception as e:
                for x in batch:
                    self.st(x).update(state='stop', last=str(e)[:500])
                    self.log(x, 'refused', str(e)[:200])
                self.save()
        return len(items)

    def _submit_one(self, x, stmts):
        f, st = self.info(x), self.st(x)
        if f['kind'] in ('bundle', 'statement'):
            pre = getattr(self, '_prefetched', {})
            rec = pre.pop(x) if x in pre else self.api.existing(f['kind'], f['name'])
            if isinstance(rec, Exception):
                raise rec
            if rec:
                text = open(f['file'], encoding='utf-8').read()
                if same_as_ours(f['kind'], rec, text):      # ours from an earlier run: adopt it
                    st.update(state='live', id=rec['id'])
                    self.log(x, 'adopt', rec['id'])
                else:
                    # KervaireMixing 2026-10-18: someone else's statement under our name was
                    # adopted by name, and our pieces imported it
                    what = 'statement' if f['kind'] == 'statement' else 'definitions bundle'
                    st.update(state='stop', last='name taken by a different %s (author %s, id %s); '
                              'use statement_suffix (or another bundle_prefix) for a fresh name' % (
                                  what, rec.get('author') or '?', rec.get('id')))
                    self.log(x, 'name-taken', st['last'])
                self.save()
                return
        if f['kind'] == 'bundle':
            title, body, source = self.prose(x)
            job = self.api.submit_definition({
                'definition_name': f['name'], 'definition_title': title,
                'definition': open(f['file'], encoding='utf-8').read(),
                'natural_language_statement': body, 'source': source,
                'tags': self.cfg.get('tags', [])})
            st.update(state='inflight', job=job, sha=self.file_sha(x), sent=self.clock())
            self.log(x, 'submit-definition', 'job %s' % job)
            self.save()
        elif f['kind'] == 'statement':
            stmts.append(x)
        else:
            n = f['node']
            tid = self.state.get('statement:' + n, {}).get('id') if n not in self.ext \
                else self.api.theorem_id(f['name'])
            if not tid:
                self.blocked[x] = 'no theorem id for ' + f['name']
                return
            # someone else's live proof: the guard refuses ours until a person has read it and written
            # comparisons/<slug>.md, "Different from <id>: ..." (sent as the reason) or "Same as <id>: ..."
            # (settled, not sent); submit_all.py's convention (oaiq-068)
            also = open(f['comparison'], encoding='utf-8').read().strip() if os.path.exists(f['comparison']) else ''
            if st.get('lost') and not also.startswith('Same as'):
                also = '\n'.join(filter(None, [also, 'resending: our own submission(s) %s never got a verdict' % (
                    ', '.join(st['lost']))]))
            if also.startswith('Same as'):
                st.update(state='stop', last='settled: ' + also.split('\n')[0][:300], sha=self.file_sha(x))
                if self.proved_on_platform(x):
                    # read, compared and Proved by the other proof: nothing is left for a person
                    st['state'] = 'live'
                self.log(x, 'settled', also.split('\n')[0][:200] + ('' if st['state'] == 'stop' else
                                                                      ' (the theorem is Proved)'))
                self.save()
                return
            bad = self.disproved_imports(f['file'])
            if bad:                                      # submit() stops the item for a person
                from .importcheck import disproved_message
                raise RuntimeError(disproved_message(bad))
            expl = open(f['text'], encoding='utf-8').read()
            sid = self.api.verify(tid, f['file'], expl, also=also) if also else self.api.verify(tid, f['file'], expl)
            st.update(state='inflight', sid=sid, sha=self.file_sha(x), sent=self.clock())
            self.log(x, 'submit piece (try %d)' % (sum(st['history'].values()) + 1), sid)
            self.save()

    def disproved_imports(self, path):
        """The statements published by someone else (`external` nodes and the `Theorems.*` modules of
        the plan's external_defs, i.e. carve.py's external_theorems) that the piece at `path` imports
        and the platform lists as Disproved: a proof resting on one is accepted, but its target can
        never become Proved, and /open-leaves hides why (oaiq-109; p2mlib.importcheck, the check
        submit_solution.py runs). The run's own statements are not looked up."""
        check = getattr(self.api, 'disproved', None)
        if check is None:
            return []
        from .importcheck import theorem_imports
        foreign = {m: n for n, m in (self.plan.get('external_defs') or {}).items() if m.startswith('Theorems.')}
        for n in self.ext:
            name = C.statement_name(self.plan, n)
            foreign['Theorems.Thm_' + C.slug(name)] = name
        names = sorted({foreign[m] for m in theorem_imports(open(path, encoding='utf-8').read()) if m in foreign})
        return check(names) if names else []

    def _submit_statements(self, batch):
        probs = []
        for x in batch:
            f = self.info(x)
            title, body, source = self.prose(x)
            lines = open(f['file'], encoding='utf-8').read().split('\n')
            probs.append({'theorem_name': f['name'], 'theorem_title': title,
                          'preamble': '\n'.join(l for l in lines if l.startswith('import ')),
                          'formal_statement': '\n'.join(l for l in lines if not l.startswith('import ')).strip() + '\n',
                          'natural_language_statement': body, 'source': source,
                          'tags': self.cfg.get('tags', [])})
        jobs = self.api.submit_problems(probs)
        for x, job in zip(batch, jobs):
            self.st(x).update(state='inflight', job=job, sha=self.file_sha(x), sent=self.clock())
            self.log(x, 'submit-problem', 'job %s' % job)
        self.save()

    def step(self):
        """Poll what is in flight, then send what is ready. True while there is anything to wait for."""
        self.poll()
        sent = self.submit(self.ready())
        return bool(self.inflight() or sent)

    def run(self, max_hours=None):
        t0 = time.time()
        self.reconcile()
        while True:
            more = self.step()
            if max_hours and time.time() - t0 > max_hours * 3600:
                break
            if more:
                if self.inflight():
                    self.sleep(self.poll_every)
                continue
            if not self.release_open():
                break
            # carve_pipeline streams the pieces: more of them are released as they are measured
            self.sleep(self.poll_every * 3)
        return self.summary()

    def release_open(self):
        """Is the release for this plan still growing (carve_pipeline's streaming measure and measure_pieces
        write `open`), with items still held? Not when the file is older than RELEASE_OPEN_HOURS: a driver that
        died must not keep the publisher waiting."""
        path = self.cfg.get('release')
        if not path:
            return False
        path = os.path.expanduser(path)
        try:
            r = json.load(open(path, encoding='utf-8'))
            age = self.clock() - os.path.getmtime(path)
        except (OSError, ValueError):
            return False
        if not isinstance(r, dict) or not r.get('open') or r.get('plan_sha') != self.plan_sha \
                or age > RELEASE_OPEN_HOURS * 3600:
            return False
        rel = self.released()
        return any(self.state.get(x, {}).get('state', 'todo') == 'todo' and self.held(x, rel) for x in self.items)

    def summary(self):
        states = [self.state.get(x, {}).get('state', 'todo') for x in self.items]
        self.ready()
        rel = self.released()
        return {'live': states.count('live'), 'inflight': states.count('inflight'),
                'todo': states.count('todo'),
                'held': sum(1 for x, s in zip(self.items, states) if s == 'todo' and self.held(x, rel)),
                'stopped': [x for x, s in zip(self.items, states) if s in TERMINAL],
                'blocked': dict(self.blocked), 'total': len(self.items)}

    def dry_run(self, read=True):
        """What a run would adopt and send first, and what is blocked, writing nothing (neither
        the platform nor the state file). With `read`, it looks the plan's names up on the
        platform (reads only) as a run would; `read=False` touches no API at all."""
        adopted, bad = self.reconcile(write=False) if read else ({}, [])
        saved = self.state
        self.state = json.loads(json.dumps(saved))
        for x, i in adopted.items():
            self.st(x).update(state='live', id=i)
        try:
            return {'ready': self.ready(), 'blocked': dict(self.blocked), 'adopt': adopted,
                    'unsendable': self.unsendable(),
                    'mismatch': bad, 'proved_elsewhere': dict(getattr(self, 'proved_elsewhere', {})),
                    'items': len(self.items),
                    'held': sum(1 for x in self.items if self.state.get(x, {}).get('state', 'todo') == 'todo'
                                and self.held(x)),
                    'live': sum(self.live(x) for x in self.items)}
        finally:
            self.state = saved


def mismatch_message(bad):
    lines = ['%d name(s) of this plan are live on prove2.me with different text; nothing was posted.'
             % len(bad)]
    for m in bad:
        what = 'definitions bundle' if m['kind'] == 'bundle' else 'statement'
        lines.append('  %s %s: live id %s by %s; %s (ours: %s)' % (
            what, m['name'], m['id'], m['author'], m['diff'], m['file']))
    lines.append('A published item is frozen. If it is ours, regenerate the file to match it '
                 '(carve.py gen writes frozen bundles from their published copy and re-applies '
                 'work/repairs.json; a statement published by an earlier carve goes in '
                 'external_theorems). If the name is someone else\'s, carve under a fresh name '
                 '(statement_suffix, or another bundle_prefix).')
    return '\n'.join(lines)


class ReadOnly:
    """An API wrapper for dry runs: lookups pass through, every write raises."""
    READS = ('theorem_id', 'existing', 'live_proofs', 'disproved', 'theorem_status')

    def __init__(self, api):
        self._api = api

    def __getattr__(self, k):
        if k in self.READS:
            return getattr(self._api, k)
        raise RuntimeError('dry run: %s would write to the platform' % k)


class LiveApi:
    """prove2.me, through p2m.call and submit_verify.post_verify."""

    def __init__(self):
        import sys
        here = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts')
        if here not in sys.path:
            sys.path.insert(0, here)
        import p2m
        import submit_verify
        from . import api
        self._call, self._post, self._api = p2m.call, submit_verify.post_verify, api

    def _ok(self, r, what):
        if not isinstance(r, dict) or r.get('__error'):
            raise RuntimeError('%s: %s' % (what, r))
        return r

    def theorem_id(self, name):
        return self._api.theorem_id(name, call=self._call)

    def theorem_status(self, tid):
        """The platform's status of theorem `tid` ('Proved', 'Open', ...)."""
        r = self._call('GET', '/theorems/%s' % tid)
        return (r.get('theorem') or r).get('status') if isinstance(r, dict) else None

    def existing(self, kind, name):
        """The live statement or definitions bundle named exactly `name`: {id, author, preamble,
        formal_statement} or {id, author, definition}; None if there is none."""
        if kind == 'statement':
            r = self._call('GET', '/theorems?theorem_name=%s&limit=5' % name)
            hit = [x for x in (r.get('theorems') or []) if x.get('theorem_name') == name]
            if not hit:
                return None
            h = hit[0]
            return {'id': h.get('theorem_id') or h.get('id'), 'author': h.get('created_by_username'),
                    'preamble': h.get('preamble'), 'formal_statement': h.get('formal_statement')}
        hit = []
        # discover.md: `definition_name` is the exact filter; `q=` (the old lookup) is a search
        for q in ('definition_name=%s&limit=5' % name, 'q=%s&limit=20' % name):
            r = self._call('GET', '/definitions?' + q)
            hit = [x for x in (r.get('definitions') or []) if x.get('definition_name') == name]
            if hit:
                break
        if not hit:
            return None
        h = hit[0]
        return {'id': h.get('definition_id'), 'author': h.get('created_by_username'),
                'definition': h.get('definition')}

    def live_proofs(self, name):
        """The live proofs (accepted, sketch-accepted, pending) of the theorem named `name`, each
        {id, author, status, content} with its exact solution.lean."""
        tid = self.theorem_id(name)
        if not tid:
            return []
        out = []
        for r in self._api.live_proofs(tid, call=self._call):
            sid = r.get('submission_id') or r.get('id')
            out.append({'id': sid, 'status': r.get('status'),
                        'author': r.get('username') or r.get('created_by_username') or r.get('user'),
                        'content': self._api.submission_source(sid, call=self._call)})
        return out

    def disproved(self, names):
        """The theorems of `names` the platform lists as Disproved (p2mlib.importcheck)."""
        from .importcheck import disproved
        return disproved(names, call=self._call)

    def submit_definition(self, body):
        return self._ok(self._call('POST', '/submit-definition', body), 'submit-definition')['job_id']

    def submit_problems(self, problems):
        r = self._ok(self._call('POST', '/submit-problem', {'problems': problems}), 'submit-problem')
        return [j['job_id'] for j in r['jobs']]

    def job(self, jid):
        r = self._call('GET', '/publish-jobs/' + jid)
        return r if isinstance(r, dict) and not r.get('__error') else {'status': 'PENDING'}

    def verify(self, tid, path, explanation, also=None):
        return self._ok(self._post(tid, path, explanation, also=also), 'verify')['submission_id']

    def verdict(self, sid):
        r = self._call('GET', '/verify?submission_id=' + sid)
        return r if isinstance(r, dict) and not r.get('__error') else {'status': 'PENDING'}
