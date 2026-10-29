"""Publish a carved split (`carve.py plan` + `gen`) in waves, and keep publishing until done or stuck.

Items come from `carve.publish_order`: `bundle:NAME` (POST /submit-definition), `statement:NODE`
(POST /submit-problem, in batches) and `piece:NODE` (POST /verify). An item goes once everything it
imports is live. Every result goes through `verdicts.classify` / `decide`: transients retry
unchanged, own timeouts split after two, WA/CE stop for a person, and a stopped item holds back
only what depends on it.

Text: `prose/<NAME>.md` for a bundle, `prose/<slug(statement name)>.md` for a statement (front
matter `title:`, optional `source:`), `explanations/<slug>.md` for a piece (checked by
`explanation.problems`). An item whose files are missing or fail a check is blocked, never posted.

State (`state` file, written after every post and result) makes a run resumable: live items are
never re-posted, in-flight jobs and submissions are polled again. Every run starts with
`reconcile`: each bundle and statement already on the platform under its name is adopted when its
text is the one we generated (prose not needed), and one with other text stops the whole run
before anything is posted (LiveMismatch), which is what makes extending a published carve safe;
a piece whose exact source is a live proof of its statement is adopted too. Terminal states (`split`, `stop`, `give_up`,
`raise_heartbeats`) wait for a person; `reset(item)` clears one.

The platform is an object with `theorem_id(name)`, `existing(kind, name)` (the live statement or
bundle under that name: adopted only when its text is ours, whitespace aside, else the item stops
as "name taken"), `submit_definition(body) -> job`,
`submit_problems([problem]) -> [job]`, `job(id) -> record`, `verify(theorem_id, path, explanation)
-> submission`, `verdict(submission) -> record`; `LiveApi` is the real one, tests pass a fake.
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
BATCH = 10


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
    def __init__(self, cfg, api, sleep=time.sleep, poll_every=20):
        self.cfg, self.api, self.sleep, self.poll_every = cfg, api, sleep, poll_every
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
        edited run_state.json by hand). States from before `sha` was recorded are left alone."""
        for x, st in list(self.state.items()):
            if x in self.items and st.get('state') in TERMINAL and st.get('sha') and st['sha'] != self.file_sha(x):
                was = st['state']
                self.state.pop(x)
                self.log(x, 'restart', 'text changed since it stopped (%s): sending it again' % was)

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
        bad = guard_problems(open(f['file'], encoding='utf-8').read())
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
        tmp = self.cfg['state'] + '.tmp'
        json.dump(self.state, open(tmp, 'w'), indent=1, sort_keys=True)
        os.replace(tmp, self.cfg['state'])

    def log(self, item, action, what):
        name = self.info(item)['name']
        with open(self.cfg['log'], 'a', encoding='utf-8') as f:
            f.write('%s  %s  %s  %s\n' % (time.strftime('%Y-%m-%d %H:%M'), name, action, what))

    def live(self, item):
        return self.state.get(item, {}).get('state') == 'live'

    def ready(self):
        self.blocked = {}
        out = []
        for x in self.items:
            s = self.state.get(x, {}).get('state', 'todo')
            if s != 'todo' or x.split(':', 1)[0] not in self.kinds:
                continue
            stopped = [d for d in self.deps[x] if self.state.get(d, {}).get('state') in TERMINAL]
            if stopped:
                self.blocked[x] = 'waits on stopped ' + ', '.join(stopped)
                continue
            if not all(self.live(d) for d in self.deps[x]):
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

    def unsendable(self):
        """{item: why} for every item still to send (any wave, not only the ready ones) whose files are
        missing or fail a check: what a live run would block on (oaiq-047: 12 forced statements had no
        prose; the dry run, which checked only what it would send at once, was clean)."""
        out = {}
        for x in self.items:
            if self.state.get(x, {}).get('state', 'todo') != 'todo' or x.split(':', 1)[0] not in self.kinds:
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
        for x in self.items:
            kind = x.split(':', 1)[0]
            if self.state.get(x, {}).get('state') in ('live', 'inflight'):
                continue
            f = self.info(x)
            if not os.path.exists(f['file']):
                continue
            if kind == 'piece':
                # our exact source already live is adopted; someone else's live proof is reported
                # (a run's post_verify refuses the item then, for a person to compare)
                if proofs is None:
                    continue
                text = _ws(open(f['file'], encoding='utf-8').read())
                rows = proofs(f['name'])
                mine = [r for r in rows if _ws(r.get('content')) == text]
                if mine:
                    adopted[x] = mine[0]['id']
                elif rows:
                    self.proved_elsewhere[x] = ['%s (%s, %s)' % (r.get('id'), r.get('status'), r.get('author') or '?')
                                                for r in rows]
                continue
            rec = self.api.existing(kind, f['name'])
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
        dec = V.decide(kind, st['history'])
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
            why = {'split': 'NEEDS A PERSON: own compile timeout %d times; consider splitting' % (
                       st['history'].get('own_timeout', 0)),
                   'stop': 'NEEDS A PERSON: %s' % kind, 'give_up': 'NEEDS A PERSON: transient cap reached',
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
        return True

    def poll(self):
        for x in self.items:
            st = self.state.get(x)
            if not st or st['state'] != 'inflight':
                continue
            if 'job' in st:
                rec = self.api.job(st['job'])
                if rec.get('status') in FINAL_JOB:
                    self._result(x, rec, 'publish')
            else:
                rec = self.api.verdict(st['sid'])
                if rec.get('status') and rec.get('status') != 'PENDING':
                    rec.setdefault('submission_id', st['sid'])
                    self._result(x, rec, 'verdict')

    def inflight(self):
        return sum(1 for s in self.state.values() if s.get('state') == 'inflight')

    def submit(self, items):
        room = self.cfg.get('jobs', 8) - self.inflight()
        if self.max_items is not None:
            room = min(room, self.max_items - self.sent)
        items = items[:max(room, 0)]
        self.sent += len(items)
        stmts = []
        for x in items:
            try:
                self._submit_one(x, stmts)
            except Exception as e:                       # a refused post: this item waits for a person
                st = self.st(x)
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
            rec = self.api.existing(f['kind'], f['name'])
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
            st.update(state='inflight', job=job, sha=self.file_sha(x))
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
            if also.startswith('Same as'):
                st.update(state='stop', last='settled: ' + also.split('\n')[0][:300], sha=self.file_sha(x))
                self.log(x, 'settled', also.split('\n')[0][:200])
                self.save()
                return
            expl = open(f['text'], encoding='utf-8').read()
            sid = self.api.verify(tid, f['file'], expl, also=also) if also else self.api.verify(tid, f['file'], expl)
            st.update(state='inflight', sid=sid, sha=self.file_sha(x))
            self.log(x, 'submit piece (try %d)' % (sum(st['history'].values()) + 1), sid)
            self.save()

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
            self.st(x).update(state='inflight', job=job, sha=self.file_sha(x))
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
        while self.step():
            if max_hours and time.time() - t0 > max_hours * 3600:
                break
            if self.inflight():
                self.sleep(self.poll_every)
        return self.summary()

    def summary(self):
        states = [self.state.get(x, {}).get('state', 'todo') for x in self.items]
        self.ready()
        return {'live': states.count('live'), 'inflight': states.count('inflight'),
                'todo': states.count('todo'),
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
    READS = ('theorem_id', 'existing', 'live_proofs')

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
