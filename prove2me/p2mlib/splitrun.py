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
never re-posted, in-flight jobs and submissions are polled again, and a bundle or statement that is
already on the platform under its name is adopted. Terminal states (`split`, `stop`, `give_up`,
`raise_heartbeats`) wait for a person; `reset(item)` clears one.

The platform is an object with `theorem_id(name)`, `submit_definition(body) -> job`,
`submit_problems([problem]) -> [job]`, `job(id) -> record`, `verify(theorem_id, path, explanation)
-> submission`, `verdict(submission) -> record`; `LiveApi` is the real one, tests pass a fake.
Erdős 3 v1 (2026-10-08..16) is why: per-mission loops retried one piece 740 times and re-carved
published bundles."""
import json
import os
import time

from . import carve as C
from . import explanation as E
from . import verdicts as V
from .mission import front_matter

FINAL_JOB = {'PUBLISHED', 'FAILED', 'ERROR'}
TERMINAL = {'split', 'stop', 'give_up', 'raise_heartbeats'}
BATCH = 10


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
        return {'kind': kind, 'name': name, 'file': os.path.join(out, 'solutions', 'Sol_%s.lean' % s),
                'text': os.path.join(self.cfg['explanations'], '%s.md' % s), 'node': n}

    def check(self, item):
        """None if the item's files are ready to send, else why not."""
        f = self.info(item)
        for p in (f['file'], f['text']):
            if not os.path.exists(p):
                return 'missing ' + p
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
            if s != 'todo' or x.split(':', 1)[0] not in self.kinds or \
                    not all(self.live(d) for d in self.deps[x]):
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
                st.update(state='stop', last=str(e)[:500])
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
            tid = self.api.theorem_id(f['name'])
            if tid:                                  # on the platform already: adopt it
                st.update(state='live', id=tid)
                self.log(x, 'adopt', tid)
                self.save()
                return
        if f['kind'] == 'bundle':
            title, body, source = self.prose(x)
            job = self.api.submit_definition({
                'definition_name': f['name'], 'definition_title': title,
                'definition': open(f['file'], encoding='utf-8').read(),
                'natural_language_statement': body, 'source': source,
                'tags': self.cfg.get('tags', [])})
            st.update(state='inflight', job=job)
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
            sid = self.api.verify(tid, f['file'], open(f['text'], encoding='utf-8').read())
            st.update(state='inflight', sid=sid)
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
            self.st(x).update(state='inflight', job=job)
            self.log(x, 'submit-problem', 'job %s' % job)
        self.save()

    def step(self):
        """Poll what is in flight, then send what is ready. True while there is anything to wait for."""
        self.poll()
        sent = self.submit(self.ready())
        return bool(self.inflight() or sent)

    def run(self, max_hours=None):
        t0 = time.time()
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

    def dry_run(self):
        """What a run would send first, and what is blocked, without touching the platform."""
        return {'ready': self.ready(), 'blocked': dict(self.blocked),
                'items': len(self.items), 'live': sum(self.live(x) for x in self.items)}


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

    def submit_definition(self, body):
        return self._ok(self._call('POST', '/submit-definition', body), 'submit-definition')['job_id']

    def submit_problems(self, problems):
        r = self._ok(self._call('POST', '/submit-problem', {'problems': problems}), 'submit-problem')
        return [j['job_id'] for j in r['jobs']]

    def job(self, jid):
        r = self._call('GET', '/publish-jobs/' + jid)
        return r if isinstance(r, dict) and not r.get('__error') else {'status': 'PENDING'}

    def verify(self, tid, path, explanation):
        return self._ok(self._post(tid, path, explanation), 'verify')['submission_id']

    def verdict(self, sid):
        r = self._call('GET', '/verify?submission_id=' + sid)
        return r if isinstance(r, dict) and not r.get('__error') else {'status': 'PENDING'}
