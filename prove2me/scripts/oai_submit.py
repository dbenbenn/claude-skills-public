#!/usr/bin/env python3
"""Submit single-file ports as they are, in order, each once its explanation exists.

usage: oai_submit.py --dir JOB_DIR [--workers 2] [--section ID] [TAG ...]
  (runs until every tag is finished; never run two queues on one JOB_DIR)

JOB_DIR (the oai_batch.py layout) adds:
  expl/<tag>.md        the proof's explanation (prove.md format); a goal without one waits
  queue_tags.txt       more tags, one per line, re-read on every pass (a running queue picks up
                       goals appended here)
  sub_<tag>.log        submit_solution.py output, one `=== time` section per attempt
  queue_state.json     {tag: {attempts, verdict, id, msg}}
At startup each goal's state is rebuilt from its log (p2mlib.oaiport.state_from_log), so a restart
neither repeats nor loses an attempt (as long as no orphaned submit_solution.py is still running).
A timeout gets one unchanged retry, except for a file over ~90 s local CPU (results/<tag>.json
`secs`), which gets one attempt: of six goals over 90 s, five timed out twice (2026-10-18).
Refusals (including an existing proof) and wrong answers are not retried."""
import concurrent.futures as cf
import json
import os
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, os.path.expanduser('~/.claude/skills/monitor'))
from p2mlib import oaiport as O  # noqa: E402

SUBMIT = os.path.join(HERE, 'submit_solution.py')
LOCK = threading.Lock()
MAX_ATTEMPTS = 2
RETRY_UNDER = 90       # local CPU secs: a file this slow or slower gets one attempt


class Queue:
    def __init__(self, d, sid='oai-goals-submit'):
        self.d, self.sid = d, sid
        self.state_path = os.path.join(d, 'queue_state.json')

    def load(self):
        return json.load(open(self.state_path)) if os.path.exists(self.state_path) else {}

    def save(self, st):
        tmp = self.state_path + '.tmp'
        json.dump(st, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.state_path)

    def max_attempts(self, tag):
        try:
            secs = json.load(open(os.path.join(self.d, 'results', tag + '.json'))).get('secs') or 0
        except OSError:
            return MAX_ATTEMPTS
        return MAX_ATTEMPTS if secs < RETRY_UNDER else 1

    def terminal(self, s, tag):
        return s.get('verdict') in ('ACCEPTED', 'REFUSED', 'REJECTED') or \
            s.get('attempts', 0) >= self.max_attempts(tag)

    def reconcile(self, tags):
        st = self.load()
        for t in tags:
            log = os.path.join(self.d, 'sub_%s.log' % t)
            if os.path.exists(log):
                s = O.state_from_log(open(log).read())
                if s:
                    st[t] = s
        self.save(st)

    def attempt(self, tag):
        res = json.load(open(os.path.join(self.d, 'results', tag + '.json')))
        name = res['target']
        sol = os.path.join(self.d, 'run', tag, 'Sol_' + name.replace('.', '_') + '.lean')
        log = os.path.join(self.d, 'sub_%s.log' % tag)
        with open(log, 'a') as f:
            f.write('\n=== %s\n' % time.strftime('%Y-%m-%d %H:%M:%S'))
            f.flush()
            subprocess.run([sys.executable, SUBMIT, name, sol, '--explanation',
                            os.path.join(self.d, 'expl', tag + '.md'), '--go'],
                           stdout=f, stderr=subprocess.STDOUT, cwd=HERE)
        return O.classify_attempt(open(log).read().split('\n=== ')[-1]) or ('REJECTED', None, 'no verdict in log')

    def step(self, tag, tags):
        v, sid, msg = self.attempt(tag)
        with LOCK:
            st = self.load()
            s = st.setdefault(tag, {'attempts': 0})
            s.update(attempts=s['attempts'] + 1, verdict=v, id=sid, msg=msg)
            self.save(st)
        print(tag, v, sid or '', msg[:120].replace('\n', ' '), flush=True)
        self.publish(tags)

    def publish(self, tags, state='running'):
        try:
            import section
        except ImportError:
            return
        st = self.load()
        acc = sum(1 for t in tags if st.get(t, {}).get('verdict') == 'ACCEPTED')
        fin = sum(1 for t in tags if self.terminal(st.get(t, {}), t))
        bad = [t for t in tags if st.get(t, {}).get('verdict') in ('REFUSED', 'REJECTED')]
        section.publish(self.sid, title='OpenAI goals: submitting single-file ports', state=state,
                        heartbeat_secs=900, alerts=['%s: %s' % (t, st[t]['verdict']) for t in bad],
                        phases=[{'name': 'Finished (accepted, refused, or out of retries)', 'done': fin, 'total': len(tags)},
                                {'name': 'Accepted on prove2.me', 'done': acc, 'total': len(tags)}],
                        processes=[{'label': 'submit queue', 'match': r'oai_submit\.py'}])

    def run(self, given, workers=2):
        def all_tags():
            f = os.path.join(self.d, 'queue_tags.txt')
            extra = [l.strip() for l in open(f) if l.strip()] if os.path.exists(f) else []
            return list(dict.fromkeys(given + extra))
        tags = all_tags()
        self.reconcile(tags)
        self.publish(tags)
        busy = {}
        with cf.ThreadPoolExecutor(workers) as ex:
            while True:
                for t in [t for t, f in busy.items() if f.done()]:
                    busy.pop(t).result()
                tags = all_tags()
                st = self.load()
                todo = [t for t in tags if not self.terminal(st.get(t, {}), t)]
                if not todo and not busy:
                    break
                for t in todo:
                    if len(busy) >= workers:
                        break
                    if t not in busy and os.path.exists(os.path.join(self.d, 'expl', t + '.md')):
                        busy[t] = ex.submit(self.step, t, tags)
                time.sleep(30)
        self.publish(tags, state='done')


def main(argv):
    if '--dir' not in argv:
        sys.exit(__doc__)
    d = os.path.abspath(argv[argv.index('--dir') + 1])
    workers = int(argv[argv.index('--workers') + 1]) if '--workers' in argv else 2
    sid = argv[argv.index('--section') + 1] if '--section' in argv else 'oai-goals-submit'
    skip = {argv.index(o) + 1 for o in ('--dir', '--workers', '--section') if o in argv}
    given = [a for i, a in enumerate(argv) if not a.startswith('--') and i not in skip]
    Queue(d, sid).run(given, workers)


if __name__ == '__main__':
    main(sys.argv[1:])
