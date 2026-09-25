#!/usr/bin/env python3
"""Where has a Submit got to? One line now, or a line per change until it settles.

usage: publish_status.py PROPOSAL_ID            -> one status line
       publish_status.py PROPOSAL_ID --watch    -> a line whenever it changes; exits when the
                                                   proposal leaves Draft, or a job fails

Submit is asynchronous: one publish job per draft item, compiled one after another. The proposal
stays `Draft` with `submitted_at: null` until the last job lands, so neither field means failure
while jobs are still running; the publish-jobs list is the real signal. A job list that has gone
quiet with items unpublished is the known stall: say so, and a re-click of Submit resumes it.

Replaces the per-mission copies (Wolf's publish_status.py; Garrido II's inline poller, which
crashed on a response that transiently lacked `items`): every field is read defensively and a
failed fetch is reported and retried, never fatal.
"""
import os, sys, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call


def snapshot(pid):
    p = call('GET', '/mission-proposals/' + pid)
    p = p.get('proposal', p) if isinstance(p, dict) else {}
    if '__error' in p:
        return None
    names = {it.get('theorem_name') or it.get('definition_name') for it in (p.get('items') or [])}
    j = call('GET', '/publish-jobs?limit=200')
    jobs = [x for x in ((j.get('publish_jobs') or j.get('jobs') or []) if isinstance(j, dict) else [])
            if (x.get('proposal_id') or x.get('mission_proposal_id')) == pid
            or x.get('theorem_name') in names]
    by = collections.Counter(x.get('status') for x in jobs)
    failed = [(x.get('theorem_name'), (x.get('error_message') or '')[:160])
              for x in jobs if str(x.get('status')).upper() in ('FAILED', 'ERROR')]
    return p.get('status'), p.get('submitted_at'), len(names), dict(sorted(by.items())), failed


def line(s):
    st, sub, n, by, failed = s
    return '%s  %s items=%d jobs=%s%s' % (time.strftime('%H:%M:%S'), st, n, by,
                                           ''.join('\n   FAILED %s: %s' % f for f in failed))


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    pid, watch = sys.argv[1], '--watch' in sys.argv[2:]
    last, quiet = None, 0
    while True:
        s = snapshot(pid)
        if s is None:
            print(time.strftime('%H:%M:%S'), 'fetch failed; retrying', flush=True)
        elif s != last:
            print(line(s), flush=True)
            last, quiet = s, 0
        else:
            quiet += 1
            if quiet == 20:      # ~10 minutes without movement
                print(time.strftime('%H:%M:%S'), 'no change for ~10 min: likely the publish stall;'
                      ' a re-click of Submit resumes it', flush=True)
        if not watch:
            return
        if s and (s[0] != 'Draft' or s[4]):
            return
        time.sleep(30)


if __name__ == '__main__':
    main()
