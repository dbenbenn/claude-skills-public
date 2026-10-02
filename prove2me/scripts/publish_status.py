#!/usr/bin/env python3
"""Where has a Submit got to? One line now, or a line per change until it settles.

usage: publish_status.py PROPOSAL_ID                -> one status line
       publish_status.py PROPOSAL_ID --watch        -> a line whenever it changes; exits when the
                                                       proposal leaves Draft, or a job fails
       publish_status.py PROPOSAL_ID --until-click  -> as --watch, and also exits with CLICK NEEDED
                                                       once no job has been pending for 4 minutes

Submit is asynchronous: one publish job per draft item, compiled one after another. The proposal
stays `Draft` with `submitted_at: null` until the last job lands, so neither field means failure
while jobs are still running; the publish-jobs list is the real signal. A job list that has gone
quiet with items unpublished is the known stall: say so, and a re-click of Submit resumes it.

Replaces the per-mission copies (Wolf's publish_status.py; Garrido II's inline poller, which
crashed on a response that transiently lacked `items`): every field is read defensively and a
failed fetch is reported and retried, never fatal.

--until-click is for a queue that needs the human between items (Lodha-Moore, 2026-10-02: each
published item waited for a re-click before the next job existed). A published item turns into a
reference, so its job drops out of the count: no PENDING or COMPILING job while the proposal is
still Draft means nothing is queued. A one-off watcher that read a `publish_status` field from the
items, which they do not carry, never fired.
"""
import os, sys, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call


def snapshot(pid):
    p = call('GET', '/mission-proposals/' + pid)
    p = p.get('proposal', p) if isinstance(p, dict) else {}
    if '__error' in p:
        return None
    # a reference item is already published and is never republished; its old publish job (the
    # F-amenability mission's goal and bundle, matched by name) made an unsubmitted Moore Draft
    # read as "PUBLISHED: 2" and then as a stall (2026-10-01)
    names = {it.get('theorem_name') or it.get('definition_name') for it in (p.get('items') or [])
             if it.get('kind') != 'reference'}
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


DONE = ('PUBLISHED', 'FAILED', 'ERROR')
IDLE_SECS = 240


def active(by):
    """Jobs still queued or compiling, from snapshot's {status: count}."""
    return sum(n for st, n in by.items() if str(st).upper() not in DONE)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    pid, until_click = sys.argv[1], '--until-click' in sys.argv[2:]
    watch = until_click or '--watch' in sys.argv[2:]
    last, quiet, idle_since = None, 0, None
    while True:
        s = snapshot(pid)
        if s is None:
            print(time.strftime('%H:%M:%S'), 'fetch failed; retrying', flush=True)
        elif s != last:
            print(line(s), flush=True)
            last, quiet = s, 0
        else:
            quiet += 1
            if quiet == 20 and last and last[3] and not until_click:   # ~10 min without movement
                print(time.strftime('%H:%M:%S'), 'no change for ~10 min: likely the publish stall;'
                      ' a re-click of Submit resumes it', flush=True)
        if until_click and s:
            idle = s[0] == 'Draft' and s[2] and not active(s[3])
            idle_since = (idle_since if idle_since is not None else time.time()) if idle else None
            if idle and time.time() - idle_since >= IDLE_SECS:
                print(time.strftime('%H:%M:%S'), 'CLICK NEEDED: %d items unpublished and no job for'
                      ' %d min; a re-click of Submit queues the next' % (s[2], IDLE_SECS // 60), flush=True)
                return
        if not watch:
            return
        if s and (s[0] != 'Draft' or s[4]):
            return
        time.sleep(30)


if __name__ == '__main__':
    main()
