#!/usr/bin/env python3
"""Wait until named statements or definitions are published, or until a proposal's queue drains.

usage: wait_published.py NAME [NAME ...] [--every SECONDS] [--timeout SECONDS]
       wait_published.py --proposal ID [--every SECONDS] [--timeout SECONDS]

NAME is the full name of a theorem (`NS.name`) or of a definitions bundle (`Bundle`). It counts as
published once `GET /theorems?theorem_name=NAME` returns it, which is the lookup publish_standalone.py
uses; the job listing is consulted only to notice a failure. With --proposal, the wait ends when every
item of the proposal has a `theorem_id` (the browser's Submit loop has published them all).

Prints one line per event (`published NAME id`, `FAILED NAME: message`) and `ALL PUBLISHED` at the end.
Exit 0 when everything is published, 1 when the newest publish job of a name has FAILED (it is not
retried here: the human re-clicks Submit, or publish_standalone.py is rerun), 2 on --timeout. Meant to
run as a background command, so its exit is the notification:

    wait_published.py --proposal ID && publish_standalone.py DIR

Replaces three ad-hoc waiters of 2026-10-05/06. One polled `/publish-jobs?limit=6` for its bundle's job;
when later jobs pushed that job out of the window, "not found" read as "not done" and it never exited
(dbenbenn: "Maybe that should be a shared, tested, debugged script rather than ad-hoc?").
"""
import argparse, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call  # noqa: E402

LIVE = ('PENDING', 'COMPILING')


def published_id(name):
    """The id of the theorem or bundle published under exactly `name`, or None."""
    r = call('GET', '/theorems?theorem_name=' + name)
    for t in (r.get('theorems') or []) if isinstance(r, dict) else []:
        if t.get('theorem_name') == name:
            return t.get('theorem_id') or t.get('id') or '?'
    return None


def failure(name):
    """The error of `name`'s newest publish job if that job FAILED and no newer one is queued, else None.
    An old failure followed by a resubmission that is still pending is not a failure."""
    jobs = []
    for st in ('FAILED',) + LIVE:
        r = call('GET', '/publish-jobs?status=%s&limit=200' % st)
        for j in (r.get('publish_jobs') or []) if isinstance(r, dict) else []:
            if name in (j.get('theorem_name'), j.get('definition_name')):
                jobs.append(j)
    if not jobs:
        return None
    newest = max(jobs, key=lambda j: j.get('created_at') or '')
    if newest.get('status') != 'FAILED':
        return None
    return newest.get('error_message') or 'FAILED (no message)'


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('names', nargs='*')
    ap.add_argument('--proposal')
    ap.add_argument('--every', type=float, default=60)
    ap.add_argument('--timeout', type=float, default=None)
    a = ap.parse_args(argv)
    if bool(a.names) == bool(a.proposal):
        sys.exit(__doc__)
    waited, pending = 0.0, list(a.names)
    while True:
        if a.proposal:
            d = call('GET', '/mission-proposals/' + a.proposal)
            d = d.get('proposal', d) if isinstance(d, dict) else {}
            items = d.get('items') or []
            left = [i for i in items if not i.get('theorem_id')]
            if items and not left:
                print(time.strftime('%H:%M'), 'ALL PUBLISHED', len(items), 'items', flush=True)
                sys.exit(0)
            pending = [i.get('theorem_name') or i.get('definition_name') for i in left]
        else:
            for name in list(pending):
                tid = published_id(name)
                if tid:
                    print(time.strftime('%H:%M'), 'published', name, tid, flush=True)
                    pending.remove(name)
            if not pending:
                print(time.strftime('%H:%M'), 'ALL PUBLISHED', flush=True)
                sys.exit(0)
        for name in pending:
            err = name and failure(name)
            if err:
                print(time.strftime('%H:%M'), 'FAILED', name + ':', err, flush=True)
                sys.exit(1)
        if a.timeout is not None and waited + a.every > a.timeout:
            print(time.strftime('%H:%M'), 'TIMEOUT; still unpublished:', ', '.join(map(str, pending)), flush=True)
            sys.exit(2)
        time.sleep(a.every)
        waited += a.every


if __name__ == '__main__':
    main()
