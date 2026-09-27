#!/usr/bin/env python3
"""Watch mission proposals until their status changes (e.g. `In review` -> approved).

usage: watch_proposal.py PROPOSAL_ID [...] [--every SECONDS]   (default 300)

Prints one line per proposal at start, then one line whenever a proposal's status (or its mission
id) changes, and exits once every proposal has changed at least once. Meant to run under a Monitor:
each printed line is an event. A failed request prints nothing and is retried next round.
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call  # noqa: E402


def state(pid):
    p = call('GET', '/mission-proposals/' + pid)
    p = p.get('proposal', p) if isinstance(p, dict) else {}
    return p.get('status'), p.get('mission_id')


def main():
    args = sys.argv[1:]
    every = 300
    if '--every' in args:
        i = args.index('--every'); every = int(args[i + 1]); del args[i:i + 2]
    last, changed = {}, set()
    while True:
        for pid in args:
            try:
                s = state(pid)
            except Exception:  # noqa: BLE001 -- transient API failure: retry next round
                continue
            if pid not in last:
                print(time.strftime('%H:%M'), pid[:8], 'status', s[0], 'mission', s[1], flush=True)
            elif s != last[pid]:
                print(time.strftime('%H:%M'), pid[:8], 'CHANGED', last[pid][0], '->', s[0], 'mission', s[1], flush=True)
                changed.add(pid)
            last[pid] = s
        if changed >= set(args):
            return
        time.sleep(every)


if __name__ == '__main__':
    main()
