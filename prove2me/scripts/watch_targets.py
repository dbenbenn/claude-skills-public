#!/usr/bin/env python3
"""Watch published theorems you are about to prove, or are proving, and report status changes.

    watch_targets.py check  ID [ID ...]        one line per target, then exit
    watch_targets.py watch  ID [ID ...]        poll every 60s; emit a line when a target's status
                                               changes; exit when none is Open any more

Why: another contributor can close an Open statement while your prover is running. That happened on
the Chou mission (`hall_finite_subgroups_of_index`, closed by another user seven minutes before the
proof landed), and the wasted work is avoidable for the price of one API call before you start.

`check` is the launch-time guard: run it in the same breath as dispatching a proof.
`watch` is for a long proof: run it under a Monitor so a status flip reaches you as an event, then
decide whether to stop the prover. It deliberately does not kill anything.
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call


def status(tid):
    r = call('GET', '/theorems/' + tid)
    if isinstance(r, dict) and '__error' in r:
        return None, None
    return r.get('status'), (r.get('theorem_name') or tid)


def main():
    if len(sys.argv) < 3 or sys.argv[1] not in ('check', 'watch'):
        sys.exit(__doc__)
    mode, ids = sys.argv[1], sys.argv[2:]
    seen = {}
    for tid in ids:
        st, name = status(tid)
        seen[tid] = st
        print(f'{st or "FETCH FAILED":10s} {name or tid}', flush=True)
    # an unreadable target is not a clear one: `check` must not green-light it, and `watch`
    # must not report "none Open" because it never learned the status
    if any(st is None for st in seen.values()):
        print('FETCH FAILED for at least one target -- status unknown')
        sys.exit(2)
    if mode == 'check':
        if any(st == 'Proved' for st in seen.values()):
            print('ALREADY PROVED — do not spend a proof on it')
            sys.exit(1)
        return
    while any(st == 'Open' for st in seen.values()):
        time.sleep(60)
        for tid in ids:
            st, name = status(tid)
            if st is None:
                print(f'FETCH FAILED {tid} (will retry)', flush=True)
            elif st != seen[tid]:
                print(f'CHANGED {seen[tid]} -> {st}  {name}', flush=True)
                seen[tid] = st
    print('DONE none Open')

if __name__ == '__main__':
    main()
