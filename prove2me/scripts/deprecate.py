#!/usr/bin/env python3
"""Deprecate superseded submissions, naming the one that keeps the theorem proved.

usage: deprecate.py --keep KEEP_SID OLD_SID [OLD_SID ...] [--go]      (dry run without --go)

Use it after a replacement proof is accepted: a pruned proof that drops a false edge, a rewired
one that imports what it used to re-derive. Deprecation hides a submission's sketch node from
the graph, so a stale sketch's edges disappear with it (PATCH /submissions/:id is reversible).

Why `--keep` is required rather than inferred. The mission scripts this replaces chose the
submission to keep as "the newest ACCEPTED row" of GET /submissions -- but that list never reports
`deprecated_at` (only GET /submissions/:id does). When the newest row had itself been deprecated
earlier, they kept a proof that no longer counted and deprecated every live one, and the theorem
stopped being Proved; the status check ran after the damage. Here the caller names what stays, and
each id, the kept one included, is checked against the detail endpoint first:

  * KEEP_SID must be ACCEPTED or SKETCH_ACCEPTED, not deprecated, and on the same theorem as every
    OLD_SID; an OLD_SID already deprecated is skipped, never re-patched;
  * after each deprecation the theorem must still be Proved -- if not, that deprecation is undone
    and the run stops.
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call

LIVE = ('ACCEPTED', 'SKETCH_ACCEPTED')


def detail(sid):
    d = call('GET', '/submissions/' + sid)
    if '__error' in d:
        sys.exit('cannot read submission %s: %s' % (sid, d['__error']))
    return d


def status(tid):
    t = call('GET', '/theorems/' + tid)
    return t.get('theorem', t).get('status')


def main():
    args, go = sys.argv[1:], '--go' in sys.argv[1:]
    args = [a for a in args if a != '--go']
    if len(args) < 3 or args[0] != '--keep' or any(a.startswith('--') for a in args[2:]):
        sys.exit(__doc__)
    keep, olds = args[1], args[2:]
    if keep in olds:
        sys.exit('refusing: %s is both kept and deprecated' % keep)
    k = detail(keep)
    if k.get('status') not in LIVE or k.get('deprecated_at'):
        sys.exit('refusing: kept submission %s is %s%s' % (keep, k.get('status'),
                 ', deprecated' if k.get('deprecated_at') else ''))
    tid = k['theorem_id']
    plan = []
    for sid in olds:
        d = detail(sid)
        if d['theorem_id'] != tid:
            sys.exit('refusing: %s is on %s, not %s' % (sid, d.get('theorem_name'), k.get('theorem_name')))
        if d.get('deprecated_at'):
            print('skip   %s  already deprecated' % sid)
            continue
        plan.append(d)
    print('%s  keep %s (%s)' % (k.get('theorem_name'), keep, k['status']))
    for d in plan:
        print('   deprecate %s (%s, %s)' % (d['id'], d['status'], d['created_at'][:19]))
    if not go:
        print('dry run -- pass --go to apply')
        return
    for d in plan:
        r = call('PATCH', '/submissions/' + d['id'], {'deprecated': True})
        if isinstance(r, dict) and '__error' in r:
            sys.exit('FAILED to deprecate %s: %s' % (d['id'], r['__error']))
        time.sleep(0.5)
        st = status(tid)
        if st != 'Proved':
            call('PATCH', '/submissions/' + d['id'], {'deprecated': False})
            sys.exit('STOPPED: theorem became %s after deprecating %s; undone' % (st, d['id']))
        print('deprecated %s   theorem still Proved' % d['id'])


if __name__ == '__main__':
    main()
