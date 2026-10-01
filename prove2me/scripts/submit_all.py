#!/usr/bin/env python3
"""Build and submit each of a mission's statements as it is published, once each, until all are done.

usage: submit_all.py MISSION_DIR --proposal ID --check MOD [--check MOD ...] [--hold NAME ...]
                     [--every SECONDS]

Loops: fetch_theorems.py --proposal ID (so published statements and siblings are in Theorems/),
then for every THEOREMS entry of MISSION_DIR/mission.py that is published and not yet in
MISSION_DIR/solutions/submitted.json: build_solutions.py, prune_solution.py --check,
submit_solution.py --go. A statement no check file proves (an external milestone, a reduction to
be written by hand) is recorded as `no-check` and skipped; --hold NAME builds but does not submit
(for a manual edge check). Prints one line per event; meant to run under a Monitor. Exits when
every statement has an entry.

--wait-all builds nothing until every statement is published: a solution built while a sibling it
uses is still unpublished keeps that sibling's proof inline (rewire.py only sees published names),
which is a missing graph edge. Use it whenever an early milestone's proof uses later ones (Moore's
Theorem 1.1 is milestone 1 and uses nearly everything). --build-only builds and prunes every
statement but submits none (entries `held`), so edge_overlap.py can run first; a later run without
it submits the held ones.

Generalised 2026-09-30 from the per-mission submit_all.py of CFP §6 and §7.
"""
import argparse, json, os, re, subprocess, sys, time

SK = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SK)
from prune_solution import _workspace  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mission_dir')
    ap.add_argument('--proposal', required=True)
    ap.add_argument('--check', dest='checks', action='append', required=True)
    ap.add_argument('--hold', nargs='*', default=[])
    ap.add_argument('--every', type=int, default=120)
    ap.add_argument('--wait-all', action='store_true')
    ap.add_argument('--build-only', action='store_true')
    a = ap.parse_intermixed_args()
    mdir = os.path.abspath(a.mission_dir)
    sys.path.insert(0, mdir)
    import mission  # noqa: E402
    ns, names = mission.NAMESPACE, [T['name'] for T in mission.THEOREMS]
    out = os.path.join(mdir, 'solutions')
    os.makedirs(out, exist_ok=True)
    state = os.path.join(out, 'submitted.json')
    done = json.load(open(state)) if os.path.exists(state) else {}
    thm = os.path.join(_workspace(), 'Theorems')
    checks = sum((['--check', c] for c in a.checks), [])
    held = set(a.hold) | (set(names) if a.build_only else set())
    last = None
    while True:
        subprocess.run([sys.executable, os.path.join(SK, 'fetch_theorems.py'), '--proposal', a.proposal],
                       capture_output=True)
        here = [n for n in names if os.path.exists(os.path.join(thm, 'Thm_%s_%s.lean' % (ns.replace('.', '_'), n)))]
        if a.wait_all and len(here) < len(names):
            if len(here) != last:
                print(time.strftime('%H:%M'), 'published %d of %d; waiting for all' % (len(here), len(names)),
                      flush=True)
                last = len(here)
            time.sleep(a.every)
            continue
        for n in here:
            if n in done and not (done[n] == 'held' and n not in held):
                continue
            p = subprocess.run([sys.executable, os.path.join(SK, 'build_solutions.py'), mdir] + checks + [n],
                               capture_output=True, text=True)
            st = (p.stdout.split() or ['ERROR'])[0]
            if st == 'NO-CHECK':
                done[n] = 'no-check'
            elif st not in ('OK', 'OK*'):
                done[n] = 'build-fail ' + st
            elif n in held:
                done[n] = 'held'
            else:
                f = os.path.join(out, 'Sol_%s.lean' % n)
                q = subprocess.run([sys.executable, os.path.join(SK, 'prune_solution.py'), f, '--check'],
                                   capture_output=True, text=True)
                if q.returncode:
                    done[n] = 'prune-fail'
                else:
                    r = subprocess.run([sys.executable, os.path.join(SK, 'submit_solution.py'), '%s.%s' % (ns, n),
                                        f, '--go'], capture_output=True, text=True)
                    o = r.stdout + r.stderr
                    v = re.search(r'verdict (\S+) (\S+)', o)
                    done[n] = '%s %s' % v.groups() if v else 'ERROR: ' + o.strip()[-300:]
            print(time.strftime('%H:%M'), n, '->', done[n], flush=True)
            json.dump(done, open(state, 'w'), indent=1)
        if all(n in done and not (done[n] == 'held' and n not in held) for n in names):
            break
        time.sleep(a.every)
    print('ALL DONE', flush=True)


if __name__ == '__main__':
    main()
