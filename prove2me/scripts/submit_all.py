#!/usr/bin/env python3
"""Build and submit each of a mission's statements as it is published, once each, until all are done.

usage: submit_all.py MISSION_DIR --proposal ID --check MOD [--check MOD ...] [--hold NAME ...]
                     [--every SECONDS]

Loops: fetch_theorems.py --proposal ID (so published statements and siblings are in Theorems/),
then for every THEOREMS entry of MISSION_DIR/mission.py that is published and not yet in
MISSION_DIR/solutions/submitted.json: build_solutions.py and prune_solution.py --check, one at a
time, and then every solution ready in that round is submitted at once (submit_solution.py --go;
--parallel N caps the batch, default 32). Serial submission cost about 13 minutes per verdict; six
Moore solutions submitted together all had verdicts within 15 minutes (2026-10-02).

A verdict other than ACCEPTED/SKETCH_ACCEPTED is retried, up to --retries (default 2), then
recorded as `FAILED ...` and printed with `!!`. Refusals a resubmission cannot change (DUPLICATE,
REFUSED, EDGES-DIFFER) are recorded without a retry. A verdict that is only late (`PENDING sid`)
is polled on later rounds, never resubmitted. The run ends by listing every entry that needs
attention, and exits 1 if there is one. A statement no check file proves (an external milestone, a reduction to
be written by hand) is recorded as `no-check` and skipped; --hold NAME builds but does not submit
(for a manual edge check). Prints one line per event; meant to run under a Monitor. Exits when
every statement has an entry.

--wait-all builds nothing until every statement is published: a solution built while a sibling it
uses is still unpublished keeps that sibling's proof inline (rewire.py only sees published names),
which is a missing graph edge. Use it whenever an early milestone's proof uses later ones (Moore's
Theorem 1.1 is milestone 1 and uses nearly everything). --build-only builds and prunes every
statement but submits none (entries `held`), so `edge_audit.py --local` can run first; a later run without
it submits the held ones exactly as they stand in solutions/ (not rebuilt), so fixes made by hand
after the audit survive.

Generalised 2026-09-30 from the per-mission submit_all.py of CFP §6 and §7.
"""
import argparse, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

SK = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SK)
from prune_solution import _workspace  # noqa: E402
from p2m import call  # noqa: E402


LIVE = ('ACCEPTED', 'SKETCH_ACCEPTED')
# refusals that a resubmission cannot change: record them, do not retry
FINAL = ('DUPLICATE', 'REFUSED', 'EDGES-DIFFER')


def submit(ns, n, f):
    """Submit one solution; return 'STATUS SID', 'PENDING SID', or a one-line failure."""
    r = subprocess.run([sys.executable, os.path.join(SK, 'submit_solution.py'), '%s.%s' % (ns, n), f, '--go'],
                       capture_output=True, text=True)
    o = r.stdout + r.stderr
    v = re.search(r'verdict (\S+) (\S+)', o)
    if 'EDGES DIFFER' in o and v:
        return 'EDGES-DIFFER %s %s' % v.groups()
    if v:
        return '%s %s' % v.groups()
    for key in ('DUPLICATE', 'REFUSED'):
        if key in o:
            return '%s: %s' % (key, o.strip().split(key, 1)[1][:200].strip())
    return 'ERROR: ' + ' '.join(o.strip().split())[-300:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mission_dir')
    ap.add_argument('--proposal', required=True)
    ap.add_argument('--check', dest='checks', action='append', required=True)
    ap.add_argument('--hold', nargs='*', default=[])
    ap.add_argument('--every', type=int, default=120)
    ap.add_argument('--wait-all', action='store_true')
    ap.add_argument('--build-only', action='store_true')
    ap.add_argument('--parallel', type=int, default=32)
    ap.add_argument('--retries', type=int, default=2)
    a = ap.parse_intermixed_args()
    mdir = os.path.abspath(a.mission_dir)
    sys.path.insert(0, mdir)
    from p2mlib.mission import load
    mission = load(mdir)
    ns, names = mission.NAMESPACE, [T['name'] for T in mission.THEOREMS]
    out = os.path.join(mdir, 'solutions')
    os.makedirs(out, exist_ok=True)
    state = os.path.join(out, 'submitted.json')
    done = json.load(open(state)) if os.path.exists(state) else {}
    tries_path = os.path.join(out, 'submit_tries.json')
    tries = json.load(open(tries_path)) if os.path.exists(tries_path) else {}
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
        # 1. builds, one at a time (local compiles); everything ready goes into one batch
        batch = []
        for n in here:
            v = done.get(n, '')
            if v.startswith('PENDING '):
                # a verdict that was only late: poll that submission, never resubmit it (a second
                # copy would duplicate the proof if the first is then accepted)
                sid = v.split()[1]
                st2 = (call('GET', '/submissions/' + sid) or {}).get('status')
                if st2 in LIVE:
                    done[n] = '%s %s' % (st2, sid)
                    print(time.strftime('%H:%M'), n, '->', done[n], flush=True)
                elif st2 and st2 != 'PENDING':
                    done[n] = 'retry %s %s' % (st2, sid)
                json.dump(done, open(state, 'w'), indent=1)
                continue
            if n in done and not (v == 'held' and n not in held) and not v.startswith('retry '):
                continue
            f = os.path.join(out, 'Sol_%s.lean' % n)
            # a held solution is submitted as built: the audit fixes made by hand between the
            # --build-only run and this one were being overwritten by a rebuild (Moore, 2026-10-02)
            if (v == 'held' or v.startswith('retry ')) and os.path.exists(f):
                st = 'OK'
            else:
                p = subprocess.run([sys.executable, os.path.join(SK, 'build_solutions.py'), mdir] + checks + [n],
                                   capture_output=True, text=True)
                st = (p.stdout.split() or ['ERROR'])[0]
            if st == 'NO-CHECK':
                done[n] = 'no-check'
            elif st not in ('OK', 'OK*'):
                done[n] = 'build-fail ' + st
            elif n in held:
                done[n] = 'held'
            elif subprocess.run([sys.executable, os.path.join(SK, 'prune_solution.py'), f, '--check'],
                                capture_output=True, text=True).returncode:
                done[n] = 'prune-fail'
            else:
                batch.append((n, f))
                continue
            print(time.strftime('%H:%M'), n, '->', done[n], flush=True)
            json.dump(done, open(state, 'w'), indent=1)
        # 2. the batch is submitted all at once: the server compiles submissions concurrently (six
        # Moore solutions all had verdicts within 15 minutes, against about 13 minutes each in
        # series, 2026-10-02; dbenbenn: "I don't think we ever really want to submit proofs in serial")
        if batch:
            print(time.strftime('%H:%M'), 'submitting %d in parallel: %s' % (len(batch), ' '.join(n for n, _ in batch)),
                  flush=True)
            with ThreadPoolExecutor(max_workers=a.parallel) as ex:
                for n, res in zip([n for n, _ in batch], ex.map(lambda nf: submit(ns, *nf), batch)):
                    tries[n] = tries.get(n, 0) + 1
                    if res.split()[0] in LIVE or res.startswith('PENDING ') or res.startswith(FINAL):
                        done[n] = res
                    elif tries[n] <= a.retries:
                        done[n] = 'retry ' + res          # rebuilt-free resubmission next round
                    else:
                        done[n] = 'FAILED %s (after %d tries)' % (res, tries[n])
                    flag = '!! ' if not (res.split()[0] in LIVE or res.startswith('PENDING ')) else ''
                    print(time.strftime('%H:%M'), flag + n, '->', done[n], flush=True)
            json.dump(done, open(state, 'w'), indent=1)
            json.dump(tries, open(tries_path, 'w'), indent=1)
        if any(done.get(n, '').startswith('retry ') for n in names):
            time.sleep(a.every)
            continue
        if all(n in done and not (done[n] == 'held' and n not in held) and not done[n].startswith('PENDING ')
               for n in names):
            break
        time.sleep(a.every)
    bad = [n for n in names if done.get(n, '').split(' ')[0].rstrip(':') in
           ('FAILED', 'EDGES-DIFFER', 'DUPLICATE', 'REFUSED', 'ERROR', 'build-fail', 'prune-fail')]
    for n in bad:
        print('!! %s: %s' % (n, done[n]), flush=True)
    print('ALL DONE' + (' -- %d need attention' % len(bad) if bad else ''), flush=True)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
