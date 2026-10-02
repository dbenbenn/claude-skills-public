#!/usr/bin/env python3
"""Audit graph edges against the proofs that produce them: one auditor, judged by Lean.

usage: edge_audit.py MISSION_ID_OR_PREFIX [...]      the live proofs of missions (from the platform)
       edge_audit.py --local SOLUTIONS_DIR           Sol_<name>.lean files, before submitting them

A proof's graph edges are exactly its `import Theorems.*` lines. Each proof is elaborated (LeanInfo,
cached by content; up to four at a time, fewer when memory is short) and judged on what Lean says its declarations use:

  INCORRECT  an import that nothing reachable from `solution` uses: an edge the proof does not
             have (the pruner's own criterion, p2mlib.prune; fix: prune_solution.py, then
             submit_solution.py --replaces the old proof);
  MISSING    a declaration reachable from `solution` that states a published theorem (by
             statement, p2mlib.copies: under any name) or is named after one (its short name,
             primes dropped), which the graph does not reach (fix: rewire.py, then resubmit). A
             copy of a deprecated theorem is deliberate: importing it would put a hidden node on
             the graph;
  SHARED     two proofs whose top steps (`solution` and what it uses directly) name a common
             declaration of their own while neither reaches the other's theorem: read them; when
             one passes through the other's statement, take that step from the published theorem.
             A shared basic lemma is fine (formerly edge_overlap.py: CFP §7's Theorem 7.2 was
             `mulEquivF.trans psiEquiv`, the published Δ₁ conjugation rebuilt inline);
  UNCHECKED  a proof whose source could not be fetched, or that does not elaborate here (fetch the
             mission's statements first: fetch_theorems.py).

Live proofs are read from `GET /submissions/:id/solution` (an earlier version said the platform
never serves code and paired local files by their imports; it does, since 0.6.3). What it still
cannot see: a lemma that is a *part* of a published statement (Moore's `reduced_unique`, half of an
`∃!`), and a definition rebuilt inline.

This is the 2026-09-24 sweep made reusable: it found 36 incorrect edges on 19 theorems and missing
ones on 11, across Chou, the three Cannon-Floyd-Parry missions and Brin-Squier.
"""
import os
import re
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2m import call  # noqa: E402
from p2mlib import copies, leaninfo, names, prune  # noqa: E402
from p2mlib.api import paginate, paginate_numbered  # noqa: E402
from p2mlib.workspace import workspace as _workspace, published_by_full  # noqa: E402

CACHE = os.path.expanduser('~/.cache/p2m/audit')
GB_PER_WORKER = 9      # a proof elaborated with its candidate statements imported peaks near 8.4 GB


def workers():
    """How many proofs to elaborate at once: at most 4, as many as MemAvailable allows."""
    try:
        kb = int(re.search(r'MemAvailable:\s+(\d+)', open('/proc/meminfo').read()).group(1))
    except (OSError, AttributeError):
        return 1
    return max(1, min(4, kb // (GB_PER_WORKER * 1024 * 1024)))


def analyze(path, ws):
    """(info, {decl: [published]}) for one proof; info.errors when it does not elaborate here."""
    info = leaninfo.run(path, ws=ws)
    if info.errors:
        return info, {}
    _, same = copies.find(path, ws)
    return info, same


def judge(info, same, target, reach, byfull, is_deprecated):
    """(incorrect imports, [(decl, published, how)] missing, top-step short names)."""
    drop, drop_imports, _ = prune.plan(info)
    kept = [d for d in info.decls if d.command not in drop and not d.generated]
    byshort = {}
    for full in byfull:
        byshort.setdefault(names.short(full), full)
    missing = []
    for d in kept:
        if d.name == 'solution' or d.kind != 'theorem':
            continue
        hits = [(h, 'statement') for h in same.get(d.name, [])]
        if not hits and names.base(d.name) in byshort:
            hits = [(byshort[names.base(d.name)], 'name')]
        for full, how in hits:
            if full != target and full not in reach and not is_deprecated(full):
                missing.append((d.name, full, how))
    sol = info.decl('solution')
    top = set(sol.uses_local) if sol else set()
    for n in list(top):
        d = info.decl(n)
        top |= set(d.uses_local) if d else set()
    return [m for m in drop_imports if m.startswith('Theorems.')], missing, {names.short(n) for n in top}


def report(proofs, results):
    """Print the four sections; the exit status is 1 when anything is INCORRECT or MISSING."""
    incorrect, missing, unchecked, tops = [], [], [], []
    for (thm, sid, reach), (info, res) in zip(proofs, results):
        if res is None:
            unchecked.append((thm, sid, info))
            continue
        inc, mis, top = res
        incorrect += [(thm, sid, m) for m in inc]
        missing += [(thm, sid) + m for m in mis]
        tops.append((thm, sid, reach, top))
    shared = []
    for i, (ta, sa, ra, xa) in enumerate(tops):
        for tb, sb, rb, xb in tops[i + 1:]:
            if ta == tb or tb in ra or ta in rb:
                continue
            common = sorted(n for n in xa & xb if n.rstrip("'") not in (names.short(ta), names.short(tb)))
            if common and (ta, tb, ', '.join(common)) not in shared:    # two live proofs of one theorem
                shared.append((ta, tb, ', '.join(common)))
    print('\nINCORRECT edges (imports the proof never uses): %d' % len(incorrect))
    for x in incorrect:
        print('   %s  [%s]  -> %s' % x)
    print('MISSING edges (a published theorem re-derived, not reached by the graph): %d' % len(missing))
    for x in missing:
        print('   %s  [%s]  %s <- %s  (by %s)' % x)
    print('SHARED top-proof steps between proofs that do not reach each other (read them): %d' % len(shared))
    for x in shared:
        print('   %s  and  %s:  %s' % x)
    print('UNCHECKED proofs: %d' % len(unchecked))
    for x in unchecked:
        print('   %s  [%s]  %s' % x)
    return 1 if incorrect or missing else 0


def run_all(jobs, ws, byfull, is_deprecated):
    """jobs: [(theorem, sid, reach, path or reason)] -> results for report()."""
    def one(job):
        thm, sid, reach, path = job
        if not os.path.exists(path):
            return path, None
        try:
            info, same = analyze(path, ws)
        except RuntimeError as e:
            return 'LeanInfo failed: %s' % str(e).splitlines()[0], None
        if info.errors:
            return 'does not elaborate: %s' % info.errors[0].text.splitlines()[0][:160], None
        return info, judge(info, same, thm, reach, byfull, is_deprecated)
    with ThreadPoolExecutor(workers()) as ex:
        return list(ex.map(one, jobs))


def local(d, ws):
    byfull = published_by_full(ws)
    byshort = {names.short(f): f for f in byfull}
    jobs = []
    for f in sorted(os.listdir(d)):
        m = re.fullmatch(r'Sol_(.+)\.lean', f)
        if m:
            path = os.path.join(d, f)
            imps = copies.imports_of(open(path, encoding='utf-8').read())
            reach = {p.full for p in byfull.values() if p.module in imps}
            jobs.append((byshort.get(m.group(1), m.group(1)), f, reach, path))
    results = run_all(jobs, ws, byfull, lambda full: False)
    return report([(t, s, r) for t, s, r, _ in jobs], results)


def live(prefixes, ws):
    byfull = published_by_full(ws)
    missions = [m for m in paginate('/missions', 'missions', call=call) if any(m['id'].startswith(a) for a in prefixes)]
    if not missions:
        sys.exit('no mission matches %s' % prefixes)
    thms = {}
    for m in missions:
        for t in paginate('/theorems?mission_id=%s' % m['id'], 'theorems', call=call):
            if t.get('status') != 'Definition':
                thms[t.get('id') or t.get('theorem_id')] = t
    print('%d theorems in %s' % (len(thms), ', '.join(m['name'][:40] for m in missions)))
    # GET /submissions ignores theorem_id: fetch the whole history once, 100 a page (0.11.5)
    subs = paginate_numbered('/submissions', 'submissions', call=call)
    _dep = {}

    def is_deprecated(full):
        if full not in _dep:
            r = [x for x in (call('GET', '/theorems?theorem_name=' + full).get('theorems') or [])
                 if x.get('theorem_name') == full]
            _dep[full] = bool(r and r[0].get('deprecated_at'))
        return _dep[full]
    os.makedirs(CACHE, exist_ok=True)
    jobs = []
    for tid, t in sorted(thms.items(), key=lambda kv: kv[1]['theorem_name']):
        live_ids = [s['id'] for s in subs if s.get('theorem_id') == tid and s.get('status') in ('ACCEPTED', 'SKETCH_ACCEPTED')
                    and not call('GET', '/submissions/' + s['id']).get('deprecated_at')]
        if not live_ids:
            continue
        g = call('GET', '/theorems/%s/graph' % tid)
        nm = {n.get('theorem_id'): n.get('theorem_name') for n in g['nodes'] if n.get('node_type') == 'theorem'}
        rev = {}
        for e in g['edges']:
            rev.setdefault(e['target'], []).append(e['source'])
        seen, stack = set(), [g['root_id']]
        while stack:
            for s in rev.get(stack.pop(), []):
                if s not in seen:
                    seen.add(s); stack.append(s)
        reach = {nm[s] for s in seen if s in nm}
        for sid in live_ids:
            r = call('GET', '/submissions/%s/solution' % sid)
            code = r.get('content') if isinstance(r, dict) else None
            path = os.path.join(CACHE, 'S%s.lean' % sid.replace('-', '_'))
            if code:
                if not os.path.exists(path) or open(path, encoding='utf-8').read() != code:
                    open(path, 'w', encoding='utf-8').write(code)
            else:
                path = 'source not served'
            jobs.append((t['theorem_name'], sid[:8], reach, path))
    results = run_all(jobs, ws, byfull, is_deprecated)
    return report([(t, s, r) for t, s, r, _ in jobs], results)


def main():
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    ws = _workspace()
    if args[0] == '--local':
        sys.exit(local(args[1], ws))
    sys.exit(live(args, ws))


if __name__ == '__main__':
    main()
