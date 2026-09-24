#!/usr/bin/env python3
"""Audit a mission's live dependency graph against the proofs that produced it.

usage: edge_audit.py MISSION_ID_OR_PREFIX [...] [--files DIR ...]
       (default search roots: ~/claude and the workspace's Solutions/)

For every theorem of the missions, every live (accepted, not deprecated) submission is paired with
a local solution file -- the platform never serves submitted code -- by its `theorem solution`
statement and its `import Theorems.*` set, which must equal the sketch's live edges. Then:

  INCORRECT  an import the pruned proof never names: an edge the proof does not have
             (fix: prune_solution.py, then submit_solution.py --replaces the old sketch);
  MISSING    a declaration that copies a published theorem (its name, primes dropped, is that
             theorem's short name) which the theorem's live graph does not reach at all
             (fix: rewire.py, then submit_solution.py);
  UNMATCHED  a live proof with no local file, which cannot be checked.

Several local files can match one live proof (a test file and its clean successor with the same
imports); each flag names the file it came from, so check that it is the one submitted.

A copy the graph already reaches through another edge is an alternative route, not a missing
edge, and is not reported; nor is a self-contained full proof kept beside a sketch that has the
edges. Copies renamed to something unrelated are not detected.

This is the 2026-09-24 sweep made reusable: it found 36 incorrect edges on 19 theorems and missing
ones on 11, across Chou, the three Cannon-Floyd-Parry missions and Brin-Squier.
"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from p2m import call
from prune_solution import parse, prune, _workspace
from stage_auditor import strip
from rewire import published


def sig(text, name):
    m = re.search(r'(?:theorem|lemma)\s+%s(?![\w\'])(.*?):=' % re.escape(name), strip(text), re.S)
    if not m:
        return None
    s = re.sub(r'Type\s+\w+\b', 'Type*', m.group(1))
    s = re.sub(r'\b(?:[A-Z]\w*\.)+(?=[a-zA-Z])', '', s)
    return ' '.join(re.sub(r'[\[\]()]', ' ', s).split())


def paged(path, key):
    out, off = [], 0
    while True:
        r = call('GET', '%s%slimit=100&offset=%d' % (path, '&' if '?' in path else '?', off))
        b = r.get(key) or []
        out += b
        if len(b) < 100:
            return out
        off += 100


def main():
    args = sys.argv[1:]
    roots = []
    if '--files' in args:
        i = args.index('--files'); roots = args[i + 1:]; args = args[:i]
    if not args:
        sys.exit(__doc__)
    ws = _workspace()
    roots = roots or [os.path.expanduser('~/claude'), os.path.join(ws, 'Solutions')]
    pub = published(ws)
    full_of = {v[0].split('.')[-1]: v[0] for v in pub.values()}

    missions = [m for m in paged('/missions', 'missions') if any(m['id'].startswith(a) for a in args)]
    if not missions:
        sys.exit('no mission matches %s' % args)
    thms = {}
    for m in missions:
        for t in paged('/theorems?mission_id=%s' % m['id'], 'theorems'):
            if t.get('status') != 'Definition':
                thms[t.get('id') or t.get('theorem_id')] = t
    print('%d theorems in %s' % (len(thms), ', '.join(m['name'][:40] for m in missions)))

    # GET /submissions ignores theorem_id and returns the whole history: fetch once, filter here
    subs = call('GET', '/submissions?limit=100000').get('submissions') or []
    files = [f for r in roots for f in glob.glob(os.path.join(r, '**', '*.lean'), recursive=True)
             if '/.lake/' not in f]
    solsig, imps = {}, {}
    for f in files:
        try:
            t = open(f, encoding='utf-8').read()
        except Exception:
            continue
        if 'theorem solution' not in t:
            continue
        solsig[f] = sig(t, 'solution')
        names = set()
        for mod in re.findall(r'^import (Theorems\.\S+)', t, re.M):
            p = os.path.join(ws, mod.replace('.', '/') + '.lean')
            if os.path.exists(p):
                tt = open(p, encoding='utf-8').read()
                ns = re.search(r'^namespace (\S+)', tt, re.M)
                mm = re.search(r'^\s*theorem\s+(\S+)', tt, re.M)
                if mm:
                    names.add((ns.group(1) + '.' if ns else '') + mm.group(1))
        imps[f] = names

    incorrect, missing, unmatched = [], [], []
    for tid, t in sorted(thms.items(), key=lambda kv: kv[1]['theorem_name']):
        live = []
        for s in subs:
            if s.get('theorem_id') == tid and s.get('status') in ('ACCEPTED', 'SKETCH_ACCEPTED'):
                if not call('GET', '/submissions/' + s['id']).get('deprecated_at'):
                    live.append(s['id'])
        if not live:
            continue
        g = call('GET', '/theorems/%s/graph' % tid)
        names = {n.get('theorem_id'): n.get('theorem_name') for n in g['nodes'] if n.get('node_type') == 'theorem'}
        rev = {}
        for e in g['edges']:
            rev.setdefault(e['target'], []).append(e['source'])
        seen, stack = set(), [g['root_id']]
        while stack:
            for s in rev.get(stack.pop(), []):
                if s not in seen:
                    seen.add(s); stack.append(s)
        reach = {names[s] for s in seen if s in names}
        tsig = sig(t.get('formal_statement') or '', t['theorem_name'].split('.')[-1])
        short = t['theorem_name'].split('.')[-1]
        for sid in live:
            edges = {names[e] for e in rev.get('sketch-' + sid, []) if '.' in (names.get(e) or '')}
            cands = [f for f in solsig if tsig and solsig[f] == tsig and imps[f] == edges]
            if not cands:
                unmatched.append((t['theorem_name'], sid[:8], sorted(edges))); continue
            for f in cands[:3]:
                text = open(f, encoding='utf-8').read()
                pruned, doomed = prune(text, verbose=False)
                for n, k, *_ in doomed:
                    if k == 'import':
                        incorrect.append((t['theorem_name'], sid[:8], n, os.path.relpath(f)))
                live_decls = {d[0] for d in parse(pruned.split('\n'))}
                for d in parse(text.split('\n')):
                    base = d[0].split('.')[-1].rstrip("'")
                    if d[0] in live_decls and d[0] != 'solution' and base != short and base in full_of \
                            and full_of[base] not in reach:
                        missing.append((t['theorem_name'], sid[:8], full_of[base], os.path.relpath(f)))
    dedup = lambda xs: sorted(set(xs))
    print('\nINCORRECT edges (imports the proof never uses): %d' % len(dedup(x[:3] for x in incorrect)))
    for x in dedup(incorrect):
        print('   %s  [%s]  -> %s   (%s)' % x)
    print('MISSING edges (copied published theorem the graph does not reach): %d'
          % len(dedup(x[:3] for x in missing)))
    for x in dedup(missing):
        print('   %s  [%s]  <- %s   (%s)' % x)
    print('UNMATCHED live proofs (no local file; not checked): %d' % len(unmatched))
    for x in unmatched:
        print('   %s  [%s]  edges %s' % x)
    sys.exit(1 if incorrect or missing else 0)


if __name__ == '__main__':
    main()
