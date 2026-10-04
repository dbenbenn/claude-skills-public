#!/usr/bin/env python3
"""Submit a solution, check the graph shows exactly its imports, then retire what it replaces.

usage: submit_solution.py THEOREM FILE --explanation FILE.md [--allow-copy NAME ...] [--differs NOTE.md]
                           [--replaces SID ...] [--go]
       (dry run without --go; THEOREM is a full name like Chou.hasPackingProperty_of_finite,
        or a theorem id; --go refuses without an explanation that passes p2mlib.explanation,
        unless --no-explanation is given)

The last step of rewire.py and of any prune that drops a false edge, done the same way every
time instead of by a per-mission submit script:

  0. read the theorem's live proofs (`blocking`): refuse the same Lean source (DUPLICATE), and
     refuse a proof that adds no graph edge to one that already proves the theorem
     (ALREADY-PROVED). That refusal saves each such proof, Lean and explanation, under
     others/ beside FILE: deciding whether ours is meaningfully different means reading it.
     The comparison is then written down; one that begins "Different from <id>:" (other
     mathematics, or edges correct where its are false) is passed as --differs NOTE.md;
  1. POST /verify and poll (submit_verify.post_verify / poll); stop unless ACCEPTED or
     SKETCH_ACCEPTED;
  2. read the theorem's graph and require the new sketch's theorem edges to equal the file's
     `import Theorems.*` lines -- the check that would have caught every false edge the
     2026-09-24 audit found, had it run at submission time;
  3. deprecate each --replaces submission through deprecate.py's checks (kept = the new one,
     same theorem, detail endpoint, undo if the theorem stops being Proved).

Exit status is 0 only if all three held.
"""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from p2m import call
from prune_solution import _workspace
from p2mlib import explanation


def theorem_id(name):
    if re.fullmatch(r'[0-9a-f-]{36}', name):
        return name
    r = call('GET', '/theorems?theorem_name=%s&limit=5' % name)
    hit = [t for t in (r.get('theorems') or []) if t.get('theorem_name') == name]
    if not hit:
        sys.exit('no published theorem named %s' % name)
    return hit[0].get('id') or hit[0].get('theorem_id')


def import_names(path):
    """The theorem each `import Theorems.Thm_<X>` line brings in. The declaration is the one
    whose name, dots read as underscores, is `<X>`: a first-match regex once read a module
    docstring line beginning "theorem for balls" as the theorem `for`, and missed `lemma`s."""
    ws = _workspace()
    out = set()
    for mod in re.findall(r'^import (Theorems\.\S+)', open(path, encoding='utf-8').read(), re.M):
        t = open(os.path.join(ws, mod.replace('.', '/') + '.lean'), encoding='utf-8').read()
        ns = re.search(r'^namespace (\S+)', t, re.M)
        want = mod.split('.', 1)[1][len('Thm_'):]
        cands = [(ns.group(1) + '.' if ns else '') + n
                 for n in re.findall(r'^\s*(?:private\s+)?(?:theorem|lemma)\s+(\S+)', t, re.M)]
        hit = [c for c in cands if c.replace('.', '_') == want or c.split('.')[-1] == want]
        if not hit:
            sys.exit('cannot find the theorem of %s' % mod)
        out.add(hit[0])
    return out


def sketch_edges(tid, sid):
    g = call('GET', '/theorems/%s/graph' % tid)
    names = {n.get('theorem_id'): n.get('theorem_name') for n in g['nodes'] if n.get('node_type') == 'theorem'}
    node = 'sketch-' + sid
    present = any(e['source'] == node or e['target'] == node for e in g['edges'])
    return present, {names[e['source']] for e in g['edges']
                     if e['target'] == node and '.' in (names.get(e['source']) or '')}


def live_proofs(tid, replaces=()):
    """The theorem's live accepted proofs: dicts with id, status, username, edges (the theorems its
    graph sketch points from; empty for a full proof) and content (its Lean source). Listed from
    /submissions, not from the graph: the graph has a sketch node only for a proof with theorem
    edges, so two full proofs of one theorem were never compared (Lodha-Moore, 2026-10-04)."""
    subs = call('GET', '/theorems/%s/submissions?status=ACCEPTED,SKETCH_ACCEPTED&limit=200' % tid)
    g = call('GET', '/theorems/%s/graph' % tid)
    names = {n.get('theorem_id'): n.get('theorem_name') for n in g['nodes'] if n.get('node_type') == 'theorem'}
    out = []
    for s in (subs or {}).get('submissions') or []:
        if s.get('deprecated_at') or any(s['id'].startswith(r) for r in replaces):
            continue
        node = 'sketch-' + s['id']
        edges = {names[e['source']] for e in g['edges']
                 if e['target'] == node and '.' in (names.get(e['source']) or '')}
        content = (call('GET', '/submissions/%s/solution' % s['id']) or {}).get('content') or ''
        out.append(dict(id=s['id'], status=s.get('status'), username=s.get('username'), edges=edges,
                        content=content, explanation=s.get('explanation') or ''))
    return out


def save_others(path, proofs):
    """Write each proof's Lean source and explanation to others/<FILE stem>.<id8>.lean and .md
    beside FILE, for the comparison that decides whether ours is meaningfully different (dbenbenn,
    2026-10-04: "you might have to go read the other proof to make a decision about whether it's
    different"). Returns the .lean paths."""
    d = os.path.join(os.path.dirname(os.path.abspath(path)), 'others')
    os.makedirs(d, exist_ok=True)
    stem = os.path.splitext(os.path.basename(path))[0]
    out = []
    for p in proofs:
        base = os.path.join(d, '%s.%s' % (stem, p['id'][:8]))
        with open(base + '.lean', 'w', encoding='utf-8') as f:
            f.write(p['content'])
        with open(base + '.md', 'w', encoding='utf-8') as f:
            f.write(p.get('explanation') or '(no explanation)\n')
        out.append(base + '.lean')
    return out


def _norm(text):
    return '\n'.join(l.rstrip() for l in text.strip().splitlines())


def blocking(want, text, live):
    """(kind, proofs): the live proofs that make this one redundant, or (None, []).

    DUPLICATE: the same Lean source (Chornyi Cor 3 was resubmitted verbatim after a context summary
    lost track of the first submission, 2026-10-02). ALREADY-PROVED: a proof whose edges include all
    of `want`, when that proof proves the theorem (ACCEPTED; a reduction is ACCEPTED once its
    children are proved) or has exactly these edges. This proof would add no graph edge to it, and
    goes in only if it is meaningfully different (dbenbenn, 2026-10-04: "submit our own separate
    proof only if it's meaningfully different: correct edges, or mathematically different"). A proof
    with an edge that no live proof has is never blocked: the Lodha-Moore torsion-free milestone had
    a 252-line direct proof by another user, and ours records the paper's route through two
    milestones, edges the graph lacked."""
    dup = [p for p in live if _norm(p['content']) == _norm(text)]
    if dup:
        return 'DUPLICATE', dup
    cov = [p for p in live if want <= p['edges'] and (p['status'] == 'ACCEPTED' or p['edges'] == want)]
    return ('ALREADY-PROVED', cov) if cov else (None, [])


def note_problems(note, proofs):
    """Why a --differs note does not excuse `proofs`: it is a comparison that came out
    "Different from <id>: ..." (a "Same as" comparison is the reason not to submit), names each
    proof (the first eight characters of its id, so it was written against that proof) and says
    how ours differs, in 150 characters or more."""
    probs = [] if note.lstrip().startswith('Different from') else \
        ['the note does not begin "Different from <id>:"']
    probs += ['the note does not name %s' % p['id'][:8] for p in proofs if p['id'][:8] not in note]
    if len(note.strip()) < 150:
        probs.append('the note is too short to say how the proof differs (150 characters)')
    return probs


def describe(p):
    return '%s (%s, %s, edges %s)' % (p['id'][:8], p['username'], p['status'], sorted(p['edges']) or 'none')


def check_solution_top_level(path):
    """The checker looks for a top-level `solution`: one declared inside a `namespace` block is
    `Ns.solution` and is rejected as an unknown identifier (WA). Refuse before submitting."""
    depth, found = [], False
    for line in open(path, encoding='utf-8'):
        m = re.match(r'namespace (\S+)', line)
        if m:
            depth.append(m.group(1)); continue
        if re.match(r'end(\s|$)', line) and depth:
            depth.pop(); continue
        if re.match(r'(theorem|lemma) solution\b', line):
            if depth:
                sys.exit('REFUSED: `solution` is declared inside namespace %s; the checker needs it at '
                         'top level (close the namespace and use `open %s in`).' % ('.'.join(depth), depth[0]))
            found = True
    if not found:
        sys.exit('REFUSED: no top-level `theorem solution` in %s' % path)


def check_no_draft_imports(path):
    """Refuse a file importing a draft statement stub (stubs.py): the platform has no such module
    until that statement is published, so the verifier would fail on the import."""
    from p2mlib.workspace import drafts
    from p2mlib.copies import imports_of
    bad = sorted(set(imports_of(open(path, encoding='utf-8').read())) & set(drafts()))
    if bad:
        sys.exit('REFUSED: imports draft statements not yet published (fetch_theorems.py retires a stub '
                 'once its statement is published):\n  ' + '\n  '.join(bad))


def check_no_metaprogramming(path):
    """The platform's soundness guard rejects custom syntax/elaborator registration ("line N: `macro`
    ... metaprogramming is not supported in submissions"); CFP §6's Lemma 6.1 was refused for a
    `local macro "grp"` merged in from a development module. Refuse first. `notation` is allowed."""
    bad = [(i + 1, l.strip()) for i, l in enumerate(open(path, encoding='utf-8'))
           if re.match(r'\s*((local|scoped)\s+)?(macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|initialize)\b', l)]
    if bad:
        sys.exit('REFUSED: metaprogramming the verifier rejects:\n  ' +
                 '\n  '.join('line %d: %s' % b for b in bad[:5]) + '\ninline the tactic instead.')


def check_no_inline_copies(path, target, allow):
    """A declaration named after a *different* published theorem (primes dropped) is an inline copy:
    the proof uses that theorem without importing it, so the graph misses the edge. CFP §5's
    Lemmas 5.5/5.6 shipped this way (a local `XT1_mul_XT1'`, found only by the post-launch edge
    audit). Refuse, and point at rewire.py, which replaces the copy with an import."""
    from prune_solution import parse
    from rewire import published
    from prune_solution import _workspace
    pub = published(_workspace())
    short = target.split('.')[-1]
    text = open(path, encoding='utf-8').read()
    imported = set(re.findall(r'^import (\S+)', text, re.M))
    hits = []
    for name, kind, _, _, _ in parse(text.splitlines()):
        base = name.split('.')[-1].rstrip("'")
        # a rewired copy (proof = call to the published theorem, which is imported) has its edge
        if base in pub and base != short and base not in allow and name != 'solution' \
                and pub[base][1] not in imported:
            hits.append((name, pub[base][0]))
    # a copy of a DEPRECATED theorem is deliberate: importing it would hang the proof off a retired,
    # hidden node (resolve_imports.py copies those in; QFS 2026-09-27, Lemma 5.7 and core_induction)
    def deprecated(full):
        r = [t for t in (call('GET', '/theorems?theorem_name=' + full).get('theorems') or [])
             if t.get('theorem_name') == full]
        return bool(r and r[0].get('deprecated_at'))
    kept = [(n, f) for n, f in hits if not deprecated(f)]
    for n, f in hits:
        if (n, f) not in kept:
            print('   copy of the deprecated %s allowed (no edge to a retired theorem)' % f)
    hits = ['%s (copy of %s)' % h for h in kept]
    if hits:
        sys.exit('REFUSED: inline copies of published theorems, so their graph edges would be missing:\n  '
                 + '\n  '.join(hits) + '\nrun rewire.py FILE --target %s -o OUT, or pass --allow-copy NAME '
                 'for a genuinely different statement that shares a name.' % short)


def main():
    args = sys.argv[1:]
    go = '--go' in args
    args = [a for a in args if a != '--go']
    expl, replaces = None, []
    if '--explanation' in args:
        i = args.index('--explanation'); expl = open(args[i + 1], encoding='utf-8').read(); del args[i:i + 2]
    # every proof carries a paper-style explanation (prove.md); 480 of 1053 accepted submissions
    # had none on 2026-10-04. --no-explanation is the explicit, logged exception.
    no_expl = '--no-explanation' in args
    args = [a for a in args if a != '--no-explanation']
    if expl is not None:
        probs = explanation.problems(expl)
        if probs:
            sys.exit('REFUSED: the explanation does not meet the platform rules:\n  ' + '\n  '.join(probs))
    elif go and not no_expl:
        sys.exit('REFUSED: no --explanation FILE.md (write the proof\'s explanation first; '
                 '--no-explanation only for a deliberate exception)')
    differs = None
    if '--differs' in args:
        i = args.index('--differs'); differs = open(args[i + 1], encoding='utf-8').read(); del args[i:i + 2]
    allow = []
    while '--allow-copy' in args:
        i = args.index('--allow-copy'); allow.append(args[i + 1]); del args[i:i + 2]
    if '--replaces' in args:
        i = args.index('--replaces'); replaces = args[i + 1:]; del args[i:]
    if len(args) != 2 or any(a.startswith('--') for a in args + replaces):
        sys.exit(__doc__)
    tid, path = theorem_id(args[0]), args[1]
    check_solution_top_level(path)
    check_no_draft_imports(path)
    check_no_metaprogramming(path)
    target = args[0] if not re.fullmatch(r'[0-9a-f-]{36}', args[0]) \
        else call('GET', '/theorems/%s' % tid).get('theorem_name', '')
    check_no_inline_copies(path, target, allow)
    want = import_names(path)
    print('%s\n   file %s\n   edges it should create: %s\n   replaces: %s'
          % (args[0], path, sorted(want) or 'none (a full proof)', replaces or 'nothing'))
    # checked here, at submission time: a batch built hours earlier can find its theorem proved by
    # someone else meanwhile (Lodha-Moore torsion-free, 7 hours before our batch, 2026-10-03)
    live = live_proofs(tid, replaces)
    kind, hits = blocking(want, open(path, encoding='utf-8').read(), live)
    if kind == 'DUPLICATE':
        sys.exit('DUPLICATE: live submission %s has this Lean source; pass --replaces %s to supersede it'
                 % (describe(hits[0]), hits[0]['id']))
    if kind:
        probs = note_problems(differs, hits) if differs is not None else ['no --differs NOTE.md']
        if probs:
            saved = save_others(path, hits)
            sys.exit('ALREADY-PROVED: %s already prove%s this, and this proof adds no edge (its edges: %s). '
                     'Submit it only if it is meaningfully different. Read %s (and the .md explanation '
                     'beside each) against ours and write the comparison: "Different from <id>: ..." '
                     '(other mathematics, or edges correct where its are false: edge_audit.py MISSION '
                     'judges them) is passed as --differs NOTE.md; "Same as <id>: ..." settles that it '
                     'is not submitted; --replaces SID supersedes our own. (%s)'
                     % ('; '.join(describe(p) for p in hits), '' if len(hits) > 1 else 's',
                        sorted(want) or 'none', ', '.join(saved), '; '.join(probs)))
        print('   already proved by %s; submitted as different (--differs)' % '; '.join(describe(p) for p in hits))
    elif any(p['status'] == 'ACCEPTED' for p in live):
        print('   already proved by %s; submitted for its edges %s, which no live proof\'s edges include'
              % ('; '.join(describe(p) for p in live if p['status'] == 'ACCEPTED'), sorted(want)))
    if not go:
        print('dry run -- pass --go to submit'); return
    from submit_verify import post_verify, poll
    r = post_verify(tid, path, expl)
    sid = r.get('submission_id')
    if not sid:
        sys.exit('SUBMIT FAILED: %s' % r)
    v = poll(sid)
    print('   verdict %s %s' % (v.get('status'), sid))
    if v.get('status') == 'PENDING':
        sys.exit('still PENDING (%s): check later with GET /submissions/%s; nothing deprecated'
                 % (v.get('__error'), sid))
    if v.get('status') not in ('ACCEPTED', 'SKETCH_ACCEPTED'):
        sys.exit('not accepted: %s' % str(v.get('error_message'))[:500])
    present, got = sketch_edges(tid, sid)
    if want and got != want:
        sys.exit('EDGES DIFFER: graph %s vs imports %s -- not deprecating anything'
                 % (sorted(got), sorted(want)))
    print('   graph edges match the imports%s' % ('' if want else ' (none)'))
    if replaces:
        p = subprocess.run([sys.executable, os.path.join(HERE, 'deprecate.py'), '--keep', sid] + replaces + ['--go'])
        sys.exit(p.returncode)


if __name__ == '__main__':
    main()
