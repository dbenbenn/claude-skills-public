#!/usr/bin/env python3
"""Make a solution import the published theorems it re-derives, so each is a graph edge.

usage: rewire.py FILE --target NAME -o OUT [--only NAME ...] [--dry]

  --target  the short name of the theorem FILE proves; its own copy is never rewired

A proof assembled from a mission's shared modules carries its own copies of theorems that are
published on their own (`closure_mapA_mapB_eq_F'` beside `CannonFloydParry.closure_mapA_mapB_eq_F`).
The proof then depends on them without saying so: the platform draws an edge only for an
`import Theorems.*`, so the dependency the source argument has is missing from the graph. The
2026-09-24 sweep found eleven such proofs across Chou, CFP, Brin-Squier and Rosenblatt.

For each declaration whose name, with any trailing primes dropped, is the short name of a theorem
in $P2M_WORKSPACE/Theorems/, this replaces its proof with a call to the published theorem and adds
the import; prune_solution --check then deletes what only the old proof used and compiles the
result. The copy's own statement is kept, so the rewire is sound whatever the two statements look
like: if the call proves the copy's statement, the dependency is real. A copy the call cannot
prove (a genuinely different statement that happens to share a name) is restored and reported,
and the file is recompiled without it. Explicit hypotheses the published theorem takes as
instances are handled by installing every hypothesis as an instance first.

Name matching finds copies named after the published theorem; one renamed to something unrelated
is not found. `edge_audit.py` reports which copies are left.
"""
import argparse, os, re, shutil, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prune_solution import parse, _workspace

HERE = os.path.dirname(os.path.abspath(__file__))


def explicit_binders(header):
    """Names of the explicit `(a b : T)` binders of a declaration header, in order.

    Only TOP-LEVEL binder groups count, and only before the header's top-level `:`. A conclusion
    like `(∃ m : …) ∧ …` looks like a binder group (it once produced `haveI := ∃`), and so does a
    parenthesised term inside a binder's type: Lemma 4.8's `(hh : ∀ v, (h v : BinaryTreeAut) = …)`
    once contributed two phantom arguments `h v`."""
    names, depth, i, n = [], 0, 0, len(header)
    while i < n:
        ch = header[i]
        if depth == 0 and ch == ':' and header[i:i + 2] != ':=':
            break                                   # the conclusion starts here
        if ch in '([{⦃':
            if depth == 0 and ch == '(':
                d, j = 0, i                         # scan to the matching `)`
                while j < n:
                    if header[j] in '([{⦃':
                        d += 1
                    elif header[j] in ')]}⦄':
                        d -= 1
                        if d == 0:
                            break
                    j += 1
                grp = header[i + 1:j]
                k, dd = 0, 0                        # the group's own top-level `:`
                while k < len(grp):
                    if grp[k] in '([{⦃':
                        dd += 1
                    elif grp[k] in ')]}⦄':
                        dd -= 1
                    elif grp[k] == ':' and dd == 0:
                        names += [x for x in grp[:k].split() if re.fullmatch(r"[^\W\d][\w'₀-₉]*", x)]
                        break
                    k += 1
                i = j + 1
                continue
            depth += 1
        elif ch in ')]}⦄':
            depth -= 1
        i += 1
    return names


def published(ws):
    """{short name: (full name, module, explicit binder names)} for every theorem in the workspace."""
    out = {}
    tdir = os.path.join(ws, 'Theorems')
    for f in sorted(os.listdir(tdir)):
        if not (f.startswith('Thm_') and f.endswith('.lean')):
            continue
        t = open(os.path.join(tdir, f), encoding='utf-8').read()
        ns = re.search(r'^namespace (\S+)', t, re.M)
        m = re.search(r'^\s*theorem\s+(\S+)', t, re.M)
        if m:
            full = (ns.group(1) + '.' if ns else '') + m.group(1)
            hdr = t[m.start():t.find(':=', m.start())]
            out.setdefault(full.split('.')[-1], (full, 'Theorems.' + f[:-5], explicit_binders(hdr)))
    return out


def body_for(full, header, pub_args):
    """A proof of the copy's statement from the published theorem. Every hypothesis of class
    type becomes available as an instance (the published theorem may take as `[Group.FG N]` what
    the copy took as `(hN : Group.FG N)`), then a few standard ways of applying it are tried."""
    mine = explicit_binders(header)
    inst = ''.join('try haveI := %s; ' % h for h in mine)
    # pass the copy's own arguments wherever the published theorem has an explicit binder of the
    # same name (`fg_of_extension N` when the copy's `hN hQ` became instances there)
    named = ' '.join(a for a in pub_args if a in mine)
    alts = (['exact %s %s' % (full, named)] if named else []) + [
        'exact %s' % full, 'exact %s ..' % full,
        '(apply %s <;> first | assumption | infer_instance)' % full, 'simpa using %s' % full]
    return 'by\n  %sfirst\n%s' % (inst, ''.join('    | %s\n' % x for x in alts))


def rewrite(text, targets, pub):
    lines = text.split('\n')
    for d in sorted(parse(lines), key=lambda d: -d[2]):          # bottom-up keeps spans valid
        base = d[0].split('.')[-1].rstrip("'")
        if d[0].split('.')[-1] not in targets:
            continue
        full, mod, pub_args = pub[base]
        decl = '\n'.join(lines[d[2]:d[3]])
        i = decl.find(':=')
        header = decl[:i].rstrip()
        lines[d[2]:d[3]] = (header + ' :=\n  ' + body_for(full, header, pub_args)).split('\n')
    text = '\n'.join(lines)
    for t in targets:
        mod = pub[t.rstrip("'")][1]
        if not re.search(r'^import %s\s*$' % re.escape(mod), text, re.M):
            text = 'import %s\n' % mod + text
    return text


def check(path):
    """Prune `path` in place, then compile the pruned file itself, so error line numbers refer to
    the file whose declaration spans we attribute them to."""
    p = subprocess.run([sys.executable, os.path.join(HERE, 'prune_solution.py'), path],
                       capture_output=True, text=True)
    if p.returncode:
        return False, p.stdout + p.stderr
    ws = _workspace()
    c = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', os.path.relpath(os.path.abspath(path), ws)],
                       cwd=ws, capture_output=True, text=True)
    out = c.stdout + c.stderr
    bad = c.returncode != 0 or re.search(r': error\b', out) or re.search(r'declaration uses .sorry.', out)
    return not bad, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file'); ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--target', required=True)
    ap.add_argument('--only', nargs='*'); ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    ws = _workspace()
    pub = published(ws)
    text = open(a.file, encoding='utf-8').read()
    if not re.search(r'^theorem solution\b', text, re.M):
        sys.exit('no `theorem solution` in %s' % a.file)
    cands = []
    for d in parse(text.split('\n')):
        name = d[0].split('.')[-1]
        base = name.rstrip("'")
        if name == 'solution' or base not in pub or base == a.target.split('.')[-1]:
            continue
        if a.only and base not in a.only:
            continue
        # already a thin call to the published theorem (an earlier wiring): nothing to do
        body = '\n'.join(text.split('\n')[d[2]:d[3]])
        if re.search(r'(?<![\w.])%s(?![\w\'])' % re.escape(pub[base][0]), body[body.find(':='):]):
            continue
        cands.append(name)
    print('copies of published theorems: %s' % (', '.join(
        '%s -> %s' % (c, pub[c.rstrip("'")][0]) for c in cands) or 'none'))
    if a.dry or not cands:
        return
    kept, failed = list(cands), []
    while kept:
        open(a.out, 'w', encoding='utf-8').write(rewrite(text, kept, pub))
        ok, out = check(a.out)
        if ok:
            break
        # the copy whose span holds the first error line is the one the call could not prove;
        # restore it and try again without it
        spans = {d[0].split('.')[-1]: (d[2] + 1, d[3]) for d in parse(open(a.out).read().split('\n'))}
        errl = [int(n) for n in re.findall(r'\.lean:(\d+):\d+: error', out)]
        # a copy the prune deleted has no span any more (it was unused): it cannot hold the error
        bad = next((c for c in kept for n in errl if c in spans and spans[c][0] <= n <= spans[c][1]), None)
        if bad is None:
            sys.exit('compile failed outside every rewired copy -- the input itself may not compile:\n'
                     + out[-800:])
        print('   could not prove %s from %s; left as it was. Lean said:' % (bad, pub[bad.rstrip("'")][0]))
        for l in [l for l in out.split('\n') if ': error' in l][:4]:
            print('      ' + l[:220])
        kept.remove(bad); failed.append(bad)
    if not kept:
        shutil.copy(a.file, a.out)
        ok, out = check(a.out)
        print('no copy could be rewired; %s is %s pruned' % (a.out, 'the original,' if ok else 'the original (NOT compiling),'))
        sys.exit(1)
    imps = re.findall(r'^import (Theorems\.\S+)', open(a.out).read(), re.M)
    print('rewired %d: %s' % (len(kept), ', '.join(kept)))
    print('theorem imports now: %s' % ', '.join(i.split('Thm_', 1)[-1] for i in imps))
    print('compiles clean: %s' % a.out)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
