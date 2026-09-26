#!/usr/bin/env python3
"""Find missing graph edges that rewire.py cannot see: a solution whose last step is a sibling's.

usage: edge_overlap.py SOLUTIONS_DIR

rewire.py catches a copy of a published theorem only by name (`foo'` for published `foo`). A
development can also pass through a sibling's statement under other names -- CFP §7's Theorem 7.2
was `mulEquivF.trans psiEquiv`, where `psiEquiv` is the construction behind the published Delta_1
conjugation, rebuilt inline, and it shipped with no edge to it. Counting shared declarations does
not find this (a common lemma library makes every pair look alike); comparing final steps does.

For each Sol_<A>.lean in the directory, the "top proof" is the body of `solution` plus the body of
the development theorem it calls (`<A>'`, or the `_of` theorem it applies). This prints every pair
A, B where A does not import B's theorem and the two top proofs name a common declaration of the
file's own (not Mathlib's). Read A's top proof: when it passes through B's statement, take that
step from the published theorem (compose with its conclusion), prune, and resubmit with
`submit_solution.py --replaces`.
"""
import os, re, sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial )*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance) ([\w'.]+)", re.M)
TOP = re.compile(r"^(?:@\[|private |protected |noncomputable |partial |theorem |lemma |def |abbrev |"
                 r"structure |inductive |instance |end |namespace |section |open |/-)", re.M)


def body(text, name):
    m = re.search(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def) %s(?![\w'])" % re.escape(name),
                  text, re.M)
    if not m:
        return ''
    nxt = TOP.search(text, m.end())
    return text[m.end():nxt.start() if nxt else len(text)]


def top_idents(text, own):
    """Own declarations named in `solution` and in the development theorems it names directly."""
    sol = body(text, 'solution')
    first = {i for i in re.findall(r"[\w'.]+", sol) if i in own or i.split('.')[-1] in own}
    names = set()
    for i in first:
        names.add(i.split('.')[-1])
        names |= {j.split('.')[-1] for j in re.findall(r"[\w'.]+", body(text, i.split('.')[-1]))
                  if j.split('.')[-1] in own}
    return names


def main():
    d = sys.argv[1]
    sols = {}
    for f in sorted(os.listdir(d)):
        m = re.fullmatch(r'Sol_(\w+)\.lean', f)
        if not m:
            continue
        t = open(os.path.join(d, f), encoding='utf-8').read()
        own = {n.split('.')[-1] for n in DECL.findall(t)} - {'solution'}
        imps = set(re.findall(r'^import Theorems\.Thm_\w*?_(\w+)$', t, re.M))
        sols[m.group(1)] = (top_idents(t, own), imps)
    hits = 0
    for a, (ta, ia) in sols.items():
        for b, (tb, _) in sols.items():
            if a == b or b in ia:
                continue
            common = sorted(n for n in ta & tb if n.rstrip("'") not in (a, b))
            if common:
                hits += 1
                print('%s  and  %s  share top-proof steps: %s' % (a, b, ', '.join(common)))
    if not hits:
        print('no solution shares a top-proof step with a sibling it does not import')


if __name__ == '__main__':
    main()
