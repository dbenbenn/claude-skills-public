#!/usr/bin/env python3
"""Is a mission's development complete? Each milestone's proof, judged by Lean, and the graph.

usage: check_complete.py MISSION_DIR CHECK_MODULE [CHECK_MODULE ...]

  CHECK_MODULE  a module under $P2M_WORKSPACE/Solutions proving milestones as `chk_<name>`
                (e.g. LodhaMoore/Dev/Lemma54)

A milestone's proof imports its sibling milestones' statements (the stubs stubs.py installs), as
its submission will, so it is a reduction until they are proved -- exactly as on the platform.
The development is complete when every milestone has a proof that
  * states the milestone: `chk_<name>`'s statement equals the stub's (LeanInfo: same statement up
    to binder names, universes, local predicates and proofs);
  * uses `sorry` only through statements it imports (LeanInfo `uses_sorry`, which stops at
    `Theorems.*` constants);
and the milestones' "rests on" relation (LeanInfo `rests_on`) has no cycle. A milestone is
COMPLETE when its proof is good and everything it rests on is COMPLETE; a statement outside the
mission that a proof rests on is listed, since its platform status decides the rest.

Exit 0 when the goal is COMPLETE.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import leaninfo  # noqa: E402
from p2mlib.mission import load  # noqa: E402
from p2mlib.workspace import workspace, statement_module  # noqa: E402


def proofs(mdir, checks, ws):
    """{milestone full name: [(module, chk decl, ok, rests_on, problem)]} and the milestone names."""
    M = load(mdir)
    ms = [T.get('namespace', M.NAMESPACE) + '.' + T['name'] for T in M.THEOREMS]
    mods = [statement_module(f)[0] for f in ms]
    out = {}
    for mod in checks:
        info = leaninfo.run(os.path.join(ws, 'Solutions', mod + '.lean'), ws=ws, candidates=mods)
        if info.errors:
            sys.exit('%s does not compile: %s' % (mod, info.errors[0].text.splitlines()[0][:200]))
        for d in info.decls:
            target = target_of(d.name, ms)
            if target is None:
                continue
            problem = None
            if not d.statement_compared:
                problem = 'its statement could not be compared (LeanInfo failed on it; not a verdict)'
            elif target not in d.same_statement_as:
                problem = 'states something other than the milestone'
            elif d.uses_sorry:
                problem = 'uses sorry other than through imported statements'
            out.setdefault(target, []).append((mod, d.name, problem is None, list(d.rests_on), problem))
    return M, ms, out


def target_of(name, ms):
    """The milestone a check block `<ns>.chk_<short>` proves: `<ns>.<short>` when that is a
    milestone, else the one milestone named `<short>` (a Blueprint keeps its checks in its own
    namespace, CFW's in CFWPlan.Main), else None (not a check, or ambiguous)."""
    short = name.rsplit('.', 1)[-1]
    if not short.startswith('chk_'):
        return None
    base = short[4:]
    full = name.rsplit('.', 1)[0] + '.' + base if '.' in name else base
    if full in ms:
        return full
    same = [m for m in ms if m.rsplit('.', 1)[-1] == base]
    return same[0] if len(same) == 1 else None


def complete(ms, good):
    """{milestone: True/False} -- complete when a good proof's every rests-on milestone is complete;
    cycles are never complete. good: {milestone: rests_on of its best good proof}."""
    state = {}

    def visit(m, path):
        if m in state:
            return state[m]
        if m in path or m not in good:
            return False
        state[m] = all(visit(r, path | {m}) for r in good[m] if r in ms)
        return state[m]
    return {m: visit(m, frozenset()) for m in ms}


def summary(M, done, ms, good):
    """(the closing line, success). A standalone package has no GOAL: it succeeds when every
    statement is complete (markov-heat-kernels 2026-10-04 crashed here with AttributeError)."""
    n = sum(done.values())
    head = '%d of %d milestones complete; %d have a proof; ' % (n, len(ms), len(good))
    g = getattr(M, 'GOAL', None)
    if not g:
        ok = n == len(ms)
        return head + 'no goal (standalone package): %s' % ('all complete' if ok else 'not all complete'), ok
    goal = g[4:] if g.startswith('ref:') else M.NAMESPACE + '.' + g
    ok = bool(done.get(goal))
    return head + 'goal ' + ('COMPLETE' if ok else 'not complete'), ok


def main():
    args = sys.argv[1:]
    if len(args) < 2:
        sys.exit(__doc__)
    ws = workspace()
    M, ms, found = proofs(os.path.abspath(args[0]), args[1:], ws)
    good = {}
    for m, ps in found.items():
        ok = [p for p in ps if p[2]]
        if ok:
            good[m] = min((p[3] for p in ok), key=len)
    done = complete(ms, good)
    external = sorted({r for rs in good.values() for r in rs if r not in ms})
    short = lambda f: f.rsplit('.', 1)[-1]
    for m in ms:
        ps = found.get(m, [])
        if m in good:
            sib = [short(r) for r in good[m] if r in ms]
            how = 'COMPLETE ' if done[m] else 'reduction'
            print('%s %-50s %s' % (how, short(m), ('rests on ' + ', '.join(sib)) if sib else 'outright'))
        elif ps:
            print('BAD      %-50s %s' % (short(m), '; '.join('%s: %s' % (p[1], p[4]) for p in ps)))
        else:
            print('no proof %s' % short(m))
    if external:
        print('rests on statements outside the mission (their platform status decides): %s' % ', '.join(external))
    line, ok = summary(M, done, ms, good)
    print('\n' + line)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
