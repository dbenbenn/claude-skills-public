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
            if not d.short.startswith('chk_'):
                continue
            target = d.name.rsplit('.', 1)[0] + '.' + d.short[4:] if '.' in d.name else d.short[4:]
            if target not in ms:
                continue
            problem = None
            if target not in d.same_statement_as:
                problem = 'states something other than the milestone'
            elif d.uses_sorry:
                problem = 'uses sorry other than through imported statements'
            out.setdefault(target, []).append((mod, d.name, problem is None, list(d.rests_on), problem))
    return M, ms, out


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
    goal = (M.GOAL[4:] if M.GOAL.startswith('ref:') else M.NAMESPACE + '.' + M.GOAL)
    n = sum(done.values())
    print('\n%d of %d milestones complete; %d have a proof; goal %s' % (n, len(ms), len(good),
          'COMPLETE' if done.get(goal) else 'not complete'))
    sys.exit(0 if done.get(goal) else 1)


if __name__ == '__main__':
    main()
