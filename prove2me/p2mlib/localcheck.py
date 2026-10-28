"""The pure parts of a local check that predicts prove2.me's verifier.

A local "ok" may only be trusted for the exact files it saw, and a plain compile of a solution does
not show what the verifier checks next. Erdős 3 (2026-10-15/16) submitted pieces on stale cached
results and got WA "expected token / Unknown constant `_check`" for signatures and import sets that
compiled locally.

* `content_key(solution, lib_dir, version)`: a hash of the solution and of every lib/ file it
  imports (Definitions.X / Theorems.X -> lib_dir/X.lean), plus a check version. Store it with the
  result; a result counts only while the key still matches. Bump `version` when the check changes.
* `server_check_text(solution, preamble, formal_statement, target)`: the solution compiled the way
  the verifier checks it: both import sets first, then the solution, the published statement and
  `theorem _check : type_of% @target := @solution`. The solution itself must not mention the
  target (the verifier compiles it without the target in scope) and must name its own copy
  `<target>_oai`. For a universe-polymorphic target it then runs the verifier's coercion fallback
  (COE_CHECK): on prove2.me such a target is compared with `solution` through a `CoeT solType x
  targetType` search, which can time out on a large type even though `_check` compiles (oaiq-039,
  2026-10-28: 13 pieces got WA "failed to synthesize CoeT ... (deterministic) timeout at
  `typeclass`"; this search failed for exactly those 13 of the carve's 246 polymorphic statements).
  Such a statement can never be proved there: fold it into its importers (carve.py fold) or state it
  monomorphically.
"""
import hashlib
import os
import re

IMPORT = re.compile(r'^import (\S+)\s*$', re.M)


def content_key(solution, lib_dir, version='1'):
    h = hashlib.sha1(('check-version:' + str(version) + '\n').encode())
    txt = open(solution, 'rb').read()
    h.update(txt)
    for m in sorted(set(re.findall(rb'^import (?:Definitions|Theorems)\.(\S+)', txt, re.M))):
        p = os.path.join(lib_dir, m.decode() + '.lean')
        if os.path.exists(p):
            h.update(m)
            h.update(open(p, 'rb').read())
    return h.hexdigest()


COE_FAILURE = 'the verifier rejects this universe-polymorphic statement: its CoeT fallback'

COE_CHECK = """
open Lean Meta in
run_meta do
  let tgt := `%s
  unless (← getConstInfo tgt).levelParams.isEmpty do
    let s ← inferType (← mkConstWithFreshMVarLevels `solution)
    let t ← inferType (← mkConstWithFreshMVarLevels tgt)
    unless ← isDefEq s t do
      throwError "the type of solution is not the target's"
    withLocalDeclD `x s fun x => do
      let coe := mkAppN (mkConst ``CoeT [← getLevel s, ← getLevel t]) #[s, x, t]
      let ok ← try pure (← synthInstance? coe).isSome catch _ => pure false
      unless ok do
        throwError "%s (CoeT solType x targetType) fails or times out; fold the statement into its importers (carve.py fold) or state it monomorphically (oaiq-039)"
"""


def server_check_text(solution, preamble, formal_statement, target):
    body = solution.rstrip('\n') + '\n\n' + formal_statement.rstrip('\n') + '\n\n' + \
        'theorem _check : type_of%% @%s := @solution\n' % target + COE_CHECK % (target, COE_FAILURE)
    imps = list(dict.fromkeys(IMPORT.findall(solution) + IMPORT.findall(preamble or '') + ['Lean']))
    rest = IMPORT.sub('', body).lstrip('\n')
    return ''.join('import %s\n' % i for i in imps) + '\n' + rest
