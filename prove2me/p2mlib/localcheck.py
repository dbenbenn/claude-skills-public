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
  `<target>_oai`.
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


def server_check_text(solution, preamble, formal_statement, target):
    body = solution.rstrip('\n') + '\n\n' + formal_statement.rstrip('\n') + '\n\n' + \
        'theorem _check : type_of%% @%s := @solution\n' % target
    imps = list(dict.fromkeys(IMPORT.findall(solution) + IMPORT.findall(preamble or '')))
    rest = IMPORT.sub('', body).lstrip('\n')
    return ''.join('import %s\n' % i for i in imps) + '\n' + rest
