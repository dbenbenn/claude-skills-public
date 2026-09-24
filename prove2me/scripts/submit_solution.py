#!/usr/bin/env python3
"""Submit a solution, check the graph shows exactly its imports, then retire what it replaces.

usage: submit_solution.py THEOREM FILE [--explanation FILE.md] [--replaces SID ...] [--go]
       (dry run without --go; THEOREM is a full name like Chou.hasPackingProperty_of_finite,
        or a theorem id)

The last step of rewire.py and of any prune that drops a false edge, done the same way every
time instead of by a per-mission submit script:

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
from p2m import call
from prune_solution import _workspace


def theorem_id(name):
    if re.fullmatch(r'[0-9a-f-]{36}', name):
        return name
    r = call('GET', '/theorems?theorem_name=%s&limit=5' % name)
    hit = [t for t in (r.get('theorems') or []) if t.get('theorem_name') == name]
    if not hit:
        sys.exit('no published theorem named %s' % name)
    return hit[0].get('id') or hit[0].get('theorem_id')


def import_names(path):
    ws = _workspace()
    out = set()
    for mod in re.findall(r'^import (Theorems\.\S+)', open(path, encoding='utf-8').read(), re.M):
        t = open(os.path.join(ws, mod.replace('.', '/') + '.lean'), encoding='utf-8').read()
        ns = re.search(r'^namespace (\S+)', t, re.M)
        m = re.search(r'^\s*theorem\s+(\S+)', t, re.M)
        out.add((ns.group(1) + '.' if ns else '') + m.group(1))
    return out


def sketch_edges(tid, sid):
    g = call('GET', '/theorems/%s/graph' % tid)
    names = {n.get('theorem_id'): n.get('theorem_name') for n in g['nodes'] if n.get('node_type') == 'theorem'}
    node = 'sketch-' + sid
    present = any(e['source'] == node or e['target'] == node for e in g['edges'])
    return present, {names[e['source']] for e in g['edges']
                     if e['target'] == node and '.' in (names.get(e['source']) or '')}


def main():
    args = sys.argv[1:]
    go = '--go' in args
    args = [a for a in args if a != '--go']
    expl, replaces = None, []
    if '--explanation' in args:
        i = args.index('--explanation'); expl = open(args[i + 1], encoding='utf-8').read(); del args[i:i + 2]
    if '--replaces' in args:
        i = args.index('--replaces'); replaces = args[i + 1:]; del args[i:]
    if len(args) != 2 or any(a.startswith('--') for a in args + replaces):
        sys.exit(__doc__)
    tid, path = theorem_id(args[0]), args[1]
    want = import_names(path)
    print('%s\n   file %s\n   edges it should create: %s\n   replaces: %s'
          % (args[0], path, sorted(want) or 'none (a full proof)', replaces or 'nothing'))
    if not go:
        print('dry run -- pass --go to submit'); return
    from submit_verify import post_verify, poll
    r = post_verify(tid, path, expl)
    sid = r.get('submission_id')
    if not sid:
        sys.exit('SUBMIT FAILED: %s' % r)
    v = poll(sid)
    print('   verdict %s %s' % (v.get('status'), sid))
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
