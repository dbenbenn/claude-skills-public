"""What a solution imports, checked the same way by every submitter -- the one copy.

submit_solution.py runs these checks (and so do submit_all.py and oai_submit.py, which submit only
through it); p2mlib.splitrun runs the Disproved check on the statements its pieces import from
someone else (external statements and `external_theorems`).

* Draft stubs (stubs.py, listed in Theorems/.drafts.json): the platform has no such module until
  the statement is published, so a solution importing one is refused. A stub stays listed until
  fetch_theorems.py writes its published text, and nothing ran that fetch for a sibling of an
  in-review mission that had just been published and proved (oaiq-100, 2026-10-29: the cure was
  `fetch_theorems.py --names ...`, which no message named). `retire_published` asks the platform
  about each one and runs that fetch for the published ones.
* Disproved theorems: the verifier accepts a proof resting on one (SKETCH_ACCEPTED), but the
  target can then never become Proved, and /open-leaves does not list a Disproved leaf, so
  everything above it stays Open with no visible reason (oaiq-109: JM Prop 3.3 rested on a
  disproved JdlS statement)."""
import os
import re
import subprocess
import sys

from .copies import imports_of

FETCH = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts', 'fetch_theorems.py')


def _call(call):
    if call is None:
        from .api import call
    return call


def theorem_imports(text):
    """The `Theorems.*` modules a Lean source imports (comments ignored)."""
    return [m for m in imports_of(text) if m.startswith('Theorems.')]


def module_theorem(mod, ws):
    """The full name of the theorem that the workspace's statement module `mod` declares, or None:
    the declaration whose name, dots read as underscores, is the module's `Thm_<X>`. A first-match
    regex once read a module docstring line beginning "theorem for balls" as the theorem `for`, and
    missed `lemma`s; nested `namespace A` / `namespace B` give `A.B` (an OAI-generated statement
    nests `namespace OAI` and `namespace X`, 2026-10-07); `theorem _root_.A.b` ignores the
    namespaces in force (carved SWPort pieces, 2026-10-08)."""
    path = os.path.join(ws, *mod.split('.')) + '.lean'
    if not os.path.exists(path):
        return None
    want = mod.split('.', 1)[1][len('Thm_'):]
    cands, stack = [], []
    for line in open(path, encoding='utf-8').read().split('\n'):
        m = re.match(r'^(namespace|section)\b\s*(\S*)', line)
        if m:
            stack.append((m.group(1), m.group(2)))
            continue
        m = re.match(r'^end\b\s*(\S*)\s*$', line)
        if m and stack:
            stack.pop()
            continue
        m = re.match(r'^\s*(?:private\s+)?(?:theorem|lemma)\s+(\S+)', line)
        if m:
            name = m.group(1)
            cands.append(name[len('_root_.'):] if name.startswith('_root_.') else
                         '.'.join([n for k, n in stack if k == 'namespace'] + [name]))
    hit = [c for c in cands if c.replace('.', '_') == want or c.split('.')[-1] == want]
    return hit[0] if hit else None


def lookup(name, call=None):
    """The live /theorems row named exactly `name`, or None (not published)."""
    r = _call(call)('GET', '/theorems?theorem_name=%s&limit=5' % name)
    hit = [t for t in ((r.get('theorems') if isinstance(r, dict) else None) or [])
           if t.get('theorem_name') == name]
    return hit[0] if hit else None


def disproved(names, call=None):
    """The theorems of `names` that the platform lists as Disproved, sorted."""
    out = []
    for n in sorted(set(names)):
        row = lookup(n, call)
        if row and row.get('status') == 'Disproved':
            out.append(n)
    return out


def disproved_message(bad):
    return ('REFUSED: imports Disproved theorems, so the target could never become Proved:\n  ' +
            '\n  '.join(bad) + '\nimport a corrected (Proved or Open) statement instead.')


def published_drafts(mods, ws, call=None):
    """{module: theorem name} of the draft-stub modules `mods` whose statement the platform has
    published (the stub is still listed only because no fetch has run since)."""
    out = {}
    for m in mods:
        n = module_theorem(m, ws)
        if n and lookup(n, call):
            out[m] = n
    return out


def fetch_command(names):
    return 'python3 %s --names %s' % (FETCH, ' '.join(names))


def retire_published(mods, ws, call=None, run=subprocess.run):
    """Run `fetch_theorems.py --names` for the draft-stub modules of `mods` that the platform has
    published, which retires their stubs. Returns (the modules of `mods` still listed as drafts
    afterwards, the names fetched)."""
    from .workspace import drafts
    pub = published_drafts(mods, ws, call)
    fetched = sorted(pub.values())
    if fetched:
        env = dict(os.environ, P2M_WORKSPACE=ws)
        run([sys.executable, FETCH, '--names'] + fetched, capture_output=True, text=True, env=env)
    left = drafts(ws)
    return sorted(m for m in mods if m in left), fetched
