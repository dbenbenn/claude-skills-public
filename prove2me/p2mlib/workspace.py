"""The prove2.me Lean workspace and the published statements in it -- the one copy.

There were three `_workspace()` copies (p2m, prune_solution, stage_auditor) and two `published()`
copies (rewire, build_solution); the latter read the first line matching `^theorem`, so a comment
line beginning "theorem" named the wrong declaration (tests/test_rewire.py)."""
import os
import re
from typing import NamedTuple

from .leantext import strip, explicit_binders


def workspace():
    """$P2M_WORKSPACE, else the first known location that exists."""
    for p in (os.environ.get('P2M_WORKSPACE'), '~/claude/prove2me_workspace', '~/prove2me_workspace'):
        if p and os.path.isdir(os.path.expanduser(p)):
            return os.path.expanduser(p)
    raise SystemExit('prove2.me workspace not found; set P2M_WORKSPACE')


def statement_module(full):
    """`LodhaMoore.foo` -> (module `Theorems.Thm_LodhaMoore_foo`, path relative to the workspace)."""
    stem = 'Thm_' + full.replace('.', '_')
    return 'Theorems.' + stem, os.path.join('Theorems', stem + '.lean')


def statement_text(preamble, formal_statement):
    """A statement module's text: exactly what the platform publishes and the verifier imports
    (fetch_theorems writes published ones, stubs.py draft ones, with this one function)."""
    return (preamble or '').strip() + '\n\n' + (formal_statement or '').strip() + '\n'


DRAFTS = os.path.join('Theorems', '.drafts.json')


def drafts(ws=None):
    """{module: mission dir} of the statement modules in Theorems/ that are local draft stubs, not
    published statements (stubs.py records them; fetch_theorems retires each one it publishes)."""
    import json
    p = os.path.join(ws or workspace(), DRAFTS)
    return json.load(open(p)) if os.path.exists(p) else {}


def set_drafts(d, ws=None):
    import json
    p = os.path.join(ws or workspace(), DRAFTS)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, 'w', encoding='utf-8') as f:
        json.dump(dict(sorted(d.items())), f, indent=1)
        f.write('\n')


class Published(NamedTuple):
    full: str          # e.g. MooreFoelner.isTree_iff
    module: str        # e.g. Theorems.Thm_MooreFoelner_isTree_iff
    binders: list      # explicit binder names, in order


def statement_decl(text):
    """(full name, header) of the one theorem in a server-shape statement file, comments ignored."""
    code = strip(text)
    ns = re.search(r'^namespace\s+(\S+)', code, re.M)
    m = re.search(r'^\s*(?:theorem|lemma)\s+(\S+)', code, re.M)
    if not m:
        return None, None
    full = (ns.group(1) + '.' if ns else '') + m.group(1)
    j = code.find(':=', m.start())
    return full, code[m.start():j if j >= 0 else len(code)]


def published_by_full(ws=None):
    """{full name: Published} for every published statement in Theorems/ (draft stubs excluded:
    a submission importing one fails, since the platform has no such module yet)."""
    ws = ws or workspace()
    tdir = os.path.join(ws, 'Theorems')
    draft = drafts(ws)
    out = {}
    for f in sorted(os.listdir(tdir)) if os.path.isdir(tdir) else []:
        if not (f.startswith('Thm_') and f.endswith('.lean')) or 'Theorems.' + f[:-5] in draft:
            continue
        full, hdr = statement_decl(open(os.path.join(tdir, f), encoding='utf-8').read())
        if full:
            out.setdefault(full, Published(full, 'Theorems.' + f[:-5], explicit_binders(hdr)))
    return out


def published(ws=None):
    """{short name: Published} for every statement in Theorems/ (first file wins when two share a
    short name; published_by_full has them all)."""
    out = {}
    for full, p in published_by_full(ws).items():
        out.setdefault(full.rsplit('.', 1)[-1], p)
    return out
