"""Load a mission's data (MISSION_DIR/mission.py) -- never through `import mission` -- and its prose.

`import mission` goes through Python's module cache, so a second mission in the same process is
silently the first one (submit_all waited forever on another mission's statement in the test
suite, 2026-10-02). This loads the file under a fresh module name each time.

**Prose as Markdown (new missions, Phase 5).** A mission may keep each item's prose in
`MISSION_DIR/prose/<name>.md` instead of Python strings (every mission through Lodha–Moore kept
it in `mission.py` or a `prose.py` of raw strings, where a stray `\\'` once reached a live Draft):

    ---
    title: Lemma 5.3 — a standard form derived from y_s^{±1}
    milestone_title: Lemma 5.3 — ...
    ---
    The natural-language statement, Markdown + KaTeX, as it will appear.

    ## Milestone
    The milestone description (optional; only for a milestone).

`<name>` is the item's `name` (a definition bundle's or a theorem's short name). The front matter is
`key: value` lines, one per field, a value optionally in quotes. load() merges each file into the
DEFINITIONS/THEOREMS entry of that name: the body before `## Milestone` is `nls`, the section is
`milestone_description`. It refuses a field set both in mission.py and in the file, and a file that
names no item, so the two can never silently disagree. A mission without prose/ loads as before.
"""
import importlib.util
import itertools
import os
import re
import sys

_n = itertools.count()
MILESTONE = re.compile(r'^## Milestone[ \t]*$', re.M)


def front_matter(text):
    """(fields, body): `---` front matter of `key: value` lines, if the text starts with one."""
    if not text.startswith('---\n'):
        return {}, text
    end = text.find('\n---\n', 3)
    if end < 0:
        raise ValueError('front matter opened with --- but never closed')
    fields = {}
    for line in text[4:end].split('\n'):
        if not line.strip():
            continue
        key, sep, value = line.partition(':')
        if not sep or not re.fullmatch(r'[a-z_]+', key.strip()):
            raise ValueError('front matter line is not `key: value`: %r' % line)
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] and value[0] in '"\'':
            value = value[1:-1]
        fields[key.strip()] = value
    return fields, text[end + 5:]


def read_prose(path):
    """The fields one prose/<name>.md file supplies."""
    fields, body = front_matter(open(path, encoding='utf-8').read())
    parts = MILESTONE.split(body)
    if len(parts) > 2:
        raise ValueError('%s: more than one "## Milestone" section' % path)
    out = dict(fields)
    if parts[0].strip():
        out['nls'] = parts[0].strip()
    if len(parts) == 2:
        out['milestone_description'] = parts[1].strip()
    return out


def merge_prose(m, mdir):
    """Merge MISSION_DIR/prose/*.md into the loaded mission module `m` (see the module doc)."""
    pdir = os.path.join(mdir, 'prose')
    if not os.path.isdir(pdir):
        return
    items = {}
    for lst in ('DEFINITIONS', 'THEOREMS'):
        for it in getattr(m, lst, []):
            items[it['name']] = it
    for f in sorted(os.listdir(pdir)):
        if not f.endswith('.md'):
            continue
        name = f[:-3]
        if name not in items:
            raise SystemExit('prose/%s names no item of mission.py (DEFINITIONS/THEOREMS)' % f)
        for k, v in read_prose(os.path.join(pdir, f)).items():
            if items[name].get(k):
                raise SystemExit('%s.%s is set both in mission.py and in prose/%s; keep one' % (name, k, f))
            items[name][k] = v


STATEMENT_START = re.compile(r'^(?:namespace|theorem|open\s.*\bin\s*$)', re.M)


def statement_payload(path):
    """(preamble, formal_statement) of one statements/Thm_<NS>_<name>.lean file: the preamble is
    everything before its first `namespace` or `theorem` line (imports, `open`s, `universe`s), and
    the two must rejoin to the file exactly (workspace.statement_text), or the file is refused."""
    from .workspace import statement_text
    text = open(path, encoding='utf-8').read()
    m = STATEMENT_START.search(text)
    if not m:
        raise SystemExit('%s: no `namespace` or `theorem` line' % path)
    pre, fs = text[:m.start()], text[m.start():]
    if statement_text(pre, fs) != text:
        raise SystemExit('%s is not in published shape: imports and opens, one blank line, the statement, '
                         'one final newline' % path)
    return pre.strip(), fs.strip()


def statement_payloads(mdir):
    """{short name: (preamble, formal_statement)} from MISSION_DIR/statements/, the source of truth
    of a mission drafted with one file per statement: each file is byte for byte the module the
    platform publishes, so stubs.py installs it unchanged."""
    out = {}
    sdir = os.path.join(mdir, 'statements')
    for f in sorted(os.listdir(sdir)):
        if f.startswith('Thm_') and f.endswith('.lean'):
            pre, fs = statement_payload(os.path.join(sdir, f))
            m = re.search(r'^theorem\s+(\S+)', fs, re.M)
            if not m:
                raise SystemExit('statements/%s has no theorem' % f)
            out[m.group(1).rsplit('.', 1)[-1]] = (pre, fs)
    return out


def lib_payload(path):
    """(preamble, formal_statement) of a standalone statement file lib/Thm_<name>.lean, split exactly
    as publish_standalone.py sends it: the import lines, then everything else."""
    lines = open(path, encoding='utf-8').read().split('\n')
    pre = '\n'.join(l for l in lines if l.startswith('import '))
    body = '\n'.join(l for l in lines if not l.startswith('import ')).strip() + '\n'
    return pre, body


def lib_payloads(mdir):
    """{short name: (preamble, formal_statement)} from MISSION_DIR/lib/Thm_*.lean, the layout of a
    p2m-standalone folder (publish_standalone.py)."""
    out = {}
    for f in sorted(os.listdir(os.path.join(mdir, 'lib'))):
        if f.startswith('Thm_') and f.endswith('.lean'):
            pre, fs = lib_payload(os.path.join(mdir, 'lib', f))
            m = re.search(r'^theorem\s+(\S+)', fs, re.M)
            if not m:
                raise SystemExit('lib/%s has no theorem' % f)
            out[m.group(1).rsplit('.', 1)[-1]] = (pre, fs)
    return out


def load(mdir):
    mdir = os.path.abspath(mdir)
    name = '_p2m_mission_%d' % next(_n)
    spec = importlib.util.spec_from_file_location(name, os.path.join(mdir, 'mission.py'))
    m = importlib.util.module_from_spec(spec)
    if mdir not in sys.path:            # mission.py may import its own helpers (prose.py, …)
        sys.path.insert(0, mdir)
    spec.loader.exec_module(m)
    merge_prose(m, mdir)
    if not hasattr(m, 'payloads') and os.path.isdir(os.path.join(mdir, 'statements')):
        m.payloads = lambda: statement_payloads(mdir)
    elif not hasattr(m, 'payloads') and os.path.isdir(os.path.join(mdir, 'lib')):
        m.payloads = lambda: lib_payloads(mdir)
    return m
