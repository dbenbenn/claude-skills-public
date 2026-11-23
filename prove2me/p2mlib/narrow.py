"""Narrow a statement preamble's `import Mathlib` to the modules the statement actually uses.

A published statement's preamble is frozen, and every proof that imports the statement (every
reduction to it, every milestone above it) pays for the preamble's imports in the verifier.
`import Mathlib` alone peaks at about 6.4 GB of the verifier's 7150 MiB, so such a proof has about
0.7 GB left (q431, q434, q444). The x25519-dalek contracts (2026-11-23) needed no Mathlib at all,
and their reductions were split for memory only because of this line, which draft.extract_payloads
used to write into every preamble.

Mathlib's `#min_imports in` proposes the modules. A narrowed preamble is accepted only when the
statement compiles under it and elaborates to the same term under `pp.all` as with all of Mathlib.
Fewer imports can make Lean pick another instance, coercion or notation, and then the statement
would say something else.

`lean` below is a function from a probe module's text to Lean's output (scripts/narrow_imports.py
compiles in the workspace through the lean-cap wrapper; the tests pass a fake)."""
import re

from .workspace import statement_text

BARE = re.compile(r'^import Mathlib[ \t]*$', re.M)
# import roots a published statement has used (Theorems/, 2026-11-23: Mathlib, Lean, Batteries, Std)
ROOTS = ('Mathlib', 'Batteries', 'Std', 'Lean')
KEPT = ('Definitions', 'Theorems', 'Init')        # the preamble's own; never proposed again
SKIP = {'Mathlib.Tactic.MinImports'}
DECL = re.compile(r'^(?:/--(?:(?!-/).)*-/\s*)?(?:@\[[^\]]*\]\s*)?theorem\s+([^\s:({\[]+)', re.M | re.S)
ERROR = re.compile(r'^\S+:\d+:\d+: error', re.M)
MESSAGE = re.compile(r'^\S+:\d+:\d+: (?:warning|info|error)')
SUGGESTION = re.compile(r'^(?:public\s+)?import\s+([\w.\']+)\s*$')


class NarrowError(Exception):
    pass


def whole_mathlib(preamble):
    """Whether the preamble imports all of Mathlib (a bare `import Mathlib` line)."""
    return bool(BARE.search(preamble or ''))


def probe_text(preamble, formal_statement, min_imports):
    """The statement module, with `#min_imports in` on its declaration when `min_imports`, and a
    `pp.all` `#check` of it at the end (inside its namespace, so the name resolves as written)."""
    text = statement_text(preamble, formal_statement)
    m = DECL.search(text)
    if not m:
        raise NarrowError('no `theorem` declaration found')
    name = m.group(1)
    if min_imports:
        text = text[:m.start()] + '#min_imports in\n' + text[m.start():]
    check = 'set_option pp.all true in\n#check @%s\n' % name
    ends = list(re.finditer(r'^end\b.*$', text, re.M)) if re.search(r'^namespace\s', text, re.M) else []
    if ends:
        i = ends[-1].start()
        return text[:i] + check + '\n' + text[i:]
    return text.rstrip('\n') + '\n\n' + check


def errors(log):
    return [l for l in log.split('\n') if ERROR.match(l)]


def suggestions(log):
    """The modules `#min_imports` printed, in order."""
    out = []
    for l in log.split('\n'):
        m = SUGGESTION.match(l)
        if m and m.group(1) not in out:
            out.append(m.group(1))
    return out


def check_output(log):
    """The `#check` output: what is left of the log once lean-cap's lines, positioned messages
    (warnings) and `#min_imports`' import lines are dropped."""
    keep = [l for l in log.split('\n')
            if l.strip() and not l.startswith('lean-cap:') and not MESSAGE.match(l) and not SUGGESTION.match(l)]
    return '\n'.join(keep).strip()


def narrowed_preamble(preamble, suggested, with_lean=False):
    """`preamble` with its `import Mathlib` line replaced, in place, by the suggested library modules it
    does not import yet (none: the line goes). `Lean.*` modules are left out unless `with_lean`:
    `#min_imports` names Lean.Parser.Command for the probe's own syntax."""
    lines = (preamble or '').split('\n')
    have = {l.split()[1] for l in lines if l.startswith('import ') and len(l.split()) > 1}
    add, odd = [], []
    for mod in suggested:
        root = mod.split('.')[0]
        if root in KEPT or mod in SKIP or mod in have or mod in add:
            continue
        if root not in ROOTS:
            odd.append(mod)
        elif root != 'Lean' or with_lean:
            add.append(mod)
    if odd:
        raise NarrowError('#min_imports proposes %s, outside the import roots published statements use (%s); '
                          'find a Mathlib module that imports it, or keep `import Mathlib`'
                          % (', '.join(odd), ', '.join(ROOTS)))
    out = []
    for l in lines:
        if BARE.match(l):
            out += ['import ' + m for m in sorted(add)]
        else:
            out.append(l)
    return '\n'.join(out)


def narrow(preamble, formal_statement, lean):
    """The narrowed preamble, or NarrowError saying why there is none."""
    full = lean(probe_text(preamble, formal_statement, True))
    if errors(full):
        raise NarrowError('the statement does not compile with all of Mathlib: ' + errors(full)[0][:300])
    want, sug = check_output(full), suggestions(full)
    if not want:
        raise NarrowError('no #check output in the full-Mathlib probe')
    tried, last = set(), ''
    for with_lean in (False, True):
        pre = narrowed_preamble(preamble, sug, with_lean)
        if pre in tried:
            continue
        tried.add(pre)
        log = lean(probe_text(pre, formal_statement, False))
        if errors(log):
            last = errors(log)[0][:300]
            continue
        got = check_output(log)
        if got != want:
            raise NarrowError('the statement elaborates differently with the narrowed imports, so they would '
                              'change what it says; keep `import Mathlib` or add the module that restores it.\n'
                              'with Mathlib:\n%s\nnarrowed:\n%s' % (want[:1500], got[:1500]))
        return pre
    raise NarrowError('the narrowed statement does not compile: ' + last)


def rewrite_file(path, preamble):
    """Replace the bare `import Mathlib` line of the statement file `path` by the import lines of
    `preamble` that the file does not already have (none: the line is deleted)."""
    lines = open(path, encoding='utf-8').read().split('\n')
    have = {l.strip() for l in lines if l.startswith('import ')}
    new = [l for l in preamble.split('\n') if l.startswith('import ') and l.strip() not in have]
    out, done = [], False
    for l in lines:
        if not done and BARE.match(l):
            out += new
            done = True
        else:
            out.append(l)
    if not done:
        raise NarrowError('%s has no bare `import Mathlib` line' % path)
    open(path, 'w', encoding='utf-8').write('\n'.join(out))
