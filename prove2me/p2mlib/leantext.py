"""Lexical handling of Lean source: comment stripping and binder names.

Comment stripping is a scanner over Lean's lexical rules (literals, nested block comments), not a
regular expression, and it is the one copy: stage_auditor, prune_solution and p2m's publish guard
all use it. Anything about declarations, commands or names comes from `leaninfo` instead."""
import re

_IDCHAR = re.compile(r"[\w'.!?\u2080-\u209c]")
_CHARLIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
_RAW = re.compile(r'r(#*)"')


def strip(text):
    """Lean source with every comment removed: block comments (nested), docstrings and line
    comments. Blind staging depends on this — a docstring handed to an auditor is the intended
    reading leaking into a reading that is supposed to be independent.

    Literals are copied verbatim, so a comment marker inside one is not a comment: `"/-"`,
    `"a--b"`, `r#"-- x"#`, `«foo--bar»` and `'-'`. An unclosed block comment is an error rather
    than a silent truncation of the rest of the file. Runs of blank lines left by deleted
    comments are collapsed, outside literals only."""
    code, lits, i, n = [''], [], 0, len(text)
    buf = []

    def lit(j):                       # text[i:j] is a literal: keep it out of the collapse
        buf.append(('c', ''.join(code_acc)))
        code_acc.clear()
        buf.append(('l', text[i:j]))

    code_acc = []
    while i < n:
        prev = text[i - 1] if i else ''
        ident_before = bool(prev) and bool(_IDCHAR.match(prev))
        if text.startswith('/-', i):
            depth, j = 0, i
            while j < n:
                if text.startswith('/-', j):
                    depth += 1; j += 2
                elif text.startswith('-/', j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            if depth:
                line = text.count('\n', 0, i) + 1
                raise ValueError('unclosed block comment starting at line %d' % line)
            i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j == -1 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            lit(min(j + 1, n)); i = min(j + 1, n)
        elif text[i] == '«':
            j = text.find('»', i)
            j = n if j == -1 else j + 1
            lit(j); i = j
        elif text[i] == 'r' and not ident_before and _RAW.match(text, i):
            close = '"' + _RAW.match(text, i).group(1)
            j = text.find(close, _RAW.match(text, i).end())
            j = n if j == -1 else j + len(close)
            lit(j); i = j
        elif text[i] == "'" and not ident_before and _CHARLIT.match(text, i):
            j = _CHARLIT.match(text, i).end()
            lit(j); i = j
        else:
            code_acc.append(text[i]); i += 1
    buf.append(('c', ''.join(code_acc)))
    out = ''.join(re.sub(r'\n{3,}', '\n\n', t) if k == 'c' else t for k, t in buf)
    return out.strip() + '\n'


def explicit_binders(header):
    """Names of the explicit `(a b : T)` binders of a declaration header, in order.

    Only TOP-LEVEL binder groups count, and only before the header's top-level `:`. A conclusion
    like `(∃ m : …) ∧ …` looks like a binder group (it once produced `haveI := ∃`), and so does a
    parenthesised term inside a binder's type: Lemma 4.8's `(hh : ∀ v, (h v : BinaryTreeAut) = …)`
    once contributed two phantom arguments `h v`."""
    names, depth, i, n = [], 0, 0, len(header)
    while i < n:
        ch = header[i]
        if depth == 0 and ch == ':' and header[i:i + 2] != ':=':
            break                                   # the conclusion starts here
        if ch in '([{⦃':
            if depth == 0 and ch == '(':
                d, j = 0, i                         # scan to the matching `)`
                while j < n:
                    if header[j] in '([{⦃':
                        d += 1
                    elif header[j] in ')]}⦄':
                        d -= 1
                        if d == 0:
                            break
                    j += 1
                grp = header[i + 1:j]
                k, dd = 0, 0                        # the group's own top-level `:`
                while k < len(grp):
                    if grp[k] in '([{⦃':
                        dd += 1
                    elif grp[k] in ')]}⦄':
                        dd -= 1
                    elif grp[k] == ':' and dd == 0:
                        names += [x for x in grp[:k].split() if re.fullmatch(r"[^\W\d][\w'₀-₉]*", x)]
                        break
                    k += 1
                i = j + 1
                continue
            depth += 1
        elif ch in ')]}⦄':
            depth -= 1
        i += 1
    return names


_HEADER_LINE = re.compile(r'(?:import|prelude|module|public\s+import|meta\s+import)\b[^\n]*')


def header_end(text):
    """Where a Lean file's header ends: the offset of its first command. The header grammar is only
    whitespace, comments, `prelude`, `module` and `import` lines, so this scanner is exact; a doc
    comment (`/--`, `/-!`) already belongs to the first command."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
        elif text.startswith('/-', i) and not text.startswith(('/--', '/-!'), i):
            depth, j = 0, i
            while j < n:
                if text.startswith('/-', j):
                    depth += 1; j += 2
                elif text.startswith('-/', j):
                    depth -= 1; j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            i = j
        else:
            m = _HEADER_LINE.match(text, i)
            if not m:
                break
            i = m.end()
    return i

