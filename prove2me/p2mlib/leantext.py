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



_TACTIC_MACRO = re.compile(r'^[ \t]*(?:(?:local|scoped)[ \t]+)?macro[ \t]+"([A-Za-z_][\w]*)"[ \t]*:[ \t]*tactic[ \t]*=>\s*`\(tactic\|', re.M)
_DOC_BEFORE = re.compile(r'/--(?:(?!-/).)*-/[ \t]*\n$', re.S)


def tactic_macros(text):
    """(text, {name: body}): every `macro "name" : tactic => `(tactic| body)` removed, with the doc
    comment right above it (left behind, it dangles before the next command: WLIdentification
    2026-10-23), and its body, whitespace-normalized. Uses are not touched (inline_macro_uses)."""
    macros = {}
    while True:
        m = _TACTIC_MACRO.search(text)
        if not m:
            return text, macros
        name, i, depth = m.group(1), m.end(), 1
        while i < len(text) and depth:
            depth += {'(': 1, ')': -1}.get(text[i], 0)
            i += 1
        macros[name] = ' '.join(text[m.end():i - 1].split())
        end = text.find('\n', i)
        end = len(text) if end < 0 else end + 1
        start = m.start()
        d = _DOC_BEFORE.search(text[:start][-20000:])
        if d:
            start -= len(text[:start][-20000:]) - d.start()
        while text[end:end + 1] == '\n' and text[start - 2:start] == '\n\n':
            end += 1                                   # do not leave two blank lines behind
        text = text[:start] + text[end:]


def inline_macro_uses(text, macros):
    """Each use of a macro name ({name: body}) replaced by `(body)`."""
    for name, body in macros.items():
        text = re.sub(r"(?<![\w.'])%s(?![\w'!?])" % re.escape(name), lambda _, b=body: '(%s)' % b, text)
    return text


def inline_tactic_macros(text):
    """(text, [names]): every `macro "name" : tactic => `(tactic| body)` removed (tactic_macros)
    and each use of `name` replaced by `(body)`. The verifier rejects all macro registration (CFP
    §6's `grp`, Lodha-Moore's `gp`, both merged in from development modules); a solution must
    inline them. The module route (oaiport.module_texts) inlines across modules the same way."""
    text, macros = tactic_macros(text)
    return inline_macro_uses(text, macros), list(macros)


def code_only(text):
    """`text` with every comment and literal (string, char, raw string, «name») blanked to spaces,
    newlines kept, so offsets and line numbers still match the source."""
    out, i, n = [], 0, len(text)

    def blank(j):
        out.append(re.sub(r'[^\n]', ' ', text[i:j]))
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
            blank(j); i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j == -1 else j
            blank(j); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            blank(j); i = j
        elif text[i] == '«':
            j = text.find('»', i)
            j = n if j == -1 else j + 1
            blank(j); i = j
        elif text[i] == 'r' and not ident_before and _RAW.match(text, i):
            close = '"' + _RAW.match(text, i).group(1)
            j = text.find(close, _RAW.match(text, i).end())
            j = n if j == -1 else j + len(close)
            blank(j); i = j
        elif text[i] == "'" and not ident_before and _CHARLIT.match(text, i):
            j = _CHARLIT.match(text, i).end()
            blank(j); i = j
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


# What prove2.me's soundness guard refuses in any submitted file (solution, statement, bundle):
# custom syntax/elaborator registration ("line N: `macro` ... metaprogramming is not supported in
# submissions"; CFP §6's `local macro "grp"`), and the token `prelude` anywhere, even as an
# identifier (WLTime 2026-10-23: OpenAI's `def prelude` in a bundle, "`prelude` — disables the
# automatic Init prelude import, enabling kernel-primitive shadowing"). `notation` is allowed.
GUARD_COMMAND = re.compile(r'[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:local|scoped)\s+)?'
                           r'(macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|initialize)\b')
GUARD_TOKENS = {'prelude': 'disables the automatic Init prelude import (refused even as an identifier)',
                'initialize': 'arbitrary code execution at module initialization (refused even as an identifier or a field)'}
_TOKEN = r"(?<![\w'!?₀-ₜ])%s(?![\w'!?₀-ₜ])"


def guard_problems(text):
    """[(line, token, why)] of what the soundness guard refuses, read outside comments and
    literals: a metaprogramming command at the start of a line, a refused token anywhere."""
    out = []
    for k, l in enumerate(code_only(text).split('\n'), 1):
        m = GUARD_COMMAND.match(l)
        if m:
            out.append((k, m.group(1), 'metaprogramming is not supported in submissions'))
        for tok, why in GUARD_TOKENS.items():
            if re.search(_TOKEN % re.escape(tok), l):
                out.append((k, tok, why))
    return out


def guard_message(problems, limit=5):
    return '; '.join('line %d: `%s` (%s)' % p for p in problems[:limit]) + \
        (' (and %d more)' % (len(problems) - limit) if len(problems) > limit else '')
