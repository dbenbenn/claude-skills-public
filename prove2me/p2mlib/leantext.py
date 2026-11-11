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


_HEADER_LINE = re.compile(r'(?:prelude|module|(?:public\s+)?(?:meta\s+)?import)\b[^\n]*')


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


def _remove_command(text, start, end):
    """text without text[start:end] (whole lines), with the doc comment right above it, leaving no
    run of two blank lines behind."""
    d = _DOC_BEFORE.search(text[:start][-20000:])
    if d:
        start -= len(text[:start][-20000:]) - d.start()
    while text[end:end + 1] == '\n' and text[start - 2:start] == '\n\n':
        end += 1                                   # do not leave two blank lines behind
    return text[:start] + text[end:]


def _quotation_end(text, i):
    """Index after the `)` closing a `(tactic| …` quotation whose body starts at i."""
    depth = 1
    while i < len(text) and depth:
        depth += {'(': 1, ')': -1}.get(text[i], 0)
        i += 1
    return i


_SYNTAX_TACTIC = re.compile(r'^[ \t]*(?:(?:local|scoped)[ \t]+)?syntax[ \t]+"([A-Za-z_]\w*)"[ \t]*:[ \t]*tactic'
                            r'[ \t]*(?:--[^\n]*)?(?:\n|$)', re.M)


def _macro_rules_of(name):
    return re.compile(r'^[ \t]*(?:(?:local|scoped)[ \t]+)?macro_rules\b[ \t]*(?:\([^()\n]*\)[ \t]*)?\s*\|[ \t]*'
                      r'`\(tactic\|[ \t]*%s[ \t]*\)[ \t]*=>\s*`\(tactic\|' % re.escape(name), re.M)


def tactic_macros(text):
    """(text, {name: body}): every `macro "name" : tactic => `(tactic| body)` removed, with the doc
    comment right above it (left behind, it dangles before the next command: WLIdentification
    2026-10-23), and its body, whitespace-normalized. Uses are not touched (inline_macro_uses).

    Likewise a `syntax "name" : tactic` with one `macro_rules | `(tactic| name) => `(tactic| body)`
    in the same text (q222, q241: carve.py gen refused the `syntax` command after the whole build).
    Its body may call `name` itself: close_tactic_macros flattens that. A `syntax` with several
    arms or `macro_rules` blocks (Lean tries them all, backtracking) is left, with a warning."""
    import warnings
    macros = {}
    while True:
        m = _TACTIC_MACRO.search(text)
        if not m:
            break
        i = _quotation_end(text, m.end())
        macros[m.group(1)] = ' '.join(text[m.end():i - 1].split())
        end = text.find('\n', i)
        text = _remove_command(text, m.start(), len(text) if end < 0 else end + 1)
    pos = 0
    while True:
        s = _SYNTAX_TACTIC.search(text, pos)
        if not s:
            return text, macros
        name = s.group(1)
        rules = list(_macro_rules_of(name).finditer(text))
        blocks = len(re.findall(r'^[ \t]*(?:(?:local|scoped)[ \t]+)?macro_rules\b[^\n]*\n?(?:[ \t]*\n)*[ \t]*\|[ \t]*'
                                r'`\(tactic\|[ \t]*%s\b' % re.escape(name), text, re.M))
        if len(rules) == 1 and blocks == 1:
            r = rules[0]
            i = _quotation_end(text, r.end())
            end = text.find('\n', i)
            end = len(text) if end < 0 else end + 1
            rest = text[i:end].strip()
            nxt = text[end:].lstrip()
            if (not rest or rest.startswith('--')) and not nxt.startswith('|') and r.start() > s.start():
                macros[name] = ' '.join(text[r.end():i - 1].split())
                text = _remove_command(text, r.start(), end)
                text = _remove_command(text, s.start(), s.end())
                continue
        if rules or blocks:
            warnings.warn('tactic `%s`: a `syntax` with %d `macro_rules` arm(s) the port does not read (several arms, '
                          'or arguments): it is left in place, and carve.py gen will refuse it; expand it by a port '
                          'patch' % (name, max(len(rules), blocks)), stacklevel=2)
        pos = s.end()


_WRAPPERS = r'(?:(?:with_reducible_and_instances|with_reducible|with_unfolding_all)\s+)*'


def _uses(name):
    return re.compile(r"(?<![\w.'])%s(?![\w'!?])" % re.escape(name))


def _top_bars(s):
    """s split at its top-level `|` (outside brackets; not `<|`, `|>`, `||`)."""
    parts, depth, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        if (c == '|' and depth == 0 and s[i - 1:i] not in ('<', '|') and s[i + 1:i + 2] not in ('>', '|')):
            parts.append(cur)
            cur = ''
        else:
            cur += c
        i += 1
    return parts + [cur]


def _unparen(a):
    a = a.strip()
    while a.startswith('(') and _quotation_end(a, 1) == len(a):
        a = a[1:-1].strip()
    return a


def close_tactic_macros(macros):
    """{name: body} with every macro call in a body expanded: {name: closed body, or None where that
    cannot be done}. A macro that does not reach itself through calls is plain substitution.

    A recursive one (q222's `poly_bound`, q241's `bit_linear`) must be a `[with_reducible…] first | …`
    whose alternatives call recursive macros only as their last step (`(apply A <;> x)`, `(apply A;
    x)`, `apply A <;> x`). It becomes `repeat' (WRAP first | alts)`: the call is dropped from each
    alternative (`apply A`), and the alternatives of every recursive macro it tail-calls follow its
    own, each once, in source order (q222 unioned `poly_emit` with `rat_emit` by hand). WRAP is the
    macro's own wrapper.

    What is lost, so a use can need a port patch:
    * backtracking. The macro retried the next alternative when a recursive call failed further down;
      `repeat'` commits to the first alternative that applies. q222 had to put `apply PolyBound.mul`
      before `apply PolyBound.add` (a goal `Nat.mul a (b+35)` unifies with `x + y` by Nat offset
      unification). The port keeps the source order: it cannot know which order the goals need.
    * failure. The macro failed where it could not close the goal; `repeat'` succeeds and leaves the
      goals it could not close, so a use under `first | … ` or `try` means something else.
    * `;` versus `<;>`: `(apply A; x)` recursed on the first new goal only; `repeat'` works on all.
    * a union of macros applies all their alternatives to every goal, also those of the other family."""
    import warnings
    calls = {n: [m for m in macros if _uses(m).search(b)] for n, b in macros.items()}

    def reach(n):
        seen, todo = [], list(calls[n])
        while todo:
            m = todo.pop(0)
            if m not in seen:
                seen.append(m)
                todo += calls[m]
        return seen

    recursive = {n for n in macros if n in reach(n)}
    closed = {}

    def close(n):
        if n in closed:
            return closed[n]
        if n not in recursive:
            b = macros[n]
            for m in calls[n]:
                c = close(m)
                if c is None:
                    closed[n] = None
                    return None
                b = _uses(m).sub(lambda _, c=c: '(%s)' % c, b)
            closed[n] = b
            return b
        closed[n] = None                      # until done: a cycle through n is not expanded twice
        m0 = re.fullmatch(r'(%s)first\s*\|(.*)' % _WRAPPERS, macros[n], re.S)
        if not m0:
            warnings.warn('tactic `%s` calls itself but is not a `first | …`: expand it by hand (a port patch '
                          'at each use)' % n, stacklevel=3)
            return None
        wrap, order, alts, i = m0.group(1), [n], [], 0
        while i < len(order):
            body = re.fullmatch(r'(%s)first\s*\|(.*)' % _WRAPPERS, macros[order[i]], re.S)
            if not body:
                warnings.warn('tactic `%s` (called by `%s`) is not a `first | …`: expand it by hand (a port patch '
                              'at each use)' % (order[i], n), stacklevel=3)
                return None
            for a in _top_bars(body.group(2)):
                a = _unparen(a)
                t = re.fullmatch(r'(.*?)\s*(?:<;>|;)\s*\(?\s*([A-Za-z_]\w*)\s*\)?', a, re.S)
                if t and t.group(2) in recursive:
                    a = _unparen(t.group(1))
                    if t.group(2) not in order:
                        order.append(t.group(2))
                for m in calls[order[i]]:
                    if not _uses(m).search(a):
                        continue
                    if m in recursive:
                        warnings.warn('tactic `%s` calls `%s` other than as the last step of an alternative '
                                      '(`%s`): no `repeat\'` form; expand it by hand (a port patch at each use)'
                                      % (n, m, a), stacklevel=3)
                        return None
                    c = close(m)
                    if c is None:
                        return None
                    a = _uses(m).sub(lambda _, c=c: '(%s)' % c, a)
                if a and a not in alts:
                    alts.append(a)
            i += 1
        closed[n] = "repeat' (%sfirst | %s)" % (wrap, ' | '.join(alts))
        return closed[n]

    for n in macros:
        close(n)
    return closed


def inline_macro_uses(text, macros):
    """Each use of a macro name ({name: body}) replaced by `(body)`, calls inside bodies expanded first
    (close_tactic_macros); a macro that cannot be closed keeps its uses as written."""
    for name, body in close_tactic_macros(macros).items():
        if body is not None:
            text = _uses(name).sub(lambda _, b=body: '(%s)' % b, text)
    return text


def inline_tactic_macros(text):
    """(text, [names]): every `macro "name" : tactic => `(tactic| body)` (and `syntax` + `macro_rules`
    tactic) removed (tactic_macros) and each use of `name` replaced by `(body)`. The verifier rejects
    all macro registration (CFP §6's `grp`, Lodha-Moore's `gp`, both merged in from development
    modules); a solution must inline them. The module route (oaiport.module_texts) inlines across
    modules the same way."""
    text, macros = tactic_macros(text)
    return inline_macro_uses(text, macros), list(macros)


IMPORT_RE = re.compile(r"^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)", re.M)


def import_names(text):
    """The modules `text` imports, in order, module-system forms included (`public import`, `meta import`,
    `import all M` is M)."""
    return IMPORT_RE.findall(text)


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
                           r'(macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|initialize|run_cmd|run_elab|run_meta)\b')
GUARD_TOKENS = {'prelude': 'disables the automatic Init prelude import (refused even as an identifier)',
                'initialize': 'arbitrary code execution at module initialization (refused even as an identifier or a field)'}
# q151 (2026-11-02): "`TermElabM` -- metaprogramming monad -- not supported in submissions" on a bundle
# that kept an elaborator's helper defs; TacticM and MetaM are the same kind (not yet seen refused)
GUARD_TOKENS.update({m: 'metaprogramming monad' for m in ('TermElabM', 'TacticM', 'MetaM')})
GUARD_TOKENS['modifyEnv'] = 'mutates the elaboration environment'   # q151, with `run_cmd`
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
