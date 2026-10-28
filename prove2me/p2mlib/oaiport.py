"""Porting an openai/math result to prove2.me: the text transformations shared by the single-file
route (scripts/oai_port.py) and the module route (scripts/oai_port_modules.py, then carve.py).

Every function here pins a behaviour that went wrong on a live port (2026-10-18):
* `bundle_decl_names` / `drop_declarations`: what a published Definitions bundle declares is dropped
  from the port by FULL name, namespace by namespace, never by last component (Grothendieck: the
  bundle's `Hom.id` took OpenAI's own GlobularSet.Hom.id); named instances with a priority,
  `local`/`scoped` instances, and anonymous instances (matched by namespace and header) included
  (DirectionalZeroOne: a kept anonymous `MeasurableSpace (Row d)` became a second instance); a
  dropped declaration takes its `… in` modifiers along (BassTrace: a dangling one hit `end K0`).
* `rename_target`: OpenAI's copy of the target becomes `<name>_oai`, and only the uses that mean it
  (Superstring's field `main`, GeneralizedStarHeight's `main j := …`, SingleFold's `| main`).
* `apply_patches`: each patch applies exactly its `count` times (default 1), every mismatch reported.
* `compat_block`: the compatibility lemmas (names newer Lean/Mathlib has) inside a namespace, so two
  bundles never both declare root `ite_eq_left`; an `alias X := Y` becomes a rewrite of the sources
  (inside the namespace it would create OAI.Finset and shadow Mathlib's in `open Finset`,
  CPTSeparation).
* `classify_attempt` / `state_from_log`: the submit queue rebuilds each goal from its log, so a
  restart neither repeats nor loses an attempt.
"""
import os
import re


class PortError(Exception):
    pass


MODS = r'(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*'
HEAD = re.compile(r'^(?P<attr>(?:@\[[^\]]*\]\s*)*)(?P<mods>%s)'
                  r'(?P<kind>def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque|axiom)\b'
                  r'(?P<rest>.*)$' % MODS)
SEG = r'(?:«[^»]+»|[^\W\d][\w\'!?₀-ₜ]*)'
IDENT = re.compile(r'(%s(?:\.%s)*(?:\.\{[^}]*\})?)' % (SEG, SEG))
PRIORITY = re.compile(r'\s*\(\s*priority\s*:=[^)]*\)')
# anything that starts a new top-level command ends the declaration above it
TOP = re.compile(r'^(?:@\[|/--|/-!|(?:private|protected|noncomputable|partial|unsafe|local|scoped)\b|'
                 r'(?:def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque|axiom|example)\b|'
                 r'end\b|namespace\b|section\b|open\b|variable\b|universe\b|attribute\b|set_option\b|'
                 r'mutual\b|omit\b|include\b|notation\b|infix[lr]?\b|prefix\b|postfix\b|macro\b|'
                 r'macro_rules\b|syntax\b|elab\b|#)')
# one-command modifiers on the lines above a declaration
MODIFIER = re.compile(r'\s*(attribute\s*\[[^\]]*\]|(omit|include|open|set_option)\b).*\bin\s*$')


def ns_by_line(lines):
    """The namespace in force at each line; `noncomputable section` and named sections included."""
    stack, out = [], []
    for l in lines:
        out.append('.'.join(n for kd, n in stack if kd == 'ns'))
        m = re.match(r'^\s*(?:noncomputable\s+)?(namespace|section|end)\b\s*(\S*)', l)
        if not m:
            continue
        if m.group(1) == 'namespace':
            stack += [('ns', q) for q in m.group(2).split('.')]
        elif m.group(1) == 'section':
            stack.append(('sec', m.group(2)))
        elif stack:
            for _ in range(m.group(2).count('.') + 1 if m.group(2) else 1):
                if stack:
                    stack.pop()
    return out


def _head_name(m):
    """The declared name of a HEAD match, or None for an anonymous instance."""
    rest = m.group('rest')
    if m.group('kind') == 'instance':
        p = PRIORITY.match(rest)
        if p:
            rest = rest[p.end():]
    r = rest.lstrip()
    if not r or r[0] in '([{⦃:' or r.startswith('where'):
        return None
    n = IDENT.match(r)
    return re.sub(r'\.\{[^}]*\}$', '', n.group(1)) if n else None


def _full(ns, name):
    if name.startswith('_root_.'):
        return name[len('_root_.'):]
    return '.'.join(x for x in (ns, name) if x)


def anon_header(text_from_kind):
    """An anonymous instance's header, whitespace-normalized: from `instance` up to `:=`/`where`."""
    t = ' '.join(text_from_kind.split())
    m = re.search(r'\s(:=|where)(\s|$)', t)
    t = t[:m.start()] if m else t
    return PRIORITY.sub('', t).replace('instance  ', 'instance ').strip()


def declarations(lines):
    """[(full name or None, anonymous header or None, start, end)] of the top-level declarations:
    `start` takes the doc comment and attribute lines above, `end` stops before the next command."""
    nsl = ns_by_line(lines)
    out = []
    for i, l in enumerate(lines):
        m = HEAD.match(l)
        if not m:
            continue
        j = i + 1
        while j < len(lines) and not TOP.match(lines[j]):
            j += 1
        while j - 1 > i and lines[j - 1].strip() == '':
            j -= 1
        s = i
        while s > 0:
            prev = lines[s - 1].rstrip()
            if prev.endswith('-/'):
                d = s - 1
                while d >= 0 and not lines[d].lstrip().startswith(('/--', '/-!', '/-')):
                    d -= 1
                if d >= 0 and lines[d].lstrip().startswith('/--'):
                    s = d
                    continue
                break
            if prev.lstrip().startswith('@[') and not HEAD.match(prev):
                s -= 1
                continue
            break
        name = _head_name(m)
        if name is None:
            body = '\n'.join(lines[i:j])
            k = body.index(m.group('kind'), len(m.group('attr')) + len(m.group('mods')))
            out.append((None, anon_header(body[k:]), s, j, nsl[i]))
        else:
            out.append((_full(nsl[i], name), None, s, j, nsl[i]))
    return out


def bundle_decl_names(text):
    """(full names, {(namespace, anonymous instance header)}) a bundle declares."""
    names, anon = set(), set()
    for full, header, _s, _e, ns in declarations(text.split('\n')):
        if full:
            names.add(full)
        else:
            anon.add((ns, header))
    return names, anon


def drop_declarations(text, names, anon=()):
    """The text without the declarations named in `names` (full names) or matching `anon`
    ({(namespace, header)}), each with its one-command modifiers; and the list of what went."""
    lines = text.split('\n')
    anon = set(anon)
    spans, dropped = [], []
    for full, header, s, e, ns in declarations(lines):
        if (full and full in names) or (header is not None and (ns, header) in anon):
            while s > 0 and MODIFIER.match(lines[s - 1]):
                s -= 1
            spans.append((s, e))
            dropped.append(full or 'instance %s.%s' % (ns, header))
    for s, e in sorted(set(spans), reverse=True):
        del lines[s:e]
    return '\n'.join(lines), dropped


def strip_declared_universes(text):
    """Drop `.{u, v}` lists from declaration heads when every listed universe is declared by a
    `universe` line (merge.py declares them once at the top; Grothendieck "already declared")."""
    declared = set(u for l in text.split('\n') if l.startswith('universe ') for u in l.split()[1:])

    def strip(m):
        us = [u.strip() for u in m.group(3).split(',')]
        return m.group(1) + m.group(2) if us and all(u in declared for u in us) else m.group(0)
    return re.sub(r'^((?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*'
                  r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+)(\S+?)\.\{([^}]*)\}',
                  strip, text, flags=re.M)


def rename_target(text, target, suffix='_oai'):
    """OpenAI's copy of `target` (full name) renamed `<short><suffix>`, with the uses that mean it:
    qualified names ending in `<a suffix of its namespace>.<short>`, and the bare short name inside
    its namespace, except a structure field `short : T`, an assignment `short … := …`, a constructor
    or case `| short`, and field access `x.short`."""
    short = target.rsplit('.', 1)[1]
    ns = target.rsplit('.', 1)[0] if '.' in target else ''
    lines = text.split('\n')
    nsl = ns_by_line(lines)
    hits = []
    for k, l in enumerate(lines):
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)', l)
        if m and _full(nsl[k], re.sub(r'\.\{[^}]*\}$', '', m.group(2))) == target:
            hits.append(k)
    if len(hits) != 1:
        raise PortError('expected exactly one declaration of %s, found %d' % (target, len(hits)))
    k0 = hits[0]
    lines[k0] = re.sub(r'(theorem|lemma)\s+(\S*?)%s\b' % re.escape(short),
                       lambda m: m.group(1) + ' ' + m.group(2) + short + suffix, lines[k0], count=1)
    parts = ns.split('.') if ns else []
    quals = ['.'.join(parts[a:]) + '.' + short for a in range(len(parts))]
    spare = re.compile(r'\s+%s\s*:(?!=)|\s*%s(\s+[^:=]+)?\s*:=|\s*\|\s*%s\b' % ((re.escape(short),) * 3))
    for k, l in enumerate(lines):
        if k == k0:
            continue
        for qn in quals:
            l = re.sub(r'(?<![\w.])%s(?![\w\'])' % re.escape(qn), qn + suffix, l)
        if (nsl[k] == ns or nsl[k].startswith(ns + '.')) and not spare.match(l):
            l = re.sub(r'(?<![\w.])%s(?![\w\'])(?!\s*:=)' % re.escape(short), short + suffix, l)
        lines[k] = l
    return '\n'.join(lines)


def _univ_norm(s):
    return re.sub(r'\.\{([^}]*)\}', lambda m: '.{%s}' % ','.join(sorted(x.strip() for x in m.group(1).split(','))), s)


def single_file_only(p):
    """Is patch p for the single-file route only? Marked `"route": "single"`, or a reordering of a
    universe list (`X.{uA, uB}` -> `X.{uB, uA}`): merge.py's one top-level `universe` line orders a
    declaration's universe parameters there, while a module's own `universe` line rules a module
    (WLTime 2026-10-23: two such patches matched in the modules and broke the build)."""
    if p.get('route') == 'single':
        return True
    return p['old'] != p['new'] and _univ_norm(p['old']) == _univ_norm(p['new'])


def applies_to(p, route):
    """Does patch p apply on `route` ('single', 'modules' or None for any)? A patch's optional
    `route` key says where it belongs; a universe reordering is single-file only."""
    if route is None:
        return True
    if route == 'modules':
        return not single_file_only(p)
    return p.get('route', route) == route


def apply_patches(files, patches, route=None):
    """`files` ({path: text}, or one text) with each patch {old, new, count=1} applied in order;
    each must occur exactly `count` times over all files as the earlier patches left them (a later
    patch may amend an earlier one's output), and every one that does not is reported. With
    `route` ('single' or 'modules'), patches for the other route are skipped (applies_to)."""
    single = isinstance(files, str)
    files = {'': files} if single else dict(files)
    bad = []
    for p in patches:
        if not applies_to(p, route):
            continue
        n = sum(t.count(p['old']) for t in files.values())
        if n != p.get('count', 1):
            bad.append('patch applies %d times, want %d: %r' % (n, p.get('count', 1), p['old'][:100]))
            continue
        for f in files:
            files[f] = files[f].replace(p['old'], p['new'])
    if bad:
        raise PortError('\n'.join(bad))
    return files[''] if single else files


def compat_block(text, namespace='OAI'):
    """The compatibility block, inside `namespace` (default OAI: every ported module lives in it),
    and {alias name: target} rewrites for the sources. namespace=None returns the root-level text
    unchanged (the old behaviour: root `ite_eq_left` in every bundle that keeps it clashed)."""
    if namespace is None:
        return text, {}
    rewrites, keep = {}, []
    for l in text.split('\n'):
        m = re.match(r'^alias\s+(\S+)\s*:=\s*(\S+)\s*$', l)
        if m:
            rewrites[m.group(1)] = m.group(2)
        else:
            keep.append(l)
    return 'namespace %s\n\n%s\n\nend %s\n' % (namespace, '\n'.join(keep).strip('\n'), namespace), rewrites


def apply_rewrites(text, rewrites):
    """Each whole name X of `rewrites` replaced by its target (not inside a longer name). When the
    text opens X's namespace (`open Finset`, `open Finset in`) and the target lives in the same
    namespace, the bare last component is rewritten too (`prod_le_prod₀` -> `prod_le_prod`)."""
    for old, new in rewrites.items():
        text = re.sub(r'(?<![\w.\'])%s(?![\w\'₀-ₜ])' % re.escape(old), new, text)
        if '.' in old:
            ns, short = old.rsplit('.', 1)
            if new.startswith(ns + '.') and re.search(r'^\s*open\b[^\n]*(?<![\w.])%s(?![\w.])' % re.escape(ns), text, re.M):
                text = re.sub(r'(?<![\w.\'])%s(?![\w\'₀-ₜ])' % re.escape(short), new[len(ns) + 1:], text)
    return text


# identifiers prove2.me's soundness guard refuses (leantext.GUARD_TOKENS), and what the ports call
# them instead (WLTime 2026-10-23: OpenAI's `def prelude`, renamed by hand to preludeCode)
GUARD_RENAMES = {'prelude': 'prelude_', 'initialize': 'initialize_'}


def guard_renames(text):
    """Every identifier token the soundness guard refuses renamed (GUARD_RENAMES), qualified uses
    (`X.prelude`) included, longer names (`prelude_size`) not; comments too, harmlessly."""
    for old, new in GUARD_RENAMES.items():
        text = re.sub(r"(?<![\w'!?\u2080-\u209c])%s(?![\w'!?\u2080-\u209c])" % re.escape(old), new, text)
    return text


def split_partial_namespaces(text):
    """`namespace A.B` that a shorter `end B` closes becomes `namespace A` + `namespace B` (same meaning;
    the carver's scope mirror counts a dotted namespace as one scope). Others are left alone."""
    lines = text.split('\n')
    stack = []                                     # (kind, name, line index)
    split = []
    for i, l in enumerate(lines):
        m = re.match(r'namespace\s+(\S+)\s*$', l)
        if m:
            stack.append(('ns', m.group(1), i)); continue
        if re.match(r'(?:noncomputable\s+)?section(?:\s+\S+)?\s*$', l):
            stack.append(('sec', None, i)); continue
        m = re.match(r'end(?:\s+(\S+))?\s*$', l)
        if m and stack:
            k, n, j = stack.pop()
            if k == 'ns' and m.group(1) and m.group(1) != n and n.endswith('.' + m.group(1)):
                split.append((j, n, m.group(1)))
    for j, n, short in split:
        head = n[:-len(short) - 1]
        lines[j] = 'namespace %s\nnamespace %s' % (head, short)
    return '\n'.join(lines)


def _drop_positional_arg(text, name):
    """Drop the first positional argument after `name` (a balanced `( ... )` group or a plain term),
    skipping named arguments `(x := ...)`. A use with no argument is left alone."""
    out, i = [], 0
    pat = re.compile(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])")
    while True:
        m = pat.search(text, i)
        if not m:
            out.append(text[i:])
            return ''.join(out)
        j = m.end()
        out.append(text[i:j])
        i = j
        k = j
        while True:
            m2 = re.compile(r"\s+").match(text, k)
            q = m2.end() if m2 else k
            if m2 is None or q >= len(text):
                break
            if text[q] == '(':
                depth, r = 0, q
                while r < len(text):
                    depth += (text[r] == '(') - (text[r] == ')')
                    r += 1
                    if depth == 0:
                        break
                if re.match(r"\(\w+ :=", text[q:]):
                    out.append(text[i:r])
                    i = k = r
                    continue
                i = r + len(re.compile(r"(?:\.[\w']+)*").match(text, r).group(0))   # `(h x).foo` is one argument
                break
            m3 = re.compile(r"[\w.']+").match(text, q)
            if m3 and not text[q:].startswith('<|') and m3.group(0) not in ('at', 'with', 'using', 'from', 'only'):
                i = m3.end()
            break



# The tactic that proves `AEMeasurable f μ` at a site the port rewrites for our non-total `Measure.map`.
# fun_prop first (it uses hypotheses too, but not a named lemma, a `∀ i, Measurable (c i)` hypothesis, a
# Continuous / MeasurePreserving hypothesis used as AEMeasurable), then the context, then measurability.
# oaiq-005 fixed about 50 such sites by hand; macros are rejected by the verifier, so the text is inlined.
AEM_TAC = ("first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) "
           "| (apply Continuous.aemeasurable; solve_by_elim) "
           "| (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) "
           "| (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) "
           "| exact (continuous_eval_const _).aemeasurable "
           "| (apply Measurable.aemeasurable; measurability) | measurability")
# `infer_instance` with its own synthesis budget. Port patches raise `synthInstance.maxHeartbeats` module-wide
# (to 200000, a whole declaration's budget), and a failing search then used up the declaration before the next
# alternative ran (HardSphere oaiq-054, SKGap oaiq-072); a search that runs out of its own budget fails like
# any other, and `first` goes on.
_BOUNDED_INFER = "(set_option synthInstance.maxHeartbeats 20000 in infer_instance)"


def _aem_tac(named=()):
    """AEM_TAC with the named measurability facts (_aem_named) tried first."""
    return 'first | %s | %s' % (' | '.join(named), AEM_TAC[len('first | '):]) if named else AEM_TAC


def _pm_fallback(named=()):
    """The chain that proves `IsProbabilityMeasure (μ.map f)`: the named measurability facts the text shows for
    `f` (_aem_named) first, then instance search on its own budget, then AEM_TAC (oaiq-054/061/071/072: the
    chain timed out or hit maxRecDepth where a hypothesis `hφ : Measurable φ` or a lemma `foo_measurable`
    closed the goal at once)."""
    first = ('exact Measure.isProbabilityMeasure_map (by first | %s) | ' % ' | '.join(named)) if named else ''
    return 'first | %s%s | exact Measure.isProbabilityMeasure_map (by %s)' % (first, _BOUNDED_INFER, AEM_TAC)


_PM_FALLBACK = _pm_fallback()


_PM_CONTEXT = re.compile(r"ProbabilityMeasure|\.map\b")
# a function argument: a balanced group (three levels) or a name
_ARG = r"(?:\((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*\)|[^\W\d][\w.']*)"
_MAP_FN = re.compile(r"\.map[ \t\n]+(" + _ARG + ")")
_DEF_HEAD = re.compile(r"(?m)^(?:@\[[^\n]*\][ \t]*\n?)?" + MODS + r"(?:def|abbrev)[ \t]+([^\s(:{\[]+)")
_LEMMA_HEAD = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*\n?[ \t]*)?" + MODS + r"(?:theorem|lemma)[ \t]+([^\s(:{\[]+)")
_PRED = r"(Measurable|AEMeasurable|Continuous|LipschitzWith[ \t]+[\w.']+|MeasurePreserving)"
_HYP_BINDER = re.compile(r"[({][ \t]*([\w'][\w' \t]*?)[ \t]*:[ \t]*" + _PRED + r"[ \t]+(" + _ARG + ")")
_HYP_HAVE = re.compile(r"\b(?:have|haveI)[ \t]+([\w']+)[ \t]*:[ \t]*" + _PRED + r"[ \t]+(" + _ARG + ")")
_HYP_FORALL = re.compile(r"[({][ \t]*([\w']+)[ \t]*:[ \t]*∀[ \t]*\(?([\w']+)(?:[ \t]*:[^,()]+)?\)?[ \t]*,[ \t]*"
                         r"(Measurable|Continuous)[ \t]+\(([^\W\d][\w.']*)[ \t]+\2\)")
_HYP_TERM = {'Measurable': '%s.aemeasurable', 'AEMeasurable': '%s', 'Continuous': '%s.measurable.aemeasurable',
             'LipschitzWith': '%s.continuous.measurable.aemeasurable',
             'MeasurePreserving': '%s.measurable.aemeasurable'}
_LEMMA_TAC = {'M': '(apply Measurable.aemeasurable; apply %s <;> assumption)',
              'C': '(apply Continuous.aemeasurable; apply %s <;> assumption)', 'A': '(apply %s <;> assumption)'}


def declared_lemmas(texts):
    """The theorem/lemma names the texts declare, as written and by last component (for _aem_named: in the
    module route the measurability lemma of a map often sits in a sibling module)."""
    out = set()
    for t in texts:
        for m in _LEMMA_HEAD.finditer(t):
            n = m.group(1).replace('_root_.', '')
            out.update((n, n.rsplit('.', 1)[-1]))
    return frozenset(out)


def _def_bodies(text):
    """{last component of each def/abbrev name: its text up to the next unindented line}."""
    out = {}
    for m in _DEF_HEAD.finditer(text):
        e = re.compile(r"\n(?=\S)").search(text, m.end())
        out.setdefault(m.group(1).rsplit('.', 1)[-1], text[m.start():e.start() if e else len(text)][:4000])
    return out


def _decl_start(text, pos):
    """Start of the declaration around pos: the nearest line above that starts in column 0."""
    s = text.rfind('\n', 0, pos) + 1
    while s > 0 and (text[s:s + 1] in (' ', '\t', '\n', '') or text.startswith(('--', '/-'), s)):
        s = text.rfind('\n', 0, s - 1) + 1
    return s


def _norm_term(s):
    s = re.sub(r"\s+", ' ', s.strip())
    while s.startswith('(') and _balanced_end(s, 0) == len(s):
        s = s[1:-1].strip()
    return s


def _lets(decl):
    """{name: right-hand side} of the `let`s (and `set`s) in a declaration's text."""
    out = {}
    for m in re.finditer(r"(?m)^[ \t]*(?:let|set)[ \t]+([\w']+)(?:[ \t]*:[^\n=]*)?[ \t]*:=[ \t]*([^\n]+|\n[^\n]*)", decl):
        out[m.group(1)] = m.group(2)
    return out


def _site_maps(window, decl, defs):
    """The functions mapped in `window` (`….map F`), also through the `let`s of the declaration and the
    module's defs whose names `window` mentions (`unfold midpointLaw`, `IsProbabilityMeasure ν'`)."""
    fns = [m.group(1) for m in _MAP_FN.finditer(window)]
    lets = _lets(decl)
    for t in dict.fromkeys(re.findall(r"[^\W\d][\w.']*", window)):
        body = lets.get(t)
        if body is None:
            body = defs.get(t.rsplit('.', 1)[-1])
        if body:
            fns += [m.group(1) for m in _MAP_FN.finditer(body)]
    return [f for f in dict.fromkeys(fns) if not re.match(r"\(\s*[\w']+\s*:=", f)]


def _aem_named(fns, decl, lemmas):
    """Tactics that prove `AEMeasurable F _` for a mapped function F from a named fact, cheapest first:
    a hypothesis of the declaration about F itself (`hφ : Measurable φ`, `(hf : LipschitzWith K f)`, `(hF : ∀ n,
    Measurable (F n))` for `F n`), then a lemma the port declares for F's head (`foo_measurable`,
    `measurable_foo`, `foo_continuous`, `continuous_foo`, `…aemeasurable`), applied so that its arguments
    come from unification (oaiq-054, 061, 071, 072). At most six."""
    alts = []
    nf = [_norm_term(f) for f in fns]
    for rx in (_HYP_BINDER, _HYP_HAVE):
        for m in rx.finditer(decl):
            if _norm_term(m.group(3)) in nf:
                for n in m.group(1).split():
                    alts.append('exact ' + _HYP_TERM[m.group(2).split()[0]] % n)
    for m in _HYP_FORALL.finditer(decl):
        for f in nf:
            a = re.fullmatch(re.escape(m.group(4)) + r" (" + _ARG + ")", f)
            if a:
                alts.append('exact ' + _HYP_TERM[m.group(3)] % '(%s %s)' % (m.group(1), a.group(1)))
    for f in nf:
        h = re.match(r"[^\W\d][\w.']*", f)
        if not h or h.group(0) in ('fun', 'λ'):
            continue
        pre, _, c = h.group(0).rpartition('.')
        pre = pre + '.' if pre else ''
        for name, kind in ((c + '_measurable', 'M'), ('measurable_' + c, 'M'), (c + '_continuous', 'C'),
                           ('continuous_' + c, 'C'), (c + '_aemeasurable', 'A'), ('aemeasurable_' + c, 'A')):
            if name in lemmas or pre + name in lemmas:
                alts.append(_LEMMA_TAC[kind] % (pre + name))
    return list(dict.fromkeys(alts))[:6]


def _instance_context(text, pos):
    """What says which instance the term at `pos` must be, as far as the text shows: the line up to `pos`,
    each line above with less indentation than every line between (the enclosing `have … :`, `refine ⟨`,
    bullets), each with its continuation up to its `:=`, and the statement of the declaration (the first
    unindented line above, up to its `:=`)."""
    lines = text[:pos].split('\n')
    out = [lines[-1]]
    ind = lambda l: len(l) - len(l.lstrip(' \t'))
    low = ind(lines[-1])
    for j in range(len(lines) - 2, -1, -1):
        l = lines[j]
        if not l.strip() or l.lstrip().startswith(('--', '/-')):
            continue
        if ind(l) < low:
            low = ind(l)
            k = j
            seg = [l]
            while ':=' not in seg[-1] and k + 1 < len(lines) - 1 and ind(lines[k + 1]) > low:
                k += 1
                seg.append(lines[k])
            out.append('\n'.join(seg).split(':=')[0])
            if low == 0:
                break
    return '\n'.join(out)


def _lines_before(text, pos, n=3):
    """Up to n non-blank lines above pos's line with its indentation (the `unfold foo` before a lone
    `infer_instance`)."""
    ls = text[:text.rfind('\n', 0, pos) + 1].split('\n')[:-1]
    cur = text[text.rfind('\n', 0, pos) + 1:pos]
    ind = len(cur) - len(cur.lstrip(' \t'))
    out = []
    for l in reversed(ls):
        if not l.strip():
            continue
        if len(l) - len(l.lstrip(' \t')) != ind or len(out) == n:
            break
        out.append(l)
    return '\n'.join(reversed(out))


_PM_BINDER = re.compile(r"[({][ \t]*([\w'][\w' \t]*?)[ \t]*:[ \t]*((?:[^(){}\n:]*→[ \t]*)?)"
                        r"(?:MeasureTheory\.)?ProbabilityMeasure\b")
_ATOM = r"(?:[\w.']+|\([^()\n]*\))"


def _pm_dot_map(text, defs, lemmas):
    """`μ.map F` (and `(μ n).map F`) where the declaration binds `(μ : ProbabilityMeasure X)` (resp. `(μ : ι →
    ProbabilityMeasure X)`): d13f23b's `ProbabilityMeasure.map ν f` takes no proof, ours takes `(f_aemble :
    AEMeasurable f ν)` with `f` implicit, so it becomes `μ.map (f := F) (by …)` (Perceptron oaiq-061: lemma
    statements, `(μ n).map f = μ n`, a def body; IndependentSets oaiq-069). Only where the binder makes the type
    certain; a `(μ : Measure X)` cast, a ProbabilityMeasure-valued application `(law K μ).map f`, or a name the
    declaration rebinds (`fun μ`, `let μ`, `intro μ`) is left alone."""
    bounds = [m.start() for m in re.finditer(r"(?m)^(?=\S)", text) if TOP.match(text[m.start():m.start() + 40])] + [len(text)]
    out, i = [], 0
    for a, b in zip(bounds, bounds[1:]):
        seg = text[a:b]
        names = []
        for m in _PM_BINDER.finditer(seg):
            for n in m.group(1).split():
                names.append((n, bool(m.group(2).strip())))
        if not names:
            continue
        new = seg
        for n, applied in dict.fromkeys(names):
            e = re.escape(n)
            if re.search(r"(?:\b(?:fun|λ)(?:[ \t]+[\w']+)*[ \t]+|\b(?:let|intro|rintro|set)[ \t]+)%s(?![\w'])" % e, new):
                continue
            recv = r"\(%s(?:[ \t]+%s)+\)" % (e, _ATOM) if applied else r"(?<![\w.'])%s" % e
            rx = re.compile(recv + r"\.map[ \t]+(" + _ARG + ")")

            def rep(m):
                f = m.group(1)
                if re.match(r"\(\s*(?:[\w']+\s*:=|by\b)", f) or 'aemeasurable' in f.lower() or re.search(
                        r"[({][^():]*(?<![\w'])%s(?![\w'])[^():]*:[ \t]*AEMeasurable\b" % re.escape(f), new):
                    return m.group(0)       # already our form: the proof, a named `f`, or a `by`
                tac = _aem_tac(_aem_named([f], new[:m.start()], lemmas))
                return m.group(0)[:m.start(1) - m.start()] + '(f := %s) (by %s)' % (f, tac)
            new = rx.sub(rep, new)
        out.append(text[i:a] + new)
        i = b
    return ''.join(out) + text[i:]


def _total_map_rewrites(text, known=None):
    """d13f23b's `Measure.map` is total, so `IsProbabilityMeasure (μ.map f)` is an instance for every `f`;
    ours needs `Measure.isProbabilityMeasure_map hf.aemeasurable`. Every place the source leans on the
    instance gets a fallback chain (_pm_fallback): the named measurability facts the text shows for the
    mapped function (_aem_named), instance search on its own budget, then `exact
    Measure.isProbabilityMeasure_map (by AEM_TAC)`, so an instance that exists still wins:
    * `have/let/haveI/letI … : IsProbabilityMeasure T := inferInstance` (or `by infer_instance`);
    * a line that is just `infer_instance`, a `… : IsProbabilityMeasure T := by unfold foo; infer_instance`
      line, and `inferInstance` (or `by unfold foo; infer_instance`) as an element of an anonymous constructor
      whose context (_instance_context) mentions a probability measure or a map (CoordinateSweeps oaiq-056:
      in `⟨DensityProfile p l, inferInstance, …⟩` the slots were Fintype/Nonempty, and the chain timed out
      at whnf);
    * `inferInstanceAs (IsProbabilityMeasure (… .map …))` becomes `(show IsProbabilityMeasure … by …)`
      (oaiq-061, oaiq-072);
    * `ProbabilityMeasure.map ν f` (explicit), `… : ProbabilityMeasure X := ν.map f`, and `μ.map f` for a
      `ProbabilityMeasure` binder μ (_pm_dot_map), which take the proof as an argument here: `(f := f) (by
      AEM_TAC)`, named facts first.
    `known`: the lemma names declared anywhere in the port (declared_lemmas); default, this text's."""
    defs = _def_bodies(text)
    lemmas = declared_lemmas([text]) if known is None else known

    def fb(s, pos, window):
        decl = s[_decl_start(s, pos):pos]
        return _pm_fallback(_aem_named(_site_maps(window, decl, defs), decl, lemmas))

    text = re.sub(r"(?m)^([ \t]*(?:have|let|haveI|letI)\b[^\n:]*:[ \t]*IsProbabilityMeasure\b[^\n]*?)[ \t]*:=[ \t]*"
                  r"(?:inferInstance|by infer_instance)[ \t]*$",
                  lambda m: m.group(1) + ' := by ' + fb(m.string, m.start(), m.group(1)), text)
    text = re.sub(r"(?m)^([^\n]*\bIsProbabilityMeasure\b[^\n]*:=[ \t]*by[ \t]+[^\n]*;[ \t]*)infer_instance[ \t]*$",
                  lambda m: m.group(1) + '(%s)' % fb(m.string, m.start(), m.group(1)), text)
    text = re.sub(r"inferInstanceAs[ \t]*\((IsProbabilityMeasure[ \t]+(" + _ARG + r"))\)",
                  lambda m: '(show %s by %s)' % (m.group(1), fb(m.string, m.start(), m.group(2) + '\n' +
                                                                   _instance_context(m.string, m.start())))
                  if '.map' in m.group(2) or 'Measure.map' in m.group(2) else m.group(0), text)
    if re.search(r"MeasureTheory|ProbabilityMeasure|Measure\.map", text):   # a lone instance elsewhere is no measure
        text = re.sub(r"(?m)^([ \t]*)infer_instance[ \t]*$",
                      lambda m: m.group(1) + fb(m.string, m.end(1), _instance_context(m.string, m.end(1)) + '\n'
                                                + _lines_before(m.string, m.end(1))), text)
        text = re.sub(r"(?m)^([ \t]*)inferInstance(?=[ \t]*(?:[,⟩]|$))",
                      lambda m: m.group(1) + '(by %s)' % fb(m.string, m.end(1), _instance_context(m.string, m.end(1)))
                      if _PM_CONTEXT.search(_instance_context(m.string, m.end(1))) else m.group(0), text)
        text = re.sub(r"(?<=[⟨,])(\s*)(?:by infer_instance|inferInstance)(?=[ \t]*[,⟩])",
                      lambda m: m.group(1) + '(by %s)' % fb(m.string, m.end(1), _instance_context(m.string, m.end(1)))
                      if _PM_CONTEXT.search(_instance_context(m.string, m.end(1))) else m.group(0), text)
        text = re.sub(r"(?<=[⟨,])(\s*by[ \t]+(?:unfold|dsimp|delta)\b[^;,⟨⟩\n]*;[ \t]*)infer_instance(?=[ \t]*[,⟩])",
                      lambda m: m.group(1) + '(%s)' % fb(m.string, m.end(1), _instance_context(m.string, m.end(1))
                                                        + '\n' + m.group(1))
                      if _PM_CONTEXT.search(_instance_context(m.string, m.end(1)) + m.group(1)) else m.group(0), text)

    def pm_let(m):
        if 'aemeasurable' in m.group(3):
            return m.group(0)
        decl = m.string[_decl_start(m.string, m.start()):m.start()]
        return m.group(1) + '%s.map (f := %s) (by %s)' % (m.group(2), m.group(3),
                                                          _aem_tac(_aem_named([m.group(3)], decl, lemmas)))
    text = re.sub(r"(?m)^([ \t]*(?:let|have)\b[^\n]*?:[ \t]*ProbabilityMeasure\b[^\n]*?:=[ \t]*)"
                  r"(\w[\w.']*)\.map[ \t]+(\((?:[^()]|\([^()]*\))*\)|[\w.']+)[ \t]*$", pm_let, text)

    def pm_explicit(m):
        if 'aemeasurable' in m.group(2):
            return m.group(0)
        decl = m.string[_decl_start(m.string, m.start()):m.start()]
        return '%s (f := %s) (by %s)' % (m.group(1), m.group(2), _aem_tac(_aem_named([m.group(2)], decl, lemmas)))
    text = re.sub(r"(?<![\w.'])((?:MeasureTheory\.)?ProbabilityMeasure\.map[ \t]+[\w.']+)[ \t]+"
                  r"(\((?:[^()]|\([^()]*\))*\)|[\w.']+)(?=[ \t]*$)", pm_explicit, text, flags=re.M)
    return _pm_dot_map(text, defs, lemmas)


def _arg_end(text, k):
    """End of the Lean argument starting at k (after whitespace): a balanced `( … )` group or a word,
    followed by any `.field` chain and `⁻¹`; k itself if there is none."""
    if k >= len(text):
        return k
    if text[k] in '([':
        close = {'(': ')', '[': ']'}[text[k]]
        depth, r = 0, k
        while r < len(text):
            depth += (text[r] == text[k]) - (text[r] == close)
            r += 1
            if depth == 0:
                break
    else:
        m = re.compile(r"[\w.']+").match(text, k)
        if not m or text[k:].startswith('<|'):
            return k
        r = m.end()
    m = re.compile(r"(?:\.[\w']+)*⁻?¹?").match(text, r)
    return m.end() if m else r


# The tactic that proves `AEStronglyMeasurable f μ` (or each `f i`) where ours added that argument to a lemma
# d13f23b states without it (eLpNorm_sum_le, eLpNorm_le_eLpNorm_of_exponent_le, tendsto_integral_of_L1';
# oaiq-038, oaiq-048). Same order as AEM_TAC: fun_prop, the context, Lp elements, then measurability.
AESM_TAC = ("first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ "
            "| (apply Measurable.aestronglyMeasurable; solve_by_elim) "
            "| (apply Continuous.aestronglyMeasurable; solve_by_elim) "
            "| (apply Measurable.aestronglyMeasurable; measurability) | measurability")

_BRACKETS = {'(': ')', '⟨': '⟩', '‹': '›', '[': ']', '{': '}'}
_NOT_ARGS = {'at', 'with', 'using', 'from', 'only', 'by', 'fun', 'λ', 'then', 'else', 'do', 'in', 'generalizing',
             'says', 'calc', 'if', 'match', 'show', 'have', 'let', 'exact', 'rw', 'simp', 'apply', 'refine'}


def _balanced_end(text, q):
    """End of the bracketed group opening at q (any of ( ⟨ ‹ [ { nested), or None if it never closes."""
    stack, r = [], q
    while r < len(text):
        c = text[r]
        if c in _BRACKETS:
            stack.append(_BRACKETS[c])
        elif stack and c == stack[-1]:
            stack.pop()
        r += 1
        if not stack:
            return r
    return None


def _innermost_open_bracket(text, j):
    """The innermost bracket still open at j, counting from the last line that starts in column 0 (the
    enclosing declaration), or None."""
    start = j
    while start > 0:
        start = text.rfind('\n', 0, start - 1) + 1
        if not text[start:start + 1].isspace():
            break
    stack = []
    for c in text[start:j]:
        if c in _BRACKETS:
            stack.append(c)
        elif stack and c == _BRACKETS[stack[-1]]:
            stack.pop()
    return stack[-1] if stack else None


def _call_args(text, j):
    """The arguments of the application whose head name ends at j, as (named, start, end, ws_start) tuples:
    `( … )` / `⟨ … ⟩` / `‹ … ›` groups (with any `.field` chain), plain terms, `?_`; named `(x := …)` marked.
    An argument on a later line must be indented past the head's line (otherwise it is the next tactic or a
    `calc` step) unless the head sits directly in a `rw [ … ]`/`simp [ … ]` list, a `_` opening a line is a
    `calc` step, and keywords, operators and closing brackets end it."""
    ls = text.rfind('\n', 0, j) + 1
    base = len(text[ls:j]) - len(text[ls:j].lstrip(' \t'))
    if _innermost_open_bracket(text, j) == '[':
        base = -1
    ws = re.compile(r"[ \t]*(?:\n[ \t]*)*")
    word = re.compile(r"\?[\w']*|[^\W\d][\w.'!?]*|\d[\w.]*")
    suffix = re.compile(r"(?:\.[\w']+)*⁻?¹?")
    args, k = [], j
    while True:
        q = ws.match(text, k).end()
        gap = text[k:q]
        if q == k or q >= len(text):
            break
        if '\n' in gap and len(gap) - gap.rfind('\n') - 1 <= base:
            break
        c = text[q]
        if c in '(⟨‹':
            e = _balanced_end(text, q)
            if e is None:
                break
            e = suffix.match(text, e).end()
            named = bool(re.match(r"\(\s*[\w']+\s*:=", text[q:]))
        else:
            m = word.match(text, q)
            if not m or m.group(0) in _NOT_ARGS or (m.group(0) == '_' and '\n' in gap):
                break
            e, named = m.end(), False
        args.append((named, q, e, k))
        k = e
    return args


def _drop_nth_arg(text, pattern, n, only=None):
    """Drop the n-th positional argument (1-based; named arguments skipped) after each match of `pattern`, with
    the whitespace before it. A call with fewer positional arguments is left alone; `only(arg_text)` limits
    it to arguments it accepts."""
    out, i = [], 0
    for m in re.finditer(pattern, text):
        if m.start() < i:
            continue
        pos = [a for a in _call_args(text, m.end()) if not a[0]]
        if len(pos) >= n and (only is None or only(text[pos[n - 1][1]:pos[n - 1][2]])):
            _, _, e, w = pos[n - 1]
            out.append(text[i:w])
            i = e
    return ''.join(out) + text[i:]


def _insert_named_arg(text, pattern, name, value, keep=None):
    """Insert ` (name := value)` right after each match of `pattern` (a named argument, so its place among the
    positional ones does not matter), unless the call names it already or `keep(text, positional_args)` says so."""
    out, i = [], 0
    for m in re.finditer(pattern, text):
        args = _call_args(text, m.end())
        if any(a[0] and re.match(r"\(\s*%s\s*:=" % re.escape(name), text[a[1]:]) for a in args):
            continue
        if keep and keep(text, [a for a in args if not a[0]]):
            continue
        out.append(text[i:m.end()] + ' (%s := %s)' % (name, value))
        i = m.end()
    return ''.join(out) + text[i:]


def _split_top_commas(s):
    parts, depth, cur = [], 0, ''
    for c in s:
        if c in _BRACKETS:
            depth += 1
        elif c in _BRACKETS.values():
            depth -= 1
        if c == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += c
    return parts + [cur]


def _mgf_gaussian_real_map_eq(text):
    """d13f23b's `mgf_gaussianReal (hX : HasLaw X (gaussianReal μ v) p)`; ours takes `hX : p.map X = gaussianReal μ v`,
    HasLaw's `map_eq` field (oaiq-004, oaiq-036). `⟨hm, heq⟩` becomes `heq`, a HasLaw term `h` becomes
    `h.map_eq`; `(by …)` (simp proves either) and `_`/`?_` stay."""
    out, i = [], 0
    for m in re.finditer(r"(?<![\w.'])(?:ProbabilityTheory\.)?[mc]gf_gaussianReal(?![\w'])", text):
        if m.start() < i:
            continue
        pos = [a for a in _call_args(text, m.end()) if not a[0]]
        if not pos:
            continue
        _, q, e, _ = pos[0]
        arg = text[q:e]
        if arg.startswith('⟨') and arg.endswith('⟩'):
            parts = _split_top_commas(arg[1:-1])
            if len(parts) != 2:
                continue
            new = parts[1].strip()
            if not re.fullmatch(r"[\w.'?]+", new):
                new = '(' + new + ')'
        elif re.match(r"\(\s*by\b", arg) or arg in ('_', '?_') or arg.startswith('?') or arg.startswith('‹'):
            continue
        else:
            new = arg + '.map_eq'
        out.append(text[i:q] + new)
        i = e
    return ''.join(out) + text[i:]


def _drop_map_smul_proof(text):
    """d13f23b's `Measure.map_smul c hf` takes an AEMeasurable proof; ours is `map_smul c μ f` with none
    (SingleLatticeCovering 2026-10-25; Brenier/SmoothObstruction oaiq-005). The proof is the argument after
    the first (and after named arguments): `hf.aemeasurable`, `(…).measurable.aemeasurable`, `(by fun_prop)`.
    Dropped, leaving a bare `Measure.map_smul c` for `rw`/`simp`; after `exact` the two other explicit
    arguments become `_ _` (a bare name there is "typeclass instance problem is stuck", MemoryPrecision)."""
    pat = re.compile(r"(?<![\w.'])((?:MeasureTheory\.)?Measure\.map_smul)(?![\w'])")
    out, i = [], 0
    ws = re.compile(r"\s+")
    while True:
        m = pat.search(text, i)
        if not m:
            return ''.join(out) + text[i:]
        out.append(text[i:m.end()])
        k = m.end()
        w = ws.match(text, k)
        a1 = _arg_end(text, w.end() if w else k)           # the scalar
        if not w or a1 == w.end():
            i = k
            continue
        is_exact = bool(re.search(r"(?:\bexact[ \t]+|:=\s*)$", text[max(0, m.start() - 12):m.start()]))
        scalar = text[k:a1]
        k = a1
        named = ''
        while True:                                          # named arguments stay
            w = ws.match(text, k)
            q = w.end() if w else k
            if re.match(r"\(\w+ :=", text[q:]):
                e = _arg_end(text, q)
                named += text[k:e]
                k = e
            else:
                break
        w = ws.match(text, k)
        q = w.end() if w else k
        e = _arg_end(text, q)
        arg = text[q:e]
        proof = e > q and (arg == '(by fun_prop)' or arg.endswith('.aemeasurable')
                           or (arg.startswith('(') and 'aemeasurable' in arg))
        if not proof:
            out.append(scalar + named)
            i = k
            continue
        if is_exact:
            out.append(scalar + named + ' _ _')
        elif scalar.strip() != '_':
            out.append(scalar + named)
        else:
            out.append(named)
        i = e



_CONVERT = re.compile(r"(?m)^([ \t]*)(convert\b[^\n]*(?:\n\1[ \t]+[^\n]*)*)\n")
_CONVERT_BULLET = re.compile(r"(?m)^([ \t]*)(· )(convert\b[^\n]*(?:\n\1[ \t]{3,}[^\n]*)*)\n")


def _convert_close_diamonds(text):
    """`convert h using n` (statement ending in `using n`) leaves, in our Mathlib, an instance-diamond
    goal (`Real.instPreorder.toLE = Real.instLE`) before the goals OpenAI's version leaves; the
    tactics that follow then hit the wrong goal. Close those first with reducible-instances `rfl`
    (CompleteCrossing/TriangleRemoval/NodalLength 2026-10-26). Skipped when a bullet, `<;>` or
    `case` follows, or when the convert is already combined with `;`/`<;>`."""
    def sub(rx, src):
        return rx.sub(lambda m: rep(m, src), src)

    def rep(m, src):
        bullet = m.re is _CONVERT_BULLET
        body = m.group(3 if bullet else 2)
        if not re.search(r"using \d+[ \t]*$", body) or ';' in body.split('using')[-1]:
            return m.group(0)
        rest = src[m.end():].lstrip(' \t\n')
        if re.match(r"(·|<;>|case\b|next\b|all_goals try with_reducible_and_instances rfl)", rest):
            return m.group(0)
        pad = m.group(1) + ('  ' if bullet else '')
        return m.group(0) + pad + "all_goals try with_reducible_and_instances rfl\n"
    return sub(_CONVERT_BULLET, sub(_CONVERT, text))

def _simp_lists_add_if_true(text):
    """Lean 4.34's `ite_true` takes any `Decidable True` instance; 4.33's (ours) only the standard one, so
    `simp only [ite_true]` stops firing on an `if True` whose instance came from elsewhere (oaiq-056,
    BalancedRyser oaiq-063). Our `if_true` is the general lemma: every simp-family list that names
    `ite_true` names `if_true` too (added, not renamed: ours is rfl, which `dsimp` and simp's dsimp steps
    need; `rw` lists are left alone, where an unused `if_true` would fail)."""
    out, i = [], 0
    for m in re.finditer(r"(?<![\w.'])(?:simp|simpa|simp_all|simp_arith|field_simp)\b[?!]?[^\[\n]*?\[", text):
        if m.start() < i:
            continue
        q = m.end() - 1
        e = _balanced_end(text, q)
        if e is None:
            continue
        lst = text[q:e]
        if re.search(r"(?<![\w.'@])ite_true(?![\w'])", lst) and not re.search(r"(?<![\w.'])if_true(?![\w'])", lst):
            lst = re.sub(r"(?<![\w.'@←])(ite_true)(?![\w'])", r"\1, if_true", lst, count=1)
            out.append(text[i:q] + lst)
            i = e
    return ''.join(out) + text[i:]


def _finset_antidiagonal(text):
    """`Finset.antidiagonal n` / `Finset.mem_antidiagonal` resolve to the Hahn-series `Finset.antidiagonal hs ht
    a` (the additive `mulAntidiagonal`) in our environment; the `HasAntidiagonal` ones are meant
    (BalancedRyser oaiq-063), so they are named by the class. A file that uses the Hahn-series form (it
    mentions `IsPWO`/`isPWO`/`HahnSeries`/`mulAntidiagonal`) is left alone."""
    if re.search(r"isPWO|IsPWO|HahnSeries|mulAntidiagonal", text):
        return text
    return re.sub(r"(?<![\w.'])Finset\.(mem_)?antidiagonal(?![\w'])", r"Finset.HasAntidiagonal.\1antidiagonal", text)


# `.restrict D` / `.neg` / `.mono_exponent _` of a MemLp fact is one
_MEMLP_KEEPS = ('restrict', 'neg', 'mono_exponent')


def _is_memlp(term, decl):
    """Is the term textually certain to be a `MemLp` fact? Its head (through `( … )` and the fields
    _MEMLP_KEEPS) is a name whose last component mentions memLp (`f.memLp_top`, `Lp.memLp u`,
    `centeredSquared_memLp v i j`; an `…_iff` is not), or a bare hypothesis the declaration binds as
    `MemLp …` (`(hf : MemLp f ∞ μ)`, `(hA : ∀ i k, MemLp (A i k) 2 μ)`, `have hm : MemLp …`)."""
    t = _norm_term(term)
    if t.startswith('('):
        e = _balanced_end(t, 0)
        if e is None:
            return False
        head, chain = t[:e], re.match(r"(?:\.[\w']+)*", t[e:]).group(0)
        fields = [x for x in chain.split('.') if x]
        if not fields:
            return _is_memlp(head, decl)
        if fields[-1] in _MEMLP_KEEPS:
            return _is_memlp(head + ''.join('.' + x for x in fields[:-1]), decl)
        return 'memLp' in fields[-1] and not fields[-1].endswith('_iff')
    m = re.match(r"[^\W\d][\w.']*", t)
    if not m:
        return False
    parts = m.group(0).split('.')
    if parts[-1] in _MEMLP_KEEPS and len(parts) > 1:
        return _is_memlp('.'.join(parts[:-1]), decl)
    if 'memLp' in parts[-1] or parts[-1].startswith('MemLp'):
        return not parts[-1].endswith('_iff')
    if len(parts) == 1:
        n = re.escape(parts[0])
        return bool(re.search(r"[({][^(){}:]*(?<![\w'])%s(?![\w'])[^(){}:]*:[ \t]*(?:∀[^,]*,[ \t]*)?"
                              r"(?:MeasureTheory\.)?MemLp\b" % n, decl) or
                    re.search(r"\b(?:have|haveI)[ \t]+%s[ \t]*(?:\([^()]*\)[ \t]*)*:[ \t]*(?:MeasureTheory\.)?MemLp\b" % n,
                              decl))
    return False


_MUL_HEAD_OK = re.compile(r"(?:[(⟨,\[]|:=|<\||=>|\bexact|\busing|\bfrom|\brefine|\bthen|\belse|\breturn)[ \t]*$")


def _memlp_mul_swap(text):
    """d13f23b's `MemLp.mul (hφ : MemLp φ p μ) (hf : MemLp f q μ) : MemLp (φ * f) r μ` takes the left factor
    first; ours takes `hf` first (`MemLp.mul hf hφ : MemLp (φ * f)`), and d13f23b's `fun_mul` (and its
    deprecated alias `mul'`) is our `mul'`, likewise swapped. The argument names agree in both (`hφ` the
    left factor, `hf` the right), so `A.mul B` becomes `MeasureTheory.MemLp.mul (hφ := A) (hf := B)` (other
    named arguments such as `(r := 2)` stay put; idempotent, unlike a swap), `A.fun_mul B` becomes `…mul'
    (hφ := A) (hf := B)`, `MemLp.mul A B` becomes `MemLp.mul (hφ := A) (hf := B)` (HardSphere oaiq-054,
    Conductivity oaiq-059: six sites of `exact (A).mul (r := 2) (B)`, CoulombAtom oaiq-071, SKGap oaiq-072). Only where it is textually certain: the receiver is a
    MemLp fact (_is_memlp), the call stands at the head of its term (after `(`, `,`, `:=`, `exact`,
    `using`, … or alone on a line after such a line), and it has exactly one positional argument."""
    out, i = [], 0
    for m in re.finditer(r"((?<![\w'.])MemLp\.(?:mul|fun_mul|mul')|(?<=[\w')])\.(?:mul|fun_mul|mul'))(?![\w'])", text):
        if m.start() < i:
            continue
        name = m.group(1).rsplit('.', 1)[-1]
        explicit = m.group(1).startswith('MemLp.')
        if explicit:
            if re.search(r"[\w.']$", text[:m.start()]):
                continue
            rs = m.start()
        else:                                          # the receiver, back from the dot
            k = m.start()
            while True:
                j = k
                while j > 0 and re.match(r"[\w'.]", text[j - 1]):
                    j -= 1
                if j > 0 and text[j - 1] == ')' and (j == k or text[j] == '.'):
                    depth, q = 0, j - 1
                    while q >= 0:
                        depth += (text[q] == ')') - (text[q] == '(')
                        if depth == 0:
                            break
                        q -= 1
                    if q < 0:
                        break
                    k = q
                    continue
                k = j
                break
            rs = k
            if rs == m.start():
                continue
        before = text[:rs]
        line_before = before[before.rfind('\n') + 1:]
        if line_before.strip():
            if not _MUL_HEAD_OK.search(line_before):
                continue
        else:
            prev = before[:before.rfind('\n')].rstrip()
            if not _MUL_HEAD_OK.search(prev[prev.rfind('\n') + 1:]) and not prev.endswith(('by', ':=', '=>')):
                continue
        decl = text[_decl_start(text, m.start()):m.start()]
        args = _call_args(text, m.end())
        pos = [a for a in args if not a[0]]
        if explicit:
            if len(pos) != 2 or not (_is_memlp(text[pos[0][1]:pos[0][2]], decl)
                                     or _is_memlp(text[pos[1][1]:pos[1][2]], decl)):
                continue
            a, b = pos
            out.append(text[i:m.start()] + ("MemLp.mul'" if name in ('fun_mul', "mul'") else 'MemLp.mul')
                       + text[m.end():a[1]] + '(hφ := %s)' % text[a[1]:a[2]] + text[a[2]:b[1]]
                       + '(hf := %s)' % text[b[1]:b[2]])
            i = b[2]
            continue
        recv = text[rs:m.start()]
        if len(pos) != 1 or not _is_memlp(recv, decl):
            continue
        _, q, e, w = pos[0]
        out.append(text[i:rs] + 'MeasureTheory.MemLp.' + ("mul'" if name in ('fun_mul', "mul'") else 'mul')
                   + ' (hφ := %s)' % recv + text[m.end():w] + text[w:q] + '(hf := %s)' % text[q:e])
        i = e
    return ''.join(out) + text[i:]


_CONVERT_RFL = re.compile(
    r"(?m)^(?P<ind>[ \t]*)convert (?P<e>.+?) using 1\n"
    r"(?P=ind)· (?:funext \w+\n(?P=ind)  rfl|rfl)\n(?P=ind)· ", re.S)


def convert_funext_rfl_to_congr_deriv(text):
    """OpenAI's `HasDerivAt.add/sub/mul/…` conclude lambdas, ours Pi-form sums (and instance diamonds
    on `EuclideanSpace`), so `convert h using 1` leaves a function goal that only `funext x; rfl`
    (or `rfl`) closes and sometimes `funext` cannot even apply. The function equality is
    definitional: `refine h.congr_deriv ?_` (`congr_fderiv` for `HasFDerivAt`) leaves just the
    derivative-value goal, whose bullet is kept. The conclusion's kind is read from the nearest
    preceding `theorem`/`lemma`/`have` header; an unknown kind or a `…Within…` goal is left alone
    (oaiq-080, Boltzmann: 14 sites)."""
    def kind(pos, ind):
        # the enclosing header: nearest preceding theorem/lemma/have indented less than the `convert`
        for m in reversed(list(re.finditer(r"(?m)^([ \t]*)(?:theorem|lemma|have)\b", text[:pos]))):
            if len(m.group(1).expandtabs()) >= len(ind.expandtabs()):
                continue
            head = text[m.start():pos].split(':= by')[0]
            ks = re.findall(r"Has(F?)Deriv(Within)?At", head)
            if not ks or ks[-1][1]:
                return None
            return 'congr_fderiv' if ks[-1][0] else 'congr_deriv'
        return None

    def sub(m):
        k = kind(m.start(), m.group('ind'))
        if not k:
            return m.group(0)
        e = m.group('e')
        depth, whole = 0, e.startswith('(')
        for i, c in enumerate(e):
            depth += (c == '(') - (c == ')')
            if depth == 0 and i < len(e) - 1:
                whole = False
                break
        e = e if whole or re.fullmatch(r"[\w.']+", e) else '(' + e + ')'
        return '%srefine %s.%s ?_\n%s· ' % (m.group('ind'), e, k, m.group('ind'))
    return _CONVERT_RFL.sub(sub, text)


def core_rewrites(text, compat_ns='OAI', known=None):
    """Lean core/Mathlib renames every port needs. OpenAI's `TensorProduct.inductionOn z tmul add`
    (Mathlib d13f23b) takes its zero case from `tmul 0 0`; ours has only `induction_on`, which
    wants a `zero` case too. Every use becomes the compat block's `tensorInductionOn`, which has
    OpenAI's signature, so `induction … with` alternatives, bullets and term-mode uses stay as
    written. (An inserted `| zero => simp only [map_zero]` failed on most real goals and took the
    `induction` line's indentation, not its alternatives': ComparatorModel, Boone–Higman
    2026-10-24.) Likewise `FreeGroup.induction_on`, whose first case d13f23b calls `one` and ours
    `C1`: every use becomes `freeGroupInductionOn`. `compat_ns` is the compat block's namespace
    (None: root level). `known`: the lemma names the whole port declares (declared_lemmas), for the
    measurability facts of _total_map_rewrites; default, this text's."""
    pre = compat_ns + '.' if compat_ns else ''
    text = convert_funext_rfl_to_congr_deriv(text)
    # `convert h using 1 <;> ring` on an inequality leaves an `instLE` diamond ring cannot see through
    text = re.sub(r"(?m)^([ \t]*)convert ([^\n]+?) using 1 <;> ring[ \t]*$",
                  lambda m: ('%sfirst | (convert %s using 1 <;> ring) | exact (le_of_eq (by ring)).trans (%s.trans '
                             '(le_of_eq (by ring)))') % (m.group(1), m.group(2),
                             m.group(2) if re.fullmatch(r"[\w.']+", m.group(2)) else '(' + m.group(2) + ')'),
                  text)
    # Mathlib adds the global tokens `<m ≤m <i ≤i ≤s <r ≤r ≤c`; `1<m` with a variable `m` then fails
    # to parse. Space them unless written as the notation (` <m `).
    text = re.sub(r"(?<=[^\s<≤])([<≤])([misrc])", r" \1 \2", text)
    text = re.sub(r"(?<![\w.'])(?:_root_\.)?TensorProduct\.inductionOn(?![\w'])",
                  pre + 'tensorInductionOn', text)
    # `FreeGroup.induction_on`'s first case is `one` in d13f23b and `C1` here (Eilenberg–Ganea
    # 2026-10-24): the compat block's `freeGroupInductionOn` has d13f23b's names
    text = re.sub(r"(?<![\w.'])(?:_root_\.)?FreeGroup\.induction_on(?![\w'])",
                  pre + 'freeGroupInductionOn', text)
    # d13f23b's `unifIntegrable_iff.mpr` (extended-real ε, δ) is the compat block's `unifIntegrable_of_enn`
    # (SLE IntegralLimits, oaiq-027); `.mp` and the primed form have no shim
    text = re.sub(r"(?<![\w.'])(?:MeasureTheory\.)?unifIntegrable_iff\.(?:mpr|2)(?![\w'])",
                  pre + 'unifIntegrable_of_enn', text)
    # d13f23b's `PosSemidef.dotProduct_mulVec_zero_iff` has `x` implicit; ours explicit (CAT0Fillings, oaiq-029)
    text = re.sub(r"(?<![\w.'])(\([^()\n]*\)(?:\.[12])?|[\w']+)\.dotProduct_mulVec_zero_iff\.(mpr|mp|1|2)(?![\w'])",
                  r"(\1.dotProduct_mulVec_zero_iff _).\2", text)
    # d13f23b's Egorov `tendstoUniformlyOn_of_ae_tendsto'` takes an extended-real ε proof
    # `ENNReal.ofReal_pos.mpr h`; ours takes the real `h : 0 < ε` (CAT0Fillings, oaiq-029)
    text = re.sub(r"(tendstoUniformlyOn_of_ae_tendsto'[^\n]*(?:\n[^\n]*){0,3}?)\(ENNReal\.ofReal_pos\.mpr "
                  r"(\((?:[^()]|\([^()]*\))*\)|[\w.']+)\)", r"\1\2", text)
    # openai/math modules start with a library-suggestion deny list, `open Lean in run_cmd modifyEnv …
    # nameDenyListExt.addEntry env "name"`; the platform's soundness guard refuses `run_cmd` and `modifyEnv`
    # (Kadison commutator, oaiq-039), and the list only steers `grind`/library suggestions: drop the block
    text = re.sub(r"(?m)^open Lean in\nrun_cmd modifyEnv fun env =>\n(?:[ \t]+[^\n]*nameDenyListExt[^\n]*\n|[ \t]+[^\n]*\n)+\n?",
                  lambda m: '' if 'nameDenyListExt' in m.group(0) else m.group(0), text)
    # d13f23b's `NonUnitalStarRingHom.ofClass f` is the compat block's `nonUnitalStarRingHomOfClass`
    # (Kadison commutator, oaiq-039; Kaplansky quotient, oaiq-015)
    text = re.sub(r"(?<![\w.'])NonUnitalStarRingHom\.ofClass(?![\w'])", pre + 'nonUnitalStarRingHomOfClass', text)
    # d13f23b's `Isometry.antilipschitzWith` is `Isometry.antilipschitz` here (HyperbolicGroups, oaiq-034)
    text = re.sub(r"(\.isometry\.|(?<![\w.'])Isometry\.)antilipschitzWith(?![\w'])", r"\1antilipschitz", text)
    # d13f23b's `Finsupp.mapDomain_apply_of_injective hf x a` is our `Finsupp.mapDomain_apply`
    # (same statement; Markov superreflexivity 2026-10-25)
    text = re.sub(r"(?<![\w'])(Finsupp\.)?mapDomain_apply_of_injective(?![\w'])",
                  lambda m: (m.group(1) or '') + 'mapDomain_apply', text)
    # d13f23b's `Measure.map_smul c hf` takes an AEMeasurable proof; ours is `map_smul c μ f` with none
    # (SingleLatticeCovering 2026-10-25)
    text = _drop_map_smul_proof(text)
    text = _drop_positional_arg(text, 'Measure.fst_map_prodMk')   # CompactFactors, oaiq-005
    # d13f23b's `unifIntegrable_iff'` unfolds `UnifIntegrable` to the epsilon-delta form, which is our
    # definition itself: `rw [unifIntegrable_iff']` / `apply unifIntegrable_iff'.mpr` are dropped (WeakHessian, oaiq-052)
    text = re.sub(r"(?m)^[ \t]*(?:rw \[unifIntegrable_iff'\]|apply unifIntegrable_iff'\.mpr)[ \t]*\n", "", text)
    # d13f23b's `Filter.eventuallyEmptyOrUniv_iff'` is our `Filter.eventuallyConst_set'` (FiniteFactor, 2026-10-25)
    text = re.sub(r"(?<![\w'])eventuallyEmptyOrUniv_iff'", "eventuallyConst_set'", text)
    # d13f23b's `eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf` and `eLpNorm_eq_eLpNorm' hp0 hptop hf` have a
    # third, measurability argument, `eLpNorm_nnreal_eq_eLpNorm' hp hf` a second, `eLpNorm_mono_real hf h` a first
    # and `Lp.eLpNorm_le_of_ae_tendsto bound hf hg h` a third (`hg`); ours have none (MemoryPrecision 2026-10-25,
    # oaiq-038, oaiq-048)
    for _n, _k in (("eLpNorm_eq_lintegral_rpow_enorm_toReal", 3), ("eLpNorm_eq_eLpNorm'", 3),
                   ("eLpNorm_nnreal_eq_eLpNorm'", 2), ("eLpNorm_mono_real", 1), ("eLpNorm_norm", 2),
                   ("eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul", 1)):
        text = _drop_nth_arg(text, r"(?<![\w.'@])(?:MeasureTheory\.)?" + re.escape(_n) + r"(?![\w'])", _k)
    text = _drop_nth_arg(text, r"(?<![\w.'@])(?:MeasureTheory\.)?Lp\.eLpNorm_le_of_ae_tendsto(?![\w'])", 3)
    # ours added a measurability argument to `eLpNorm_sum_le` (hfs, first), `eLpNorm_le_eLpNorm_of_exponent_le`
    # (hf, second) and the Bochner `tendsto_integral_of_L1'` (hfi, second): passed by name (oaiq-038, oaiq-048).
    # The vector-measure `tendsto_integral_of_L1' f hfi …` took it already in d13f23b.
    _pre = r"(?<![\w.'@])(?:MeasureTheory\.)?"
    text = _insert_named_arg(text, _pre + r"eLpNorm_sum_le(?![\w'])", 'hfs', 'fun _ _ => by ' + AESM_TAC)
    text = _insert_named_arg(text, _pre + r"eLpNorm_le_eLpNorm_of_exponent_le(?![\w'])", 'hf', 'by ' + AESM_TAC)
    text = _insert_named_arg(text, _pre + r"tendsto_integral_of_L1'(?![\w'])", 'hfi', 'by ' + AESM_TAC,
                             keep=lambda t, pos: len(pos) > 1 and 'stronglymeasurable' in t[pos[1][1]:pos[1][2]].lower())
    # d13f23b renames: `Filter.eventuallyEqSet_univ` is our `Filter.eventuallyEq_univ`; `eLpNorm_indicator_const`
    # (NullMeasurableSet, every use) is our `eLpNorm_indicator_const₀` (ours wants a MeasurableSet)
    text = re.sub(r"(?<![\w'])eventuallyEqSet_univ(?![\w'])", 'eventuallyEq_univ', text)
    text = re.sub(r"(?<![\w'])eLpNorm_indicator_const(?![\w'])", 'eLpNorm_indicator_const₀', text)
    text = re.sub(r"(?<![\w'])List\.sum_le_length_nsmul(?![\w'])", 'List.sum_le_card_nsmul', text)
    text = _mgf_gaussian_real_map_eq(text)    # HasLaw argument -> its map_eq (oaiq-004, oaiq-036)
    _a = r"(?:\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\)|[\w.']+)"
    # d13f23b's `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop hf` has a third, measurability
    # argument; ours has two (Elasticity Regularity, 2026-10-26)
    # (any shape: `hf.aestronglyMeasurable`, a bare `hm`, a multi-line group; CoulombAtom oaiq-071)
    text = _drop_nth_arg(text, r"(?<![\w.'@])(?:MeasureTheory\.)?eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top(?![\w'])", 3)
    # d13f23b's `eLpNorm_mono hf h` takes a measurability argument first; ours takes the bound only
    # (Boltzmann, oaiq-080: 14 sites, every first argument a `….aestronglyMeasurable`)
    for _n in ('eLpNorm_mono', 'eLpNorm_mono_ae'):
        text = _drop_nth_arg(text, r"(?<![\w.'@])(?:MeasureTheory\.)?" + _n + r"(?![\w'])", 1,
                             only=lambda a: "easurable" in a or re.search(r"\bh\w*m\b", a))
    # d13f23b's `eLpNorm_one_eq_lintegral_enorm hf` has a measurability argument; ours has none
    # (MemoryPrecision, 2026-10-25)
    text = _drop_positional_arg(text, 'eLpNorm_one_eq_lintegral_enorm')
    # d13f23b's `eLpNorm_exponent_top hf` takes a measurability argument; ours takes none
    # (Elasticity Parameters, 2026-10-26)
    text = _drop_positional_arg(text, 'eLpNorm_exponent_top')
    # d13f23b's `MvPowerSeries.pderiv i` has no ring argument; ours is `MvPowerSeries.pderiv R i`
    # (SharpRamsey RichLines, oaiq-045)
    text = re.sub(r"(?<![\w.'])MvPowerSeries\.pderiv(?=[ \t\n]+(?!_(?![\w']))[\w(])", 'MvPowerSeries.pderiv _', text)
    # d13f23b's `(Add)Subgroup.isClosed_of_discreteTopology (U := L)` is ours `isClosed_of_discrete (H := L)`
    # (SingleLatticeCovering 2026-10-25)
    text = re.sub(r"(?<=\.)isClosed_of_discreteTopology(?![\w'])( \(U :=)?",
                  lambda m: 'isClosed_of_discrete' + (' (H :=' if m.group(1) else ''), text)
    # d13f23b's `RKHS.posSemidef_tfae` has a fourth item; its `.out 1 3).mpr` is our `.out 2 0).mp`
    # (HotSpots Reciprocal, 2026-10-26)
    text = re.sub(r"\(RKHS\.posSemidef_tfae\.out 1 3\)\.mpr", "(RKHS.posSemidef_tfae.out 2 0).mp", text)
    # d13f23b's `eLpNorm_restrict_eq_of_support_subset` and `eLpNorm_congr_norm_ae` take measurability
    # arguments first (one, resp. two); ours take none (HotSpots Sobolev, 2026-10-26)
    text = _drop_positional_arg(text, 'eLpNorm_restrict_eq_of_support_subset')
    text = _drop_positional_arg(text, 'eLpNorm_le_mul_eLpNorm_of_ae_le_mul')
    for _n in ('eLpNorm_le_of_ae_bound', 'eLpNorm_le_of_ae_nnnorm_bound'):    # SKValue, 2026-10-26
        text = _drop_positional_arg(text, _n)     # GreenOperator, 2026-10-26
    text = _drop_positional_arg(_drop_positional_arg(text, 'eLpNorm_congr_norm_ae'), 'eLpNorm_congr_norm_ae')
    text = re.sub(r"(?m)^([ \t]*convert [^\n;]* using \d+)[ \t]*;[ \t]*(?:ring|\(first \| rfl \| ring\))[ \t]*$", r"\1 <;> first | rfl | ring", text)
    text = re.sub(r"(?m)^([ \t]*(?:· )?convert [^\n;]* using \d+)[ \t]*;[ \t]*(first \|[^\n]*)$", r"\1 <;> \2", text)
    text = _convert_close_diamonds(text)
    # oaiq-054..072 drift (signatures checked against both Mathlibs, 2026-10-28):
    # d13f23b's `Submodule.isTopologicalAddGroup` is our `Submodule.topologicalAddGroup` (Conductivity oaiq-059)
    text = re.sub(r"(?<![\w.'])Submodule\.isTopologicalAddGroup(?![\w'])", 'Submodule.topologicalAddGroup', text)
    # d13f23b's `LinearMap.coe_ofClass` is our `LinearMap.coe_coe` (SimpleOvergroups oaiq-066)
    text = re.sub(r"(?<![\w.'])LinearMap\.coe_ofClass(?![\w'])", 'LinearMap.coe_coe', text)
    # d13f23b's `Ordinal.lt_wf` is a `WellFoundedLT` instance, so `.induction` is `WellFoundedLT.induction` (case
    # `ind`); ours is a `WellFounded`, whose `.induction` names it `h` (TuringRigidity oaiq-064)
    text = re.sub(r"(?<=using )Ordinal\.lt_wf\.induction(?![\w'])", 'WellFoundedLT.induction', text)
    # d13f23b's `Measure.lintegral_bind_le f m (hμ : AEMeasurable μ m)` and `lintegral_map_le f (hg : AEMeasurable
    # g μ)` take the measurability; ours take the kernel / the map: the compat block's forms (CoulombAtom oaiq-071)
    text = re.sub(r"(?<![\w.'])(?:MeasureTheory\.)?(?:Measure\.)?lintegral_bind_le(?![\w'])",
                  pre + 'lintegral_bind_le_ae', text)
    text = re.sub(r"(?<![\w.'])(?:MeasureTheory\.)?lintegral_map_le(?![\w'])", pre + 'lintegral_map_le_ae', text)
    # d13f23b's `FiniteMeasure.mass_map_le {f} {μ} (hf : AEMeasurable f μ)`; ours `mass_map_le (f) (μ)`, and
    # `_ _` leaves `f` undetermined: the compat block's form (BalancedRyser oaiq-063)
    text = re.sub(r"(?<![\w.'])(?:MeasureTheory\.)?FiniteMeasure\.mass_map_le(?![\w'])",
                  pre + 'finiteMeasure_mass_map_le', text)
    # d13f23b's `Measure.isProbabilityMeasure_of_map (hf : AEMeasurable f μ)`; ours takes `f`, and `_` leaves the
    # instance argument stuck: the compat block's `isProbabilityMeasure_of_map_ae` (HardSphere oaiq-054)
    text = re.sub(r"(?<![\w.'])(?:MeasureTheory\.)?Measure\.isProbabilityMeasure_of_map(?![\w'])",
                  pre + 'isProbabilityMeasure_of_map_ae', text)
    # d13f23b's `JoinedIn.map` takes `ContinuousOn f F`; ours takes `Continuous f`, the old one is
    # `map_continuousOn` (HardSphere BathPhase oaiq-054)
    text = re.sub(r"\.map(?=[ \t]+\(?[\w.']+\.continuousOn\b)", '.map_continuousOn', text)
    # ours added `(hf : AEStronglyMeasurable f μ)` to `meas_ge_le_mul_pow_eLpNorm_enorm` (HardSphere oaiq-054)
    text = _insert_named_arg(text, _pre + r"meas_ge_le_mul_pow_eLpNorm_enorm(?![\w'])", 'hf', 'by ' + AESM_TAC)
    text = _simp_lists_add_if_true(text)
    text = _finset_antidiagonal(text)
    text = _total_map_rewrites(text, known)
    text = _memlp_mul_swap(text)      # MemLp.mul's factors swapped (oaiq-054/059/071/072)
    # d13f23b's lambda-form `logDeriv_fun_mul` / `logDeriv_fun_prod` are our `logDeriv_mul` / `logDeriv_prod`
    # (NodalLength, 2026-10-26)
    text = re.sub(r"(?<![\w'])logDeriv_fun_(mul|prod)(?![\w'])", r"logDeriv_\1", text)
    # d13f23b's `IsMinOn.isLocalMinOn` / `IsMaxOn.isLocalMaxOn` are our `.localize` (SKValue, 2026-10-26)
    text = re.sub(r"\.isLocal(?:Min|Max)On(?![\w'])", ".localize", text)
    # d13f23b's `Subgroup.isMulCommutative_closure` has an extra `x ≠ y` binder; ours has none, so the
    # `rintro` after `apply` loses its last `_` (Boone-Higman, PeriodicGroups 2026-10-26)
    text = re.sub(r"(?m)^([ \t]*apply (?:Add)?Subgroup\.is(?:Add|Mul)Commutative_closure\n[ \t]*rintro [^\n⟩]*⟩ _ [^\n⟩]*⟩) _[ \t]*$",
                  r"\1", text)
    # d13f23b's `Sigma.ι_comp_desc` is our `Sigma.ι_desc` (Kaplansky quasitrace, 2026-10-26)
    text = re.sub(r"(?<![\w'])Sigma\.ι_comp_desc(_assoc)?(?![\w'])", r"Sigma.ι_desc\1", text)
    # d13f23b renames (UnitDistances, StandardMap 2026-10-25)
    text = re.sub(r"(?<![\w.'])birkhoffSum_succ_apply'(?![\w'])", "birkhoffSum_succ'", text)
    text = re.sub(r"(?<![\w.'])birkhoffSum_add_right_apply(?![\w'])", "birkhoffSum_add", text)
    text = re.sub(r"(?<![\w.'])birkhoffSum_succ_apply(?![\w'])", "birkhoffSum_succ", text)
    text = re.sub(r"(?<![\w.'])birkhoffSum_zero_apply(?![\w'])", "birkhoffSum_zero", text)
    text = re.sub(r"(?<![\w.'])finsum_le_finsum(?![\w'])", "finsum_le_finsum'", text)
    text = re.sub(r"(?<![\w'])Filter\.eventuallyEqSet_iff(?![\w'])", 'Filter.eventuallyEq_set', text)
    text = re.sub(r"posLog_le_posLog \(neg_one_lt_zero\.le\.trans ", 'posLog_le_posLog (id ', text)
    # d13f23b renames (StandardMap 2026-10-25)
    text = re.sub(r"\brange_inj_of_wellFoundedLT\b", 'range_inj', text)
    text = re.sub(r"(?<![\w.'])TopologicalSpace\.NonemptyCompacts\.dist_eq(?![\w'])", 'Metric.NonemptyCompacts.dist_eq', text)
    text = re.sub(r"(?<![\w.'])TopologicalSpace\.NonemptyCompacts\.lipschitz_infDist_const(?![\w'])", 'Metric.lipschitz_infDist_set', text)
    # d13f23b's `Set.equivOfEq h` is our `Equiv.setCongr h` (QuarticPowerFree 2026-10-25)
    text = re.sub(r"(?<![\w.'])Set\.equivOfEq(?![\w'])", 'Equiv.setCongr', text)
    # d13f23b's `(Continuous)LinearMap.nonneg_iff_isPositive` has the operator implicit; ours takes it
    # explicitly (Kirchberg-Rordam 2026-10-25)
    text = re.sub(r"(?<![\w.'])((?:ContinuousLinearMap|LinearMap)\.nonneg_iff_isPositive)\.(mpr|mp|1|2)(?![\w'])",
                  r"(\1 _).\2", text)
    text = re.sub(r"(?<![\w.'])\(?nonneg_iff_isPositive\)?\.(mpr|mp|1|2)(?![\w'])", r"(nonneg_iff_isPositive _).\1", text)
    # d13f23b's `(Continuous)LinearMap.le_def` has f g implicit; ours takes them explicitly (NuclearUltrapower 2026-10-26)
    text = re.sub(r"(?<![\w.'])((?:ContinuousLinearMap|LinearMap)\.le_def)\.(mpr|mp|1|2)(?![\w'])", r"(\1 _ _).\2", text)
    # d13f23b's `LinearIsometryEquiv.isometry.lipschitzWith`: ours `Isometry.lipschitz` (MultipleMixing Joinings)
    text = re.sub(r"\.isometry\.lipschitzWith(?![\w'])", '.isometry.lipschitz', text)
    # ... and likewise any `ContinuousLinearMap/Equiv.lipschitzWith` field (GeneralMahler, 2026-10-26)
    text = re.sub(r"(?<=[\w)\]'])\.lipschitzWith(?![\w'])", '.lipschitz', text)
    text = re.sub(r"(?<![\w.'])ContinuousLinearMap\.isTopologicalAddGroup(?![\w'])", 'inferInstance', text)  # named instance absent here
    text = re.sub(r"\.lt_of_le\.linearOrder(?![\w'])", '.linearOrder', text)   # IsChain.linearOrder wants ≤ here
    # d13f23b's `compProd_map_condDistrib hX hY` is our `compProd_map_condDistrib hY` (MultipleMixing, 2026-10-26)
    text = _drop_positional_arg(text, 'compProd_map_condDistrib')
    # d13f23b's `CStarAlgebra.norm_mem_spectrum_of_nonneg a ha` has `a` explicit; ours implicit
    # (Kirchberg-Rordam 2026-10-25)
    text = re.sub(r"(?<![\w.'])(CStarAlgebra\.norm_(?:or_neg_norm_)?mem_spectrum(?:_of_nonneg)?)[ \t]+(?:[A-Za-z_][\w']*|\([\w']+ : [\w.']+\))[ \t]+(?=[A-Za-z_(])",
                  r"\1 ", text)
    # d13f23b's `CStarAlgebra.star_mul_le_algebraMap_norm_sq a` has `a` explicit; ours implicit
    # (FactorGeneration 2026-10-26). A named `(a := x)` use is fine in both.
    text = re.sub(r"(?<![\w.'])(CStarAlgebra\.star_mul_le_algebraMap_norm_sq)[ \t]+[A-Za-z_][\w']*(?![\w'.])",
                  r"\1", text)
    # d13f23b renamed the ordered-monoid `Finset.prod_le_prod'` (one hypothesis) to
    # `Finset.prod_le_prod`, and our nonnegative `prod_le_prod` to `prod_le_prod₀` (the compat
    # aliases map that one back, after this). So an unsuffixed use is our primed lemma
    # (wave 2, 2026-10-25: BinaryMatching, QuantitativeVanDerWaerden, PeriodicTiling).
    text = re.sub(r"(?<![\w.'])((?:Finset\.)?(?:prod_le_prod|prod_le_one|one_le_prod|single_le_prod"
                  r"|prod_le_prod_of_subset_of_le_one|prod_le_prod_of_subset_of_one_le))(?![\w'₀])",
                  r"\1'", text)
    # d13f23b's `prod_le_prod_of_subset_of_le_one₀` / `…_of_one_le₀` are our unsuffixed lemmas
    # (same statements; SquareDifference ReflectionLaw 2026-10-25)
    text = re.sub(r"(?<![\w'])((?:Finset\.)?prod_le_prod_of_subset_of_(?:le_one|one_le))₀(?![\w'])",
                  r"\1", text)
    # oaiq-068 (PiExponent 2026-10-28), d13f23b names vs ours: the presheaf-of-modules monoidal
    # structure sits in `PresheafOfModules` here; going-up lemma, power-series order of a unit,
    # the additive `sum_le_sum_of_subset_of_nonpos'` and the compactness lemma's namespace.
    text = re.sub(r"(?<![\w'])PresheafOfModulesOfCommRing\.", 'PresheafOfModules.', text)
    text = re.sub(r"(?<![\w.'])Ideal\.under_lt_under_of_integral_mem_sdiff(?![\w'])",
                  'Ideal.comap_lt_comap_of_integral_mem_sdiff', text)
    text = re.sub(r"(?<![\w.'])PowerSeries\.order_zero_of_isUnit(?![\w'])", 'PowerSeries.order_zero_of_unit', text)
    text = re.sub(r"(?<![\w'])((?:Finset\.)?sum_le_sum_of_subset_of_nonpos)(?![\w'₀])", r"\1'", text)
    text = re.sub(r"(?<![\w.'])IsCompactElement\.exists_finset_of_le_iSup(?![\w'])",
                  'CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _', text)
    # Kadison similarity (oaiq-075): d13f23b's C⋆ lemmas take the element explicitly; ours has it implicit
    # and the proof as an autoParam, so the element becomes a named argument
    text = re.sub(r"(?<![\w.'])CStarAlgebra\.pow_nonneg ([\w']+) ([\w']+) ([\w.']+)",
                  r"CStarAlgebra.pow_nonneg (a := \1) \3 \2", text)
    # d13f23b's `CStarAlgebra.pow_antitone ha₁ ha₀` takes the upper bound first; ours is `ha₀ ha₁`
    text = re.sub(r"(?<![\w.'])CStarAlgebra\.pow_antitone ([\w']+) ([\w']+)",
                  r"CStarAlgebra.pow_antitone (ha₀ := \2) (ha₁ := \1)", text)
    return split_partial_namespaces(text)


# ---------------------------------------------------------------- the StdSimplex compatibility shim

STDSIMPLEX_SHIM = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                               'StdSimplexCompat.lean')
# the shim published as a definitions bundle (the single-file route imports it once it is in the
# workspace; carve_prep config treats its declarations as external)
STDSIMPLEX_BUNDLE = 'Definitions.Def_OAIStdSimplexCompat'
STDSIMPLEX_MODULE = 'StdSimplexCompat'
# `SimplexCategory.toTopHomeo` lands in the subtype here and in the structure in d13f23b: structure
# mode calls `toTopHomeoD` (module-route only), declared in this module on top of the shim
STDSIMPLEX_TOP_MODULE = 'StdSimplexTopCompat'
STDSIMPLEX_TOP = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                              'StdSimplexTopCompat.lean')
_TOPHOMEO = re.compile(r"(?<![\w'])toTopHomeo(_naturality_apply)?(?![\w'])")
STDSIMPLEX_MODES = ('auto', 'structure', 'subtype', 'off')
# Mathlib d13f23b files our Mathlib (0df444a) does not have; the shim provides their content
STDSIMPLEX_MISSING_IMPORTS = tuple('Mathlib.Geometry.Convex.ConvexSpace.' + m for m in (
    'Topology', 'CompactSpaceStdSimplex', 'Barycenter', 'PathConnectedSpaceStdSimplex',
    'ModuleTopology'))
# every `Convexity.StdSimplex.*` name the openai/math sources use (full checkout 1581d4c,
# 2026-10-24); the P2M_LEAN test checks the shim (with our Mathlib) declares each one
OAI_STDSIMPLEX_NAMES = tuple('StdSimplex.' + n for n in (
    'barycenter continuous_convexCombPair continuous_map continuous_weights_apply '
    'diam_range_toFun_comp_weights_subset_closedBall ext homeomorphI homeomorphI_apply_coe '
    'homeomorphI_single_one homeomorphI_single_zero homeomorphI_symm_one homeomorphI_symm_zero '
    'iConvexComb_single isAffineMap_map isBounded_range_toFun_comp_weights '
    'isClosedEmbedding_toFun_comp_weights isEmbedding_toFun_comp_weights map map_comp map_const '
    'map_id map_map map_sConvexComb map_single range_toFun_comp_weights single single_injective '
    'subBarycenter subBarycenter_weights_apply_eq_zero total_of_fintype weights '
    'weights_barycenter_apply weights_convexCombPair weights_map weights_nonneg weights_sConvexComb '
    'weights_single weights_subBarycenter').split())
_SIMPLEX = re.compile(r"(?<![\w.'])(?:Convexity\.)?StdSimplex(?![\w'])")
_MISSING_IMPORT = re.compile(r'^import (%s)[ \t]*\n' % '|'.join(re.escape(m) for m in STDSIMPLEX_MISSING_IMPORTS), re.M)


def mentions_stdsimplex(text):
    """Does the text use `Convexity.StdSimplex` (qualified or bare) or import a d13f23b-only
    ConvexSpace file?"""
    return bool(_SIMPLEX.search(text) or _MISSING_IMPORT.search(text))


def stdsimplex_mode(texts, mode='auto'):
    """The shim mode for a port: 'off' when no text needs it (or on request); 'auto' means
    'structure' (the shim's API on our `Convexity.StdSimplex`, no renaming). 'subtype' (on request)
    renames `Convexity.StdSimplex` to `OAI.SStd`, the subtype `stdSimplex R X`: for code that
    identifies the simplex with `SimplexCategory.toTop.obj` (Problem340's singular homology), whose
    objects are that subtype in our Mathlib; it needs finite index types and has no ConvexSpace."""
    if mode not in STDSIMPLEX_MODES:
        raise PortError('unknown --stdsimplex mode %r (one of %s)' % (mode, ', '.join(STDSIMPLEX_MODES)))
    if mode == 'off' or not any(mentions_stdsimplex(t) for t in texts):
        return 'off'
    return 'structure' if mode == 'auto' else mode


def stdsimplex_rewrite(text, mode):
    """The text for shim mode `mode`: the d13f23b-only Mathlib imports dropped; in 'subtype' mode
    every `Convexity.StdSimplex` / bare `StdSimplex` renamed `OAI.SStd`."""
    if mode == 'off':
        return text
    text = _MISSING_IMPORT.sub('', text)
    if mode == 'subtype':
        text = _SIMPLEX.sub('OAI.SStd', text)
    elif mode == 'structure':
        text = _TOPHOMEO.sub(lambda m: 'toTopHomeoD' + (m.group(1) or ''), text)
    return text


def stdsimplex_shim(body=False):
    """The shim's text (lean/StdSimplexCompat.lean); with body=True without its import lines, for
    inlining into a single file."""
    t = open(STDSIMPLEX_SHIM, encoding='utf-8').read()
    if body:
        t = re.sub(r'^import [^\n]*\n', '', t, flags=re.M).lstrip('\n')
    return t


def stdsimplex_single(text, mode='auto', use_bundle=False, drop=((), ())):
    """The single-file route: (text, extra import lines, shim block to put after the imports).
    With use_bundle the published bundle is imported; otherwise the shim is inlined, without the
    declarations `drop` = (full names, anonymous instances) a statement bundle already declares."""
    mode = stdsimplex_mode([text], mode)
    if mode == 'off':
        return text, [], ''
    text = stdsimplex_rewrite(text, mode)
    if use_bundle:
        return text, ['import ' + STDSIMPLEX_BUNDLE], ''
    block, _ = drop_declarations(stdsimplex_shim(body=True), set(drop[0]), set(drop[1]))
    return text, [], block


LINT = ('set_option linter.all false\nset_option linter.unusedVariables false\n'
        'set_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n')


def module_sources(lean_root, prefixes):
    """{OpenAI module name: (short name, text)} for every module under the given prefixes of the
    fetched lean/ tree; the short name is the path below its prefix with `/` -> `_` (a nested
    Sub/X.lean is Sub_X)."""
    out, short = {}, {}
    for pre in prefixes:
        base = os.path.join(lean_root, *pre.split('.'))
        if not os.path.isdir(base):
            raise PortError('no directory for %s: %s' % (pre, base))
        for dp, _, fs in os.walk(base):
            for f in sorted(fs):
                if f.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(dp, f), base)[:-5]
                    s = rel.replace(os.sep, '_')
                    if s in short and short[s] != pre:
                        raise PortError('two modules flatten to %s (%s, %s)' % (s, short[s], pre))
                    short[s] = pre
                    out[pre + '.' + rel.replace(os.sep, '.')] = (
                        s, open(os.path.join(dp, f), encoding='utf-8').read())
    return out


def _scopes(lines, known_ns=()):
    """(namespace, [opened namespaces]) in force at each line. An `open X` inside namespace `A.B`
    opens each of `A.B.X`, `A.X`, `O.X` (O already open) that is a namespace of `known_ns`, else `X`;
    it lasts to the `end` of its section or namespace. `open … in` and `open scoped` are skipped."""
    frames, out = [['', [], []]], []         # [kind, namespace parts, opens]
    for l in lines:
        ns = '.'.join(p for f in frames for p in f[1])
        opens = [o for f in frames for o in f[2]]
        out.append((ns, opens))
        m = re.match(r'^\s*(?:noncomputable\s+)?(namespace|section|end)\b\s*(\S*)', l)
        if m and m.group(1) == 'namespace':
            frames += [['ns', [q], []] for q in m.group(2).split('.')]
        elif m and m.group(1) == 'section':
            frames.append(['sec', [], []])
        elif m:
            for _ in range(m.group(2).count('.') + 1 if m.group(2) else 1):
                if len(frames) > 1:
                    frames.pop()
        o = re.match(r'^\s*open\s+(?!scoped\b)(.*)$', l)
        if o and not re.search(r'\bin\s*$', l):
            words = re.sub(r'\((?:[^()])*\)|\b(?:hiding|renaming)\b.*$', ' ', o.group(1)).split()
            for w in words:
                cands = []
                parts = ns.split('.') if ns else []
                for k in range(len(parts), 0, -1):
                    cands.append('.'.join(parts[:k]) + '.' + w)
                cands += [x + '.' + w for x in opens] + [w]
                found = [c for c in cands if c in known_ns]
                frames[-1][2].extend(found or [w])
                opens = opens + (found or [w])
    return out


def _resolve(ident, ns, opens, decls):
    """The declarations of `decls` (full names) that `ident` names at a site in namespace `ns` with
    `opens` in force: the innermost namespace prefix that has it wins; at the root, the root name and
    every opened namespace's (more than one is ambiguous). A name `decls` does not hold (Mathlib's, a
    hypothesis) gives the empty set."""
    if ident.startswith('_root_.'):
        return {ident[7:]} & decls
    parts = ns.split('.') if ns else []
    for k in range(len(parts), 0, -1):
        c = '.'.join(parts[:k]) + '.' + ident
        if c in decls:
            return {c}
    return ({o + '.' + ident for o in opens} | {ident}) & decls


_MACRO_BINDERS = re.compile(r"\b(?:intro|intros|rintro|rename_i|fun|λ|obtain|rcases|have|let|set|with)\b([^;|=⟩]*)")


_TACTIC_COMBINATORS = {'repeat', "repeat'", 'try', 'all_goals', 'any_goals', 'focus', 'iterate', 'with_reducible',
                       'with_reducible_and_instances', 'with_unfolding_all', 'on_goal', 'pick_goal', 'case', 'next'}


def _macro_idents(body):
    """[(start, end, identifier)] of the term identifiers in a tactic macro body: not a tactic name
    (first word after `|`, `;`, `<;>`, `(` in tactic position, or the start), not a dotted field
    (`x.foo` after a non-name), not a name the body binds itself (intro/fun/have …), nor `h.trans` of one."""
    bound = set()
    for m in _MACRO_BINDERS.finditer(body):
        bound.update(re.findall(r"[^\W\d][\w']*", m.group(1).split(':')[0]))
    out = []
    for m in re.finditer(r"(?<![\w.'])(?:_root_\.)?%s(?:\.%s)*(?![\w'!?])" % (SEG, SEG), body):
        k, tac = m.start(), True
        while True:
            j = k - 1
            while j >= 0 and body[j] in ' \t\n':
                j -= 1
            if j < 0 or body[j] in '|;>·':
                break
            if body[j] == '(':
                k = j
                continue
            w = re.search(r"([\w']+)(?:[ \t]+\d+)?$", body[:j + 1])
            if w and w.group(1) in _TACTIC_COMBINATORS:
                break
            tac = False
            break
        if not tac and m.group(0).split('.')[0] not in bound:
            out.append((m.start(), m.end(), m.group(0)))
    return out


def inline_module_macros(sources):
    """`sources` with every tactic macro removed and inlined (leantext.inline_tactic_macros) in its
    own module and in each module that imports it, directly or not (WLIdentification 2026-10-23:
    the module route kept `macro "word_poly"`, which carve.py gen refuses; oai_port.py inlines).

    An inlined macro's names resolve at the use site, not where Lean resolved them (the macro's
    namespace and `open`s): MatchingCount (oaiq-051) defined `tree_cost` under `open
    MatchingFPRAS.TreeTyped`, and `ExecutableOptions.polynomial_map` captured its `apply
    polynomial_map` at the use sites. So each identifier of a macro body that resolves to exactly one
    ported declaration at the definition site, and to something else at some use site, is written as
    that full name in every inlined copy (`_root_.` when a namespace could capture even that). A name
    the definition site does not resolve to one ported declaration (Mathlib's, a hypothesis, an
    ambiguity) is left alone, with a warning when a use site resolves it to a ported one. Not seen:
    `open … in`, local hypotheses at the use site, structure fields and constructors."""
    import warnings
    from .leantext import tactic_macros, inline_macro_uses
    stripped, own, imps, where = {}, {}, {}, {}
    for oai, (short, t) in sources.items():
        stripped[oai], own[oai] = tactic_macros(t)
        imps[oai] = [x for x in re.findall(r'^import (\S+)', t, re.M) if x in sources]
        lines = t.split('\n')
        for name in own[oai]:
            m = re.search(r'^[ \t]*(?:(?:local|scoped)[ \t]+)?macro[ \t]+"%s"' % re.escape(name), t, re.M)
            where[name] = (oai, t[:m.start()].count('\n') if m else 0)
    decls_of = {oai: {d[0] for d in declarations(stripped[oai].split('\n')) if d[0]} for oai in sources}
    every = set().union(*decls_of.values()) if decls_of else set()
    known_ns = {'.'.join(n.split('.')[:k]) for n in every for k in range(1, n.count('.') + 1)}
    seen, closure = {}, {}

    def visible(m, stack=()):
        if m not in seen:
            out = dict()
            for x in imps[m]:
                if x not in stack:
                    out.update(visible(x, stack + (m,)))
            out.update(own[m])
            seen[m] = out
        return seen[m]

    def reach(m, stack=()):
        if m not in closure:
            out = set(decls_of[m])
            for x in imps[m]:
                if x not in stack:
                    out |= reach(x, stack + (m,))
            closure[m] = out
        return closure[m]

    scopes = {oai: _scopes(sources[oai][1].split('\n'), known_ns) for oai in sources}
    sscopes = {oai: _scopes(stripped[oai].split('\n'), known_ns) for oai in sources}
    bodies = {}
    for name, (doai, dline) in where.items():
        body = own[doai][name]
        ns, opens = scopes[doai][dline]
        idents = [(a, b, x, _resolve(x, ns, opens, reach(doai))) for a, b, x in _macro_idents(body)]
        qualify, warned = {}, set()
        for uoai in sources:
            if name not in visible(uoai):
                continue
            ls = stripped[uoai].split('\n')
            for i, l in enumerate(ls):
                if not re.search(r"(?<![\w.'])%s(?![\w'!?])" % re.escape(name), l):
                    continue
                uns, uopens = sscopes[uoai][i]
                for a, b, x, d in idents:
                    u = _resolve(x, uns, uopens, reach(uoai))
                    if u == d:
                        continue
                    if len(d) == 1:
                        qualify[x] = next(iter(d))
                    elif u and (x, uoai) not in warned:
                        warned.add((x, uoai))
                        warnings.warn('inlined macro %s: `%s` resolves to %s in %s (line %d, namespace %s) but '
                                      'to %s where the macro is defined; check that site by hand'
                                      % (name, x, ', '.join(sorted(u)), uoai, i + 1, uns or '(root)',
                                         ', '.join(sorted(d)) or 'no ported declaration'), stacklevel=2)
        for a, b, x, d in reversed(idents):
            if x in qualify:
                f = qualify[x]
                if any(n.endswith('.' + f) for n in every):
                    f = '_root_.' + f
                body = body[:a] + f + body[b:]
        bodies[name] = body
    return {oai: (short, inline_macro_uses(stripped[oai], {n: bodies[n] for n in visible(oai)}))
            for oai, (short, _) in sources.items()}


def demodule(text):
    """A file of Lean's module system as a plain file: its `module` line dropped and each
    `public import` / `meta import` / `public meta import` / `import all` made a plain `import` (Ryser
    FiniteSetEstimates 2026-10-25: the Compat import went in front of `module`, and every import
    after it then failed to parse)."""
    hdr = header_end(text) if 'header_end' in globals() else len(text)
    head, body = text[:hdr], text[hdr:]
    head = re.sub(r'^module[ \t]*\n', '', head, flags=re.M)
    head = re.sub(r'^(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?', 'import ', head, flags=re.M)
    return head + body


def mathlib_has(module, root=None):
    """False only for a `Mathlib.*` module our Mathlib (0df444a) lacks: d13f23b moved files
    (`Mathlib.Basic.Real.Basic`, MatroidSecretary 2026-10-25), and a module route import of one
    fails with "object file ... does not exist". Such an import becomes `import Mathlib`. The
    StdSimplex shim's missing imports are left to it. True when the Mathlib tree is not found."""
    if not module.startswith('Mathlib.') or module in STDSIMPLEX_MISSING_IMPORTS:
        return True
    root = root or os.path.join(os.environ.get('P2M_WORKSPACE') or
                                os.path.expanduser('~/claude/prove2me_workspace'),
                                '.lake', 'packages', 'mathlib')
    if not os.path.isdir(os.path.join(root, 'Mathlib')):
        return True
    return os.path.exists(os.path.join(root, *module.split('.')) + '.lean')


def module_texts(sources, mod, compat_text='', compat_ns='OAI', header='', stdsimplex='auto'):
    """The workspace modules of a module-route port before the patches: {file name: text} under
    Lean prefix `mod` (e.g. Solutions.OAIQW_X), Compat.lean not included. `sources` as
    module_sources returns. Each module's OAI imports are rewritten to the ported copies (an import
    of an OpenAI module that is not ported is an error: add its prefix); tactic macros are inlined
    (inline_module_macros); a module importing none of them imports `<mod>.Compat`; the linter-off
    lines and `header` go after the imports; then the core and compat rewrites, and the StdSimplex
    shim (stdsimplex_mode over all modules: each module that needs it imports `<mod>.StdSimplexCompat`,
    stdsimplex_rewrite). This is the text the patches are counted against
    (carve_prep.py filter-patches; ComparatorModel 2026-10-24: counted against the raw source, a
    patch of what core_rewrites had inserted counted 0)."""
    names = {k: v[0] for k, v in sources.items()}
    block, rewrites = compat_block(compat_text, compat_ns)
    sources = inline_module_macros(sources)
    smode = stdsimplex_mode([x for _, x in sources.values()], stdsimplex)
    known = declared_lemmas([x for _, x in sources.values()])
    files, missing = {}, set()
    for oai, (short, t) in sources.items():
        def rep(m):
            n = m.group(1)
            if n in names:
                return 'import %s.%s' % (mod, names[n])
            if n.split('.')[0] in ('OAI', 'ComparatorChallenges'):
                missing.add('%s (imported by %s)' % (n, oai))
            if not mathlib_has(n):
                return 'import Mathlib'
            return m.group(0)
        t = re.sub(r'^import (\S+)', rep, demodule(t), flags=re.M)
        if not re.search(r'^import %s\.' % re.escape(mod), t, re.M):
            # after `import Mathlib`, else first (Compat imports Mathlib, so a module with narrower
            # Mathlib imports pays nothing more)
            t, k = re.subn(r'^import Mathlib[ \t]*\n', 'import Mathlib\nimport %s.Compat\n' % mod, t,
                           count=1, flags=re.M)
            if not k:
                t = 'import %s.Compat\n' % mod + t
        if smode != 'off' and mentions_stdsimplex(t):
            t = stdsimplex_rewrite(t, smode)
            ls = t.split('\n')
            k = max(i for i, l in enumerate(ls) if l.startswith('import ')) + 1
            imps = ['import %s.%s' % (mod, STDSIMPLEX_MODULE)]
            if 'toTopHomeoD' in t:
                imps.append('import %s.%s' % (mod, STDSIMPLEX_TOP_MODULE))
            t = '\n'.join(ls[:k] + imps + ls[k:])
        ls = t.split('\n')
        k = max(i for i, l in enumerate(ls) if l.startswith('import ')) + 1
        t = '\n'.join(ls[:k] + [''] + (LINT + header).rstrip().split('\n') + ls[k:])
        files[short + '.lean'] = guard_renames(apply_rewrites(core_rewrites(t, compat_ns, known), rewrites))
    if missing:
        raise PortError('imports of OpenAI modules that are not ported:\n  ' + '\n  '.join(sorted(missing)))
    return files


# the Mathlib files the compat block's declarations need, for `module_files(compat_imports=…)`
COMPAT_NARROW_IMPORTS = (
    'Mathlib.Combinatorics.Young.YoungDiagram',
    'Mathlib.Analysis.Normed.Algebra.Spectrum',
    'Mathlib.Algebra.MvPolynomial.Basic',
    'Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order',
    'Mathlib.Algebra.Order.BigOperators.Ring.Finset',
    'Mathlib.Algebra.Order.BigOperators.Group.Finset',
    'Mathlib.Combinatorics.SimpleGraph.Paths',
    'Mathlib.Data.List.Nodup',
    'Mathlib.GroupTheory.FreeGroup.Basic',
    'Mathlib.LinearAlgebra.TensorProduct.Basic',
    'Mathlib.MeasureTheory.Measure.Typeclasses.Probability',
    'Mathlib.MeasureTheory.MeasurableSpace.Embedding',
    'Mathlib.MeasureTheory.MeasurableSpace.Constructions',
)


def module_files(sources, mod, patches=(), compat_text='', compat_ns='OAI', header='', stdsimplex='auto',
                 compat_imports=None):
    """module_texts, then the patches for the module route (each exactly its count over all files;
    single-file-only ones skipped, see single_file_only), Compat.lean holding
    compat_block(compat_text, compat_ns), and StdSimplexCompat.lean (the shim) when a module
    needs it. `compat_imports`: Mathlib modules for Compat to import instead of all of Mathlib (it
    puts every Mathlib instance in scope of every module; COMPAT_NARROW_IMPORTS)."""
    files = apply_patches(module_texts(sources, mod, compat_text, compat_ns, header, stdsimplex),
                          patches, route='modules')
    cimp = '\n'.join('import ' + m for m in compat_imports) if compat_imports else 'import Mathlib'
    files['Compat.lean'] = cimp + '\n\n' + compat_block(compat_text, compat_ns)[0]
    if any(('import %s.%s\n' % (mod, STDSIMPLEX_MODULE)) in x for x in files.values()):
        files[STDSIMPLEX_MODULE + '.lean'] = stdsimplex_shim()
    if any(('import %s.%s\n' % (mod, STDSIMPLEX_TOP_MODULE)) in x for x in files.values()):
        files[STDSIMPLEX_TOP_MODULE + '.lean'] = open(STDSIMPLEX_TOP, encoding='utf-8').read().replace('@MOD@', mod)
    return files


def classify_attempt(out):
    """(verdict, submission id, message) of one attempt's log text, or None if it never finished."""
    m = re.findall(r'verdict (\S+) (\S+)', out)
    if 'ALREADY-PROVED' in out:     # the submit guard found an existing proof; nothing was sent
        return 'REFUSED', None, out[out.index('ALREADY-PROVED'):][:300]
    if 'REFUSED' in out:
        return 'REFUSED', None, out[out.index('REFUSED'):][:300]
    if m and m[-1][0] == 'ACCEPTED':
        return 'ACCEPTED', m[-1][1], ''
    if 'not accepted' in out:
        msg = out[out.find('not accepted'):][:300]
        return ('TIMEOUT' if 'timed out' in msg else 'REJECTED'), (m[-1][1] if m else None), msg
    return None


def state_from_log(text):
    """{'attempts', 'verdict', 'id', 'msg'} from a goal's submission log (one `=== time` section per
    attempt; text before the first is an attempt made outside the queue), or None."""
    done = [c for c in map(classify_attempt, text.split('\n=== ')) if c]
    if not done:
        return None
    v, sid, msg = done[-1]
    return {'attempts': len(done), 'verdict': v, 'id': sid, 'msg': msg}
