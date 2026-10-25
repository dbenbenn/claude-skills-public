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
GUARD_RENAMES = {'prelude': 'prelude_'}


def guard_renames(text):
    """Every identifier token the soundness guard refuses renamed (GUARD_RENAMES), qualified uses
    (`X.prelude`) included, longer names (`prelude_size`) not; comments too, harmlessly."""
    for old, new in GUARD_RENAMES.items():
        text = re.sub(r"(?<![\w'!?\u2080-\u209c])%s(?![\w'!?\u2080-\u209c])" % re.escape(old), new, text)
    return text


def core_rewrites(text, compat_ns='OAI'):
    """Lean core/Mathlib renames every port needs. OpenAI's `TensorProduct.inductionOn z tmul add`
    (Mathlib d13f23b) takes its zero case from `tmul 0 0`; ours has only `induction_on`, which
    wants a `zero` case too. Every use becomes the compat block's `tensorInductionOn`, which has
    OpenAI's signature, so `induction … with` alternatives, bullets and term-mode uses stay as
    written. (An inserted `| zero => simp only [map_zero]` failed on most real goals and took the
    `induction` line's indentation, not its alternatives': ComparatorModel, Boone–Higman
    2026-10-24.) Likewise `FreeGroup.induction_on`, whose first case d13f23b calls `one` and ours
    `C1`: every use becomes `freeGroupInductionOn`. `compat_ns` is the compat block's namespace
    (None: root level)."""
    pre = compat_ns + '.' if compat_ns else ''
    text = re.sub(r"(?<![\w.'])(?:_root_\.)?TensorProduct\.inductionOn(?![\w'])",
                  pre + 'tensorInductionOn', text)
    # `FreeGroup.induction_on`'s first case is `one` in d13f23b and `C1` here (Eilenberg–Ganea
    # 2026-10-24): the compat block's `freeGroupInductionOn` has d13f23b's names
    text = re.sub(r"(?<![\w.'])(?:_root_\.)?FreeGroup\.induction_on(?![\w'])",
                  pre + 'freeGroupInductionOn', text)
    # d13f23b's `Finsupp.mapDomain_apply_of_injective hf x a` is our `Finsupp.mapDomain_apply`
    # (same statement; Markov superreflexivity 2026-10-25)
    text = re.sub(r"(?<![\w'])(Finsupp\.)?mapDomain_apply_of_injective(?![\w'])",
                  lambda m: (m.group(1) or '') + 'mapDomain_apply', text)
    # d13f23b's `Measure.map_smul c hf` takes an AEMeasurable proof; ours is `map_smul c μ f` with none
    # (SingleLatticeCovering 2026-10-25)
    text = re.sub(r"(?<![\w.'])((?:MeasureTheory\.)?Measure\.map_smul) _ "
                  r"(?:\(by fun_prop\)|[\w.]+\.aemeasurable)(?![\w.'])", r"\1", text)
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
    return text


# ---------------------------------------------------------------- the StdSimplex compatibility shim

STDSIMPLEX_SHIM = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'lean',
                               'StdSimplexCompat.lean')
# the shim published as a definitions bundle (the single-file route imports it once it is in the
# workspace; carve_prep config treats its declarations as external)
STDSIMPLEX_BUNDLE = 'Definitions.Def_OAIStdSimplexCompat'
STDSIMPLEX_MODULE = 'StdSimplexCompat'
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


def inline_module_macros(sources):
    """`sources` with every tactic macro removed and inlined (leantext.inline_tactic_macros) in its
    own module and in each module that imports it, directly or not (WLIdentification 2026-10-23:
    the module route kept `macro "word_poly"`, which carve.py gen refuses; oai_port.py inlines)."""
    from .leantext import tactic_macros, inline_macro_uses
    stripped, own, imps = {}, {}, {}
    for oai, (short, t) in sources.items():
        stripped[oai], own[oai] = tactic_macros(t)
        imps[oai] = [x for x in re.findall(r'^import (\S+)', t, re.M) if x in sources]
    seen = {}

    def visible(m, stack=()):
        if m not in seen:
            out = dict()
            for x in imps[m]:
                if x not in stack:
                    out.update(visible(x, stack + (m,)))
            out.update(own[m])
            seen[m] = out
        return seen[m]
    return {oai: (short, inline_macro_uses(stripped[oai], visible(oai)))
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
            t = '\n'.join(ls[:k] + ['import %s.%s' % (mod, STDSIMPLEX_MODULE)] + ls[k:])
        ls = t.split('\n')
        k = max(i for i, l in enumerate(ls) if l.startswith('import ')) + 1
        t = '\n'.join(ls[:k] + [''] + (LINT + header).rstrip().split('\n') + ls[k:])
        files[short + '.lean'] = guard_renames(apply_rewrites(core_rewrites(t, compat_ns), rewrites))
    if missing:
        raise PortError('imports of OpenAI modules that are not ported:\n  ' + '\n  '.join(sorted(missing)))
    return files


# the Mathlib files the compat block's declarations need, for `module_files(compat_imports=…)`
COMPAT_NARROW_IMPORTS = (
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
