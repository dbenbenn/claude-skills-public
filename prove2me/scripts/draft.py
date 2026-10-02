#!/usr/bin/env python3
"""Upload a mission proposal Draft from a repo, and verify the live Draft against it.

usage: draft.py MISSION_DIR verify
       draft.py MISSION_DIR upload [--go]        (dry run without --go)

Every mission used to carry its own upload_X.py and verify_X.py, each copied from the last and
edited; eleven verifiers across six repos, most of which only checked that a read-back was
non-empty, so a read-back filed on the wrong item passed. This is the one copy. A mission supplies
data, not code: MISSION_DIR/mission.py defines

  NAME, FIELDS (field ids), MISSION_TYPE ('ResearchPaper' | 'Textbook'), NAMESPACE ('Garrido')
  DEFINITIONS  [{name, title, nls, tags, page, result[, extra, ref]}]   code: lib/Def_<name>.lean
  THEOREMS     [{name, title, nls, tags, page, result, milestone_title, milestone_description, ...}]
               (optional `namespace`, when an item is another author's, e.g. a cited external result)
  REFERENCES   [{theorem_id, theorem_name[, milestone_title, milestone_description]}]  (no title:
               an item only, e.g. an imported definition bundle); a reference with `page` (and
               `result`, optional `context_pages`) is audited like a theorem by stage_auditor.py
               stage-all and source_audit.py, from its published statement in Theorems/
  GOAL         the goal theorem's short name (never a milestone); 'ref:<theorem_name>' when the
               goal is already published
  KEEP_REFS    optional {'<theorem_name>': 'reason'}: references kept on purpose although no statement
               needs them (verify otherwise flags them; see unneeded_refs)
  ORDER        optional item_order as a list of keys (Def names, 'ref:<name>', theorem names);
               the default is definitions, references, theorems; the goal always goes last
  src(page, result, extra=None, ref=None) -> the `source` string
  payloads()   -> {short_name: (preamble, formal_statement)}; extract_payloads() below does it
               for the usual layout (one statements file, bundles imported by use)

and the repo holds description.md, readbacks/<name>.readback.md (Def_<name> for a bundle), and
proposal.json (the proposal id and item ids, written by upload --go; never by a dry run).

`verify` also requires DECISIONS.md (source_audit.py decisions): every source-audit finding on the
goal and the milestones decided by the human, none stale -- the gap review, a human decision point
like the item-list approval.

`upload` is diff-based. It reads the live Draft first and re-posts only what differs, so an item
that has not changed is never touched and cannot lose a confirmation to a no-op edit. It creates
the proposal on the first run. `verify` compares every field the upload sets, flags live items
and milestones the repo does not have, and ends with `BAD <n>`; its exit status is n != 0.
"""
import glob, importlib.util, json, os, re, subprocess, sys, urllib.parse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

READBACK_MODEL = 'claude-opus-5-5'
norm = lambda t: ' '.join((t or '').split())


def extract_payloads(path, namespace, bundles, opens=None):
    """{name: (preamble, formal_statement)} from a statements file of top-level `theorem`s inside
    `namespace <namespace>`. Each preamble imports Mathlib plus exactly the bundles whose
    identifiers its statement uses (bundles: {module: [identifier, ...]}) -- never a template,
    since a preamble freezes at publish and an unused import is a permanent false dependency."""
    # Names and identifiers go by p2mlib.names' one identifier grammar: `theorem (\\w+)` stopped at
    # a prime, and `K\\b` matched inside `K'`. Comments go by the comment-aware stripper (only `--`
    # lines were dropped, so a module doc line beginning "theorem" read as a statement). Not
    # LeanInfo: a mission's statements are extracted while drafting, before its bundles need be built.
    from p2mlib.leantext import strip
    from p2mlib.names import IDENT_START, IDENT_END
    ident = r"[^\W\d][\w'!?₀-ₜ]*(?:\.[^\W\d][\w'!?₀-ₜ]*)*"
    text = strip(open(path, encoding='utf-8').read())
    out = {}
    for part in re.split(r'^(?=theorem\s)', text, flags=re.M):
        m = re.match(r'theorem\s+(%s)' % ident, part)
        if not m:
            continue
        body = re.split(r'^end %s\s*$' % re.escape(namespace), part, flags=re.M)[0].strip()
        imports = ['import Mathlib'] + ['import ' + mod for mod, ids in bundles.items()
                                         # an id ending in `.` is a namespace prefix ('MooreFoelner.')
                                         if any(re.search(IDENT_START + re.escape(i) + ('' if i.endswith('.') else IDENT_END), body)
                                                for i in ids)]
        pre = '\n'.join(imports)
        used = sorted(o for o, toks in (opens or {}).items() if any(t in body for t in toks))
        if used:
            pre += '\nopen scoped ' + ' '.join(used)
        for u in sorted(set(re.findall(r'Type (u(?:_\d+)?\b|v\b|w\b)', body))):
            pre += '\nuniverse ' + u
        out[m.group(1)] = (pre, 'namespace %s\n\n%s\n\nend %s' % (namespace, body, namespace))
    return out


def load(mdir):
    """The mission's data with its prose/ files merged (p2mlib.mission: a fresh module each time,
    never the cached `import mission`)."""
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from p2mlib.mission import load as _load
    return _load(mdir)


def desired(M, mdir):
    """What the Draft should contain, keyed the way proposal.json keys item ids."""
    rb = lambda n: open(os.path.join(mdir, 'readbacks', n + '.readback.md'), encoding='utf-8').read()
    pay = M.payloads()
    items = {}
    for D in M.DEFINITIONS:
        items[D['name']] = {
            'kind': 'definition', 'definition_name': D['name'], 'definition_title': D['title'],
            'definition': open(os.path.join(mdir, 'lib', 'Def_' + D['name'] + '.lean'), encoding='utf-8').read(),
            'natural_language_statement': D['nls'], 'tags': D['tags'],
            'source': M.src(D['page'], D['result'], D.get('extra'), D.get('ref')),
            'readback': rb('Def_' + D['name']), 'readback_model': READBACK_MODEL}
    for R in M.REFERENCES:
        items['ref:' + R['theorem_name']] = {'kind': 'reference', 'theorem_id': R['theorem_id']}
    for T in M.THEOREMS:
        pre, fs = pay[T['name']]
        items[T['name']] = {
            'kind': 'theorem', 'theorem_name': T.get('namespace', M.NAMESPACE) + '.' + T['name'],
            'theorem_title': T['title'],
            'preamble': pre, 'formal_statement': fs, 'natural_language_statement': T['nls'],
            'tags': T['tags'], 'source': M.src(T['page'], T['result'], T.get('extra'), T.get('ref')),
            'readback': rb(T['name']), 'readback_model': READBACK_MODEL}
    miles = {}
    for R in M.REFERENCES:
        # a referenced definition bundle is an item, not an attack target: no milestone_title
        # a published goal is a reference too (QFS): it keeps its milestone text for the audits
        if R.get('milestone_title') and 'ref:' + R['theorem_name'] != M.GOAL:
            miles['ref:' + R['theorem_name']] = (R['milestone_title'], R['milestone_description'])
    for T in M.THEOREMS:
        if T['name'] != M.GOAL:
            miles[T['name']] = (T['milestone_title'], T['milestone_description'])
    order = getattr(M, 'ORDER', None) or ([D['name'] for D in M.DEFINITIONS]
             + ['ref:' + R['theorem_name'] for R in M.REFERENCES] + [T['name'] for T in M.THEOREMS])
    # the goal is always last, also when it is a published reference
    order = [k for k in order if k != M.GOAL] + [M.GOAL]
    desc = open(os.path.join(mdir, 'description.md'), encoding='utf-8').read()
    return items, miles, order, desc


# fields compared per kind; `kind`, `theorem_id` and `readback_model` are identity, not content
FIELDS = {'definition': ['definition_name', 'definition_title', 'definition', 'natural_language_statement',
                         'tags', 'source', 'readback'],
          'theorem': ['theorem_name', 'theorem_title', 'preamble', 'formal_statement',
                      'natural_language_statement', 'tags', 'source', 'readback'],
          'reference': []}


def live_value(it, f):
    v = it.get(f)
    if f == 'definition_title' and v is None:
        v = it.get('theorem_title')
    if f == 'definition_name' and v is None:
        v = it.get('theorem_name')
    return v


def same(a, b):
    if isinstance(a, list) or isinstance(b, list):
        return sorted(a or []) == sorted(b or [])
    return norm(a) == norm(b)


def diff(M, mdir, call, st):
    """[(key, what)] for everything that differs; also returns the live proposal."""
    items, miles, order, desc = desired(M, mdir)
    d = call('GET', '/mission-proposals/' + st['id'])
    d = d.get('proposal', d)
    live = {it['id']: it for it in d.get('items') or []}
    lm = {m['item_id']: m for m in (call('GET', '/mission-proposals/%s/milestones' % st['id']).get('milestones') or [])}
    bad = []
    ids = st.get('items', {})
    for k, want in items.items():
        it = live.get(ids.get(k))
        if it is None:
            bad.append((k, 'missing item')); continue
        for f in FIELDS[want['kind']]:
            if not same(live_value(it, f), want[f]):
                bad.append((k, f))
    for k, (t, dsc) in miles.items():
        m = lm.get(ids.get(k))
        if m is None:
            bad.append((k, 'missing milestone')); continue
        if not same(m.get('title') or m.get('milestone_title'), t):
            bad.append((k, 'milestone title'))
        if not same(m.get('description') or m.get('milestone_description'), dsc):
            bad.append((k, 'milestone description'))
    known = {ids.get(k) for k in items}
    for iid in live:
        if iid not in known:
            bad.append((iid, 'stray live item not in the repo'))
    for iid in lm:
        if iid not in {ids.get(k) for k in miles}:
            bad.append((iid, 'stray milestone (the goal, or an item the repo does not list)'))
    if not same(d.get('description'), desc):
        bad.append(('description', 'text'))
    if d.get('item_order') != [ids.get(k) for k in order]:
        bad.append(('item_order', 'order'))
    if d.get('main_item_id') != ids.get(M.GOAL):
        bad.append(('goal', 'main_item_id'))
    return bad, d, lm


def unneeded_refs(M, mdir, items, miles, call):
    """References the Draft does not need: [(key, why)].

    A reference earns its place by being the goal, a milestone, or a definition bundle (or
    theorem) that one of those statements imports, directly or through another bundle. Anything
    else is left over from an earlier design: on QFS (2026-09-26) 18 of 42 references were --
    superseded statements, a dead route, five bundles nothing imported -- and passed BAD 0 because
    verify only compared what the repo listed against what the Draft held, and the repo still
    listed them. mission.py may name deliberate exceptions in KEEP_REFS {name: reason}."""
    from prune_solution import _workspace
    ws = _workspace()
    keep = getattr(M, 'KEEP_REFS', {}) or {}
    imp = lambda t: (set(re.findall(r'^import Definitions\.Def_(\w+)', t or '', re.M)),
                     set(re.findall(r'^import Theorems\.Thm_(\w+?)_(\w+)', t or '', re.M)))
    roots = {M.GOAL} | set(miles)
    defs, thms, seen_pre = set(), set(), []
    for k in roots:
        it = items.get(k) or {}
        if it.get('kind') == 'theorem':
            seen_pre.append(it['preamble'])
        elif it.get('kind') == 'reference':
            name = k[len('ref:'):]
            r = [t for t in (call('GET', '/theorems?theorem_name=' + name).get('theorems') or [])
                 if t.get('theorem_name') == name]
            seen_pre.append((r[0].get('preamble') or '') if r else '')
    for D in M.DEFINITIONS:                     # a draft bundle is always wanted: its own imports count
        seen_pre.append(items[D['name']]['definition'])
    for t in seen_pre:
        d, th = imp(t)
        defs |= d; thms |= {'%s.%s' % x for x in th}
    todo = list(defs)
    while todo:                                 # bundles import bundles
        n = todo.pop()
        for f in (os.path.join(ws, 'Definitions', 'Def_%s.lean' % n), os.path.join(mdir, 'lib', 'Def_%s.lean' % n)):
            if os.path.exists(f):
                for m in imp(open(f, encoding='utf-8').read())[0] - defs:
                    defs.add(m); todo.append(m)
                break
    out = []
    for R in M.REFERENCES:
        n, k = R['theorem_name'], 'ref:' + R['theorem_name']
        if k in roots or n in defs or n in thms or n in keep:
            continue
        kind = 'definition bundle' if os.path.exists(os.path.join(ws, 'Definitions', 'Def_%s.lean' % n)) else 'theorem'
        out.append((k, 'unneeded reference (%s: not the goal, not a milestone, not imported by one); '
                       'remove it, or list it in KEEP_REFS with a reason' % kind))
    for T in M.THEOREMS:                        # the same question for a draft theorem
        if T['name'] not in roots:
            out.append((T['name'], 'draft theorem that is neither the goal nor a milestone'))
    return out


def deprecated_refs(M, items, miles, desc, call):
    """[(where, why)] for uploaded prose that names a deprecated platform theorem.

    A deprecated theorem is hidden from discovery, so a pointer to it sends the reader to a page
    the platform no longer shows; QFS (2026-09-27) kept "the published `QFS.core_induction` gives
    ..." in three statements after retiring 42 superseded theorems. Backticked dotted names
    (`NS.name`) in every natural-language statement, source, milestone text and the description
    are looked up once each."""
    texts = [('description', desc)]
    for k, it in items.items():
        for f in ('natural_language_statement', 'source'):
            if it.get(f):
                texts.append((k, it[f]))
    for k, (t, d) in miles.items():
        texts.append((k + ' milestone', t + '\n' + d))
    cache, out = {}, []
    for where, t in texts:
        for n in sorted(set(re.findall(r'`((?:[A-Z]\w*\.)+\w+)`', t))):
            if n not in cache:
                r = [x for x in (call('GET', '/theorems?theorem_name=' + n).get('theorems') or [])
                     if x.get('theorem_name') == n]
                cache[n] = bool(r and r[0].get('deprecated_at'))
            if cache[n]:
                out.append((where, 'names the deprecated theorem `%s`' % n))
    return out


def bundle_relation_docstrings(M, mdir):
    """[(where, why)] for a bundle docstring that asserts a relationship to another object.

    A bundle freezes at publish and its docstrings are stripped before every audit, so a sentence
    like "`G = G(ℝ)` is `G ⊤`" is a permanent, unaudited claim; Monod's bundle carried exactly that
    until dbenbenn asked for G and H to be defined (2026-09-29). Relationships belong in the
    natural-language statement or in a proved lemma. Heuristic: a backticked object said to be
    another one, or "equivalent / agrees with / coincides / same as"."""
    out = []
    # one named object said to *be* another ("`G = G(ℝ)` is `G ⊤`"), not a defining phrase like
    # "is `μ`-null" or "agrees with a Möbius map"
    pat = re.compile(r'`[^`]+` is `[^`]+`(?![-\w])|\b(?:equivalent to|coincides with|the same as)\b')
    for D in getattr(M, 'DEFINITIONS', []):
        f = os.path.join(mdir, 'lib', 'Def_%s.lean' % D['name'])
        if not os.path.exists(f):
            continue
        for doc in re.findall(r'/--(.*?)-/', open(f, encoding='utf-8').read(), re.S):
            m = pat.search(doc)
            if m:
                out.append(('Def_' + D['name'], 'docstring asserts a relationship (%r): %s'
                            % (m.group(0), ' '.join(doc.split())[:120])))
    return out


LEAN_WORDS = {'fun', 'by', 'theorem', 'lemma', 'def', 'let', 'have', 'show', 'Type', 'Prop', 'Sort',
              'sorry', 'rfl', 'at', 'with', 'in', 'if', 'then', 'else', 'do', 'match'}


def _decls(path, seen):
    """Qualified names declared in a Lean file and in the Definitions/Theorems it imports, plus the
    namespaces it opens; `seen` guards the recursion."""
    names, spaces = set(), set()
    if path in seen or not os.path.exists(path):
        return names, spaces
    seen.add(path)
    text = open(path, encoding='utf-8').read()
    stack = []
    for ln in text.split('\n'):
        m = re.match(r'(namespace|end)\s+([\w.]+)\s*$', ln)
        if m and m.group(1) == 'namespace':
            stack.append(m.group(2)); spaces.add(m.group(2)); continue
        if m and stack and stack[-1] == m.group(2):
            stack.pop(); continue
        m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                     r"(?:def|theorem|lemma|abbrev|structure|class|inductive|instance)\s+([\w'.]+)", ln)
        if m:
            names.add('.'.join(stack + [m.group(1)]))
    from prune_solution import _workspace
    ws = _workspace()
    for mod in re.findall(r'^import ((?:Definitions|Theorems)\.\S+)', text, re.M):
        n, sp = _decls(os.path.join(ws, *mod.split('.')) + '.lean', seen)
        names |= n; spaces |= sp
    return names, spaces


def dead_lean_refs(M, mdir, its, mls, desc, call):
    """[(where, why)] for a backticked Lean name in the prose that no longer resolves.

    What goes stale when Lean is renamed is the prose that names it: a description or a
    natural-language statement still saying `mem_G_iff'` after the statement became
    `mem_G_iff_isPiecewiseProj`. This replaces a check that demanded the description name every
    bundle definition a statement uses (it pushed milestone-only definitions into the Setting;
    dbenbenn, 2026-09-30: what was wanted is catching *dead* references). Each backticked span's
    head name is resolved against the mission's own declarations and imported bundles, then by
    `#check` in the workspace (Mathlib, open namespaces), then on the platform by exact name
    (a published theorem not fetched locally). Bound variables (`f`, `E₀`) are skipped: only names
    with a dot, an underscore, or an upper-case letter and three or more characters are checked."""
    texts = [('description', desc)]
    for k, it in its.items():
        for f in ('natural_language_statement', 'theorem_title', 'definition_title'):
            if it.get(f):
                texts.append((k, it[f]))
    for k, (t, d) in mls.items():
        texts.append(('milestone ' + k, (t or '') + '\n' + (d or '')))
    refs = {}
    for where, t in texts:
        for span in re.findall(r'`([^`\n]+)`', t):
            m = re.match(r"[(]*([^\s()]+)", span.strip())
            if not m:
                continue
            head = m.group(1).rstrip(',.;:')
            if not re.fullmatch(r"[^\W\d][\w'.]*", head) or head in LEAN_WORDS:
                continue
            if not ('.' in head or '_' in head or (len(head) >= 3 and re.search(r'[A-Z]', head))):
                continue
            refs.setdefault(head, where)
    names, spaces, seen = set(), set(), set()
    for f in sorted(glob.glob(os.path.join(mdir, 'lib', '*.lean'))):
        n, sp = _decls(f, seen)
        names |= n; spaces |= sp
    short = {q.split('.')[-1] for q in names}
    left = [h for h in refs if h not in names and h not in short
            and not any(q.endswith('.' + h) for q in names)]
    if left:
        from prune_solution import _workspace
        ws = _workspace()
        imps = sorted({l for f in glob.glob(os.path.join(mdir, 'lib', '*.lean'))
                       for l in open(f, encoding='utf-8').read().split('\n') if l.startswith('import ')})
        imps = [l for l in imps if os.path.exists(os.path.join(ws, *l.split()[1].split('.')) + '.lean')
                or l == 'import Mathlib']
        body = '\n'.join(imps) + '\n' + ''.join('open %s\n' % sp for sp in sorted(spaces)) + '\n'
        start = body.count('\n') + 1
        body += ''.join('#check @%s\n' % h for h in left)
        probe = os.path.join(ws, '.draft_refs_probe.lean')
        open(probe, 'w', encoding='utf-8').write(body)
        out = subprocess.run(['lake', 'env', 'lean', probe], cwd=ws, capture_output=True, text=True)
        os.remove(probe)
        badlines = {int(n) for n in re.findall(r'\.lean:(\d+):\d+: error', out.stdout + out.stderr)}
        left = [h for i, h in enumerate(left) if start + i in badlines]
    out = []
    for h in left:
        if '.' in h:
            # the platform's search is flaky: the same query has answered with the theorem at
            # limit=20 and with nothing at limit=100 (2026-09-30). Try the short and the full
            # name, three rounds, and call a name dead only when every answer misses it.
            found, errored = False, False
            for _ in range(3):
                for q in (h.split('.')[-1], h):
                    try:
                        r = call('GET', '/theorems?q=' + urllib.parse.quote(q) + '&limit=20')
                    except Exception:  # noqa: BLE001 -- an unreachable platform is not a dead name
                        errored = True
                        continue
                    items = r.get('theorems', r.get('items', r.get('data', []))) if isinstance(r, dict) else r
                    if any(t.get('theorem_name') == h for t in items or []):
                        found = True
                        break
                if found:
                    break
            if found or errored:
                continue
        out.append((refs[h], 'names `%s`, which no longer resolves (renamed or removed?)' % h))
    return out


PRONOUN = re.compile(r'(?<![\w-])(he|him|his|she|her|hers)(?![\w-])', re.I)
QUOTED = re.compile(r'“[^”]*”|"[^"\n]*"|`[^`]*`')


def author_pronouns(its, mls, desc):
    """[(where, why)] for a pronoun in the published prose, outside quotations and code.

    Authors are *they* unless the source says otherwise. check_pronouns.py covers files, but was
    only as good as its arguments: handed file names it scanned nothing and reported 0 hits while a
    natural-language statement said "his right translate" of Moore (F-amenability, 2026-09-30).
    This runs on exactly what publishes. A quotation is the source's own wording (CFP's "he
    conjectured" of Geoghegan) and is skipped."""
    texts = [('description', desc)]
    for k, it in its.items():
        for f in ('natural_language_statement', 'theorem_title', 'definition_title'):
            if it.get(f):
                texts.append((k, it[f]))
    for k, (t, d) in mls.items():
        texts.append(('milestone ' + k, (t or '') + '\n' + (d or '')))
    out = []
    for where, t in texts:
        hay = QUOTED.sub(lambda m: ' ' * len(m.group(0)), t)
        for m in PRONOUN.finditer(hay):
            a = max(0, m.start() - 50)
            out.append((where, 'pronoun %r: …%s…' % (m.group(0), ' '.join(t[a:m.end() + 40].split()))))
    return out


def short_bundle_names(M, mdir):
    """[(where, why)] for a bundle declaration named with at most two characters.

    The payload builder imports a bundle when a statement mentions one of its names, and a name
    like `s` matches every bound variable `s`: the Moore bundle's string helper `s` made every §3
    statement import `Def_MooreTrees` for nothing (2026-09-30), and a preamble freezes at publish."""
    # only a name some statement actually binds is a problem: Moore's own `x0`, `L_f` are short
    # but bound nowhere, while `s` was bound in every §3 sum (2026-09-30)
    texts = []
    for f in glob.glob(os.path.join(mdir, 'lib', 'Thm_*.lean')):
        texts.append(open(f, encoding='utf-8').read())
    out = []
    # split the statements files into single declarations, so a statement that also uses a longer
    # name of the bundle (and so imports it genuinely) is not flagged: Lodha-Moore's `K` appears as
    # the ascription `(K : Set ...)`, which the binder pattern cannot tell from a binder, in a
    # statement that needs the bundle anyway (2026-10-02)
    decls = []
    for t in texts:
        decls += re.split(r"(?m)^(?=theorem |lemma )", t)
    for D in getattr(M, 'DEFINITIONS', []):
        f = os.path.join(mdir, 'lib', 'Def_%s.lean' % D['name'])
        if os.path.exists(f):
            names = re.findall(r"^(?:noncomputable )?(?:def|abbrev|structure|inductive|instance) ([\w']+)",
                               open(f, encoding='utf-8').read(), re.M)
            longs = [m for m in names if len(m) > 2]
            for n in names:
                if len(n) > 2:
                    continue
                N = re.escape(n)
                binder = re.compile(  # `(a n : T)`, `{n : T}`; `∀ n,`, `∑ n ∈`, `fun n =>`; `{n | …}`
                    r"[(\{⦃]\s*(?:[\w'₀-₉]+\s+)*?%s(?:\s+[\w'₀-₉]+)*\s*:(?!=)" % N
                    + r"|(?:[∀∃∑∏⋃⋂λ]|\bfun\b|\blet\b|\bhave\b)ᶠ?\s*(?:[\w'₀-₉]+\s+)*?%s(?=[\s:,])" % N
                    + r"|\{\s*%s\s*\|" % N)
                if any(binder.search(t) and not any(re.search(r'(?<![\w.])%s(?![\w\'])' % re.escape(m), t)
                                                    for m in longs)
                       for t in decls):
                    out.append(('Def_' + D['name'], 'declaration `%s` has a short name that a statement binds as '
                                'a variable (false imports in preambles); rename it' % n))
    return out


def title_mismatch(items, miles):
    """[(where, why)] for a milestone whose title differs from its theorem's title.

    They are different fields on different endpoints, written at different times, and they drift:
    on Monod (2026-09-29) all 18 differed, and several milestone titles dropped content the
    statement proves (M16 dropped C¹, Proposition 7 dropped its second alternative). The theorem
    title is the one checked against the Lean; the milestone title should repeat it. References
    are skipped: their theorem titles belong to already-published theorems."""
    out = []
    for k, (t, _) in miles.items():
        if k.startswith('ref:') or k not in items:
            continue
        tt = items[k].get('theorem_title')
        if tt and t != tt:
            out.append((k + ' milestone', 'milestone title differs from the theorem title (%r vs %r)' % (t, tt)))
    return out


def double_backslash(items, miles, desc):
    """[(where, why)] for uploaded prose with `\\\\` before a letter inside math.

    A raw-string prose file keeps both backslashes of `\\\\mathbf`, which KaTeX renders as a line
    break followed by the letters "mathbf". Monod's GRat ≅ T statement shipped `$G(\\\\mathbf{Z})$`
    that way and the human caught it in review (2026-09-29). A genuine `\\\\` line break is never
    followed directly by a letter in our prose, so this has no false positives so far."""
    texts = [('description', desc)]
    for k, it in items.items():
        for f in ('natural_language_statement', 'source'):
            if it.get(f):
                texts.append((k, it[f]))
    for k, (t, d) in miles.items():
        texts.append((k + ' milestone', t + '\n' + d))
    out = []
    for where, t in texts:
        for m in re.finditer(r'\$[^$]*?(\\\\[A-Za-z]+)[^$]*?\$', t):
            out.append((where, 'doubled backslash `%s` in math (renders as a line break)' % m.group(1)))
        # a quote escaped inside a raw string keeps its backslash: Moore's §2(e) milestone shipped
        # `$\Gamma\'$` (KaTeX reads `\'` as an accent), and two patch scripts left `\"` in prose
        # (2026-10-01). Our prose never wants either.
        for m in re.finditer(r'.{0,20}\\[\'"]', t):
            out.append((where, 'escaped quote `%s` (a raw-string backslash leaked into prose)' % m.group(0)))
    return out


def goal_unquoted(M, items):
    """[(goal, why)] when the source's sentence for the goal never reaches the platform.

    The goal is never a milestone, so its milestone_description -- where every other item carries
    the quoted source sentence -- is not uploaded. Unless its natural-language statement quotes the
    sentence, the Draft shows the goal only as a paraphrase, and the live-Draft quote recheck
    never sees it (QFS and Monod, 2026-09-27)."""
    it = items.get(M.GOAL) or {}
    if it.get('kind') != 'theorem':
        return []                               # a published goal: its NLS is patched by hand
    T = [T for T in M.THEOREMS if T['name'] == M.GOAL][0]
    nls = norm(it.get('natural_language_statement'))
    q = re.search(r'“(.+?)”', norm(T.get('milestone_description')))
    if q and norm(q.group(1))[:80] in nls:
        return []
    if not q and '“' in nls:
        return []
    return [(M.GOAL, "goal's natural-language statement does not quote the source sentence "
                     '(the goal has no milestone, so that is the only place it can appear)')]


def main():
    if len(sys.argv) < 3 or sys.argv[2] not in ('verify', 'upload'):
        sys.exit(__doc__)
    mdir, cmd, go = os.path.abspath(sys.argv[1]), sys.argv[2], '--go' in sys.argv[3:]
    M = load(mdir)
    from p2m import call
    stp = os.path.join(mdir, 'proposal.json')
    st = json.load(open(stp)) if os.path.exists(stp) else {}
    st.setdefault('items', {})

    if cmd == 'verify':
        if 'id' not in st:
            sys.exit('no proposal.json -- nothing uploaded yet')
        bad, d, lm = diff(M, mdir, call, st)
        its, mls, _, _ = desired(M, mdir)
        bad += unneeded_refs(M, mdir, its, mls, call)
        bad += goal_unquoted(M, its)
        bad += title_mismatch(its, mls)
        bad += short_bundle_names(M, mdir)
        bad += author_pronouns(its, mls, open(os.path.join(mdir, 'description.md'), encoding='utf-8').read())
        bad += dead_lean_refs(M, mdir, its, mls, open(os.path.join(mdir, 'description.md'), encoding='utf-8').read(), call)
        bad += bundle_relation_docstrings(M, mdir)
        bad += double_backslash(its, mls, open(os.path.join(mdir, 'description.md'), encoding='utf-8').read())
        bad += deprecated_refs(M, its, mls, open(os.path.join(mdir, 'description.md'), encoding='utf-8').read(), call)
        import decisions
        bad += decisions.check(mdir)
        # the workspace's statement modules are the plan: a proof compiled against a stale stub
        # proves a statement the Draft no longer has (stubs.py)
        import stubs
        bad += [('stubs', p) for p in stubs.sync(mdir, check=True)[0]]
        for k, what in bad:
            print('BAD', k, what)
        print('items %d  milestones %d  status %s | BAD %d'
              % (len(d.get('items') or []), len(lm), d.get('status'), len(bad)))
        sys.exit(1 if bad else 0)

    items, miles, order, desc = desired(M, mdir)

    def do(m, p, b, what):
        if not go:
            print('   would %s %s  (%s)' % (m, p, what)); return {'id': 'dry'}
        r = call(m, p, b)
        if isinstance(r, dict) and '__error' in r:
            sys.exit('FAILED %s: %s' % (what, str(r['__error'])[:400]))
        return r

    def save():
        if go:
            json.dump(st, open(stp, 'w'), indent=1)

    live_d = None
    if 'id' not in st:
        r = do('POST', '/mission-proposals', {'name': M.NAME, 'description': desc,
                                               'mission_type': M.MISSION_TYPE, 'field_ids': M.FIELDS}, 'create')
        if not go:
            print('dry run: would create the proposal and every item'); return
        st['id'] = r.get('id') or (r.get('proposal') or {}).get('id'); save()
        bad = [(k, 'missing item') for k in items] + [(k, 'missing milestone') for k in miles] \
            + [('item_order', ''), ('goal', '')]
    else:
        bad, live_d, _ = diff(M, mdir, call, st)
    # confirmation bookkeeping: the platform clears a human's confirmation when an item is
    # edited, so say exactly which confirmations this upload touches, before and after
    ids0 = st.get('items', {})
    name_of = {v: k for k, v in ids0.items()}
    conf_before = {}
    if live_d:
        conf_before = {it['id']: it.get('confirmed_at') for it in live_d.get('items') or []
                       if it.get('confirmed_at')}
    touched = {ids0.get(k) for k, w in bad if ids0.get(k) in conf_before}
    for iid in sorted(touched, key=lambda i: name_of.get(i, i)):
        whats = sorted({w for k, w in bad if ids0.get(k) == iid})
        print('   CONFIRMED item %s is %s: %s (confirmed %s)' % (
            name_of.get(iid, iid), 'edited by this upload' if go else 'would be edited',
            ', '.join(whats), conf_before[iid]))
    MS = ('missing milestone', 'milestone title', 'milestone description')
    todo = {k for k, w in bad if w not in MS}              # items (and the proposal-level keys)
    ms_todo = {k for k, w in bad if w in MS}                # milestones, tracked separately so an
    pid = st['id']                                          # item edit never re-posts its milestone
    for k, want in items.items():
        if k in todo:
            r = do('POST', '/mission-proposals/%s/items' % pid, want, k)
            if go:
                st['items'][k] = r.get('id') or st['items'].get(k); save()
    for k, (t, dsc) in miles.items():
        if k in ms_todo:
            do('POST', '/mission-proposals/%s/milestones' % pid,
               {'item_id': st['items'].get(k), 'milestone_title': t, 'milestone_description': dsc}, 'milestone ' + k)
    if 'description' in todo:
        do('PATCH', '/mission-proposals/' + pid, {'description': desc}, 'description')
    if todo & {'item_order', 'goal'} or any(w == 'missing item' for _, w in bad):
        do('PATCH', '/mission-proposals/' + pid, {'item_order': [st['items'].get(k) for k in order]}, 'order')
        do('PATCH', '/mission-proposals/' + pid, {'main_item_id': st['items'].get(M.GOAL)}, 'goal')
    if go and conf_before:
        d2 = call('GET', '/mission-proposals/' + pid)
        d2 = d2.get('proposal', d2)
        after = {it['id']: it.get('confirmed_at') for it in d2.get('items') or []}
        cleared = [i for i in conf_before if not after.get(i)]
        for iid in sorted(cleared, key=lambda i: name_of.get(i, i)):
            print('   CONFIRMATION CLEARED: %s (was confirmed %s)' % (name_of.get(iid, iid), conf_before[iid]))
        print('   confirmations: %d before, %d cleared by this upload, %d kept'
              % (len(conf_before), len(cleared), len(conf_before) - len(cleared)))
    elif conf_before:
        print('   confirmations now: %d item(s) confirmed; %d would be touched'
              % (len(conf_before), len(touched)))
    for k, w in goal_unquoted(M, items):
        print('   NOTE %s: %s' % (k, w))
    for k, w in unneeded_refs(M, mdir, items, miles, call):
        print('   NOTE %s: %s' % (k, w))
    strays = [(k, w) for k, w in bad if w.startswith('stray')]
    for k, w in strays:
        print('   NOTE %s: %s -- not deleted; remove it deliberately if it should go' % (k, w))
    print('%s: %d difference(s)%s' % ('uploaded' if go else 'dry run', len(bad) - len(strays),
                                       '' if go else ' -- pass --go to apply'))
    if go:
        # keep the workspace's statement stubs equal to what was just uploaded (stubs.py)
        import stubs
        problems, written = stubs.sync(mdir)
        print('stubs: %d written%s' % (len(written), ''.join('\n   ' + p for p in problems)))


if __name__ == '__main__':
    main()
