"""Template prose for a carve's intermediate items, with no model call (`carve_prep.py
prose-template`).

dbenbenn (2026-10-24): the prose of a carved intermediate statement or bundle is rarely read in the
short term and stays patchable, and model-written prose had become the biggest cost of a carve. So
everything here is generated from the carve's own records: the plan, the generated files in
`publish/out/`, the declaration graph (`work/decl_graph.jsonl`, what Lean elaborated) and a small
metadata file about OpenAI's release (`oai_meta.json`). Nothing is said that those records do not
show: a statement's prose renders its Lean, names the split's declarations Lean records its type
using, and says which items import it; it makes no mathematical claim of its own.

Written: `prose/<slug>.md` for every intermediate statement (not the goal, not a `forced` named
result), `prose/<NAME>.md` for every bundle, and `explanations/<slug>.md` for every proof piece of
an intermediate statement. The goal and the forced nodes are listed as needing written prose.

Generated files are marked: prose carries the front-matter field `template:` (split_run reads only
`title` and `source`), and every generated file's sha1 is kept in `prose/.template.json` /
`explanations/.template.json` (an explanation is sent as it is, so it carries no marker of its
own). A file is regenerated only when it is absent or still the unchanged template; anything else
is written prose and is kept unless `force`.

oai_meta.json: {"title", "date", "family", "commit" (40 hex), "paper" (URL, optional),
"prefixes" (OpenAI module prefixes, e.g. ["OAI.Geometry.HeilbronnTriangle"]), "lean_root"
(optional: the fetched lean/ tree, to map a flattened module name `Sub_X` back to its path)}.
"""
import hashlib
import json
import os
import re
import sys

from . import carve as C
from .mission import front_matter

MARK = 'carve_prep prose-template'
MANIFEST = '.template.json'
SHIM_MODULES = {'Compat', 'StdSimplexCompat'}
REPO = 'https://github.com/openai/math'


def _sha(text):
    return hashlib.sha1(text.encode('utf-8')).hexdigest()


def _names(xs):
    xs = ['`%s`' % x for x in xs]
    if len(xs) <= 2:
        return ' and '.join(xs)
    return ', '.join(xs[:-1]) + ' and ' + xs[-1]


def _plural(n, one, many):
    return '%d %s' % (n, one if n == 1 else many)


# ---------------------------------------------------------------- reading a stub

DECL = re.compile(r'^[ \t]*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+(\S+)', re.M)


def stub_statement(text):
    """(declaration without its proof, current namespace, [open lines in force]) of a statement
    stub: `theorem name binders : type := by sorry` inside namespaces and sections."""
    m = DECL.search(text)
    if not m:
        raise ValueError('no theorem in the stub')
    head = text[:m.start()]
    stack = []                      # (kind, name, [opens])
    opens_root = []
    for line in head.split('\n'):
        s = line.strip()
        w = s.split()
        if not w:
            continue
        if w[0] == 'namespace' and len(w) > 1:
            stack.append(('ns', w[1], []))
        elif w[0] == 'section' or w[:2] == ['noncomputable', 'section']:
            stack.append(('sec', None, []))
        elif w[0] == 'end':
            if stack:
                stack.pop()
        elif w[0] == 'open':
            (stack[-1][2] if stack else opens_root).append(s)
    body = text[m.start():]
    k = body.rfind('sorry')
    j = body.rfind(':=', 0, k if k >= 0 else len(body))
    decl = body[:j].rstrip() if j >= 0 else body.rstrip()
    ns = '.'.join(x[1] for x in stack if x[0] == 'ns')
    opens = opens_root + [o for x in stack for o in x[2]]
    return decl, ns, opens


def imports_of(text):
    return re.findall(r'^import (\S+)', text, re.M)


# ---------------------------------------------------------------- the carve

class Context:
    def __init__(self, carve_dir, meta=None):
        d = os.path.abspath(carve_dir)
        self.d, self.P = d, os.path.join(d, 'publish')
        if not os.path.exists(os.path.join(self.P, 'plan.json')):
            sys.exit('no %s/plan.json: run carve_prep.py publish-prep first' % self.P)
        self.plan = json.load(open(os.path.join(self.P, 'plan.json'), encoding='utf-8'))
        cp = os.path.join(d, 'config.json')
        self.cfg = json.load(open(cp, encoding='utf-8')) if os.path.exists(cp) else {}
        self.meta = check_meta(meta if meta is not None else load_meta(d))
        self.consts = {}
        for g in (os.path.join(os.path.expanduser(self.cfg.get('work', '')), 'decl_graph.jsonl'),
                  os.path.join(d, 'work', 'decl_graph.jsonl')):
            if os.path.exists(g):
                consts, _, _ = C.load_decl_graph(g)
                self.consts = consts
                break
        else:
            sys.exit('no work/decl_graph.jsonl: run carve.py graph first')
        self.ext = set(self.plan.get('external', ()))
        self.targets = list(self.plan.get('targets') or self.cfg.get('targets') or sorted(self.ext))
        self.forced = set(self.plan.get('forced') or ()) | set(self.cfg.get('forced') or ())
        self.bundle_of = {n: b['name'] for b in self.plan['bundles'] for n in b['nodes']}
        self.ext_defs = dict(self.plan.get('external_defs') or self.cfg.get('external_defs') or {})
        self.lib = os.path.join(self.P, 'out', 'lib')
        self.sols = os.path.join(self.P, 'out', 'solutions')
        self.slug_name = {C.slug(C.statement_name(self.plan, n)): C.statement_name(self.plan, n)
                          for n in list(self.plan['stubs']) + list(self.plan['pieces'])}
        self.paths = module_paths(self.meta)
        self.versions = versions(self.cfg.get('src'))

    # files
    def read(self, *p):
        return open(os.path.join(*p), encoding='utf-8').read()

    def stub(self, node):
        return self.read(self.lib, 'Thm_%s.lean' % C.slug(C.statement_name(self.plan, node)))

    def solution(self, node):
        return self.read(self.sols, 'Sol_%s.lean' % C.slug(C.statement_name(self.plan, node)))

    def importers(self, module):
        """(bundles, statements, pieces) of this split whose generated file imports `module`."""
        bs, ss, ps = [], [], []
        for f in sorted(os.listdir(self.lib)):
            if f.endswith('.lean') and module in imports_of(self.read(self.lib, f)):
                (bs if f.startswith('Def_') else ss).append(f[4:-5])
        for f in sorted(os.listdir(self.sols)):
            if f.endswith('.lean') and module in imports_of(self.read(self.sols, f)):
                ps.append(f[4:-5])
        return bs, [self.slug_name.get(s, s) for s in ss], [self.slug_name.get(s, s) for s in ps]

    # names
    def owner(self, name):
        """The bundle node or external definition a constant belongs to (a field -> its structure)."""
        p = name
        while p:
            if p in self.bundle_of or p in self.ext_defs:
                return p
            if '.' not in p:
                return None
            p = p.rsplit('.', 1)[0]
        return None

    def module_short(self, node):
        m = (self.consts.get(node) or {}).get('m', '')
        return m.rsplit('.', 1)[-1] if m else None

    def link(self, short):
        p = self.paths(short)
        return '%s/blob/%s/%s' % (REPO, self.meta['commit'], p) if p else None

    # common text
    def release(self):
        m = self.meta
        return 'OpenAI, *%s*, OpenAI Math Release, %s, result family %s' % (m['title'], m['date'], m['family'])

    def source_head(self):
        m = self.meta
        paper = '; paper: %s' % m['paper'] if m.get('paper') else ''
        return 'OpenAI, %s, OpenAI Math Release, %s, %s (result family %s%s; Apache License 2.0)' % (
            m['title'], m['date'], REPO, m['family'], paper)

    def ported(self):
        v = self.versions
        if v:
            return 'ported to Lean %s and Mathlib %s' % v
        return "ported to this platform's Lean and Mathlib"

    def lean_dirs(self):
        return ', '.join('lean/' + p.replace('.', '/') for p in self.meta['prefixes'])


def load_meta(d):
    p = os.path.join(d, 'oai_meta.json')
    if not os.path.exists(p):
        sys.exit('no %s: write {"title", "date", "family", "commit", "paper", "prefixes"} '
                 '(p2mlib/prosetemplate.py)' % p)
    return json.load(open(p, encoding='utf-8'))


def check_meta(m):
    for k in ('title', 'date', 'family', 'commit', 'prefixes'):
        if not m.get(k):
            sys.exit('oai_meta.json: no %r' % k)
    if not re.fullmatch(r'[0-9a-f]{40}', m['commit']):
        sys.exit('oai_meta.json: commit must be the full 40-hex commit (links pin it)')
    if len(m['prefixes']) > 1 and not m.get('lean_root'):
        sys.exit('oai_meta.json: several prefixes need lean_root to map modules to paths')
    return m


def module_paths(meta):
    """short module name (Solutions.FOLDER.<short>) -> its path in openai/math, or None."""
    table = None
    if meta.get('lean_root'):
        from .oaiport import module_sources
        table = {s: 'lean/' + oai.replace('.', '/') + '.lean'
                 for oai, (s, _) in module_sources(os.path.expanduser(meta['lean_root']), meta['prefixes']).items()}

    def path(short):
        if not short or short in SHIM_MODULES:
            return None
        if table is not None:
            return table.get(short)
        # oai_port_modules flattens a nested Sub/X.lean to Sub_X (OpenAI's file names are CamelCase)
        return 'lean/%s/%s.lean' % (meta['prefixes'][0].replace('.', '/'), short.replace('_', '/'))
    return path


def versions(ws):
    """(Lean version, Mathlib short commit) of the workspace, or None."""
    try:
        tc = open(os.path.join(ws, 'lean-toolchain')).read().strip()
        man = json.load(open(os.path.join(ws, 'lake-manifest.json')))
        rev = next(p['rev'] for p in man['packages'] if p['name'] == 'mathlib')
        return tc.rsplit(':', 1)[-1].lstrip('v'), rev[:7]
    except (OSError, TypeError, ValueError, StopIteration, KeyError):
        return None


# ---------------------------------------------------------------- the texts

def _context_line(ns, opens):
    bits = []
    if ns:
        bits.append('namespace `%s`' % ns)
    if opens:
        bits.append('with %s' % ', '.join('`%s`' % o for o in opens))
    return ' (%s)' % ', '.join(bits) if bits else ''


def _uses(ctx, node):
    """{bundle or published module: [names]} of the split's / published definitions the
    statement's type uses (Lean's record `t`)."""
    by = {}
    for n in (ctx.consts.get(node) or {}).get('t', ()):
        o = ctx.owner(n)
        if o is None or o == node:
            continue
        where = ctx.bundle_of.get(o) or ctx.ext_defs.get(o)
        lst = by.setdefault(where, [])
        if C.pubname(o) not in lst:
            lst.append(C.pubname(o))
    return by


def statement_prose(ctx, node):
    name = C.statement_name(ctx.plan, node)
    decl, ns, opens = stub_statement(ctx.stub(node))
    short = ctx.module_short(node)
    link = ctx.link(short)
    path = ctx.paths(short)
    title = '%s: intermediate lemma from OpenAI, %s' % (name, ctx.meta['title'])
    if len(title) > 200:
        title = '%s (OpenAI intermediate lemma)' % name
    src = ctx.source_head() + ('; Lean: %s (declaration %s)' % (link, C.pubname(node)) if link else '')
    goals = _names(ctx.targets)
    out = ['---', 'title: ' + title, 'source: ' + src, 'template: ' + MARK, '---',
           "An intermediate lemma of the split of OpenAI's proof of %s, carved from OpenAI's "
           'openai/math development for this platform. The statement and its proof are OpenAI\'s '
           '(%s, [github.com/openai/math](%s), Apache License 2.0)%s, %s.' % (
               goals, ctx.release(), REPO,
               ('; in Lean it is the declaration `%s` of [%s](%s) at commit %s' % (
                   C.pubname(node), path, link, ctx.meta['commit'][:7])) if link else '',
               ctx.ported()),
           '',
           '**The statement**, as published%s:' % _context_line(ns, opens),
           '', '```lean', decl, '```', '']
    uses = _uses(ctx, node)
    if uses:
        parts = []
        for where in sorted(uses, key=lambda w: (w not in {b['name'] for b in ctx.plan['bundles']}, w)):
            names = _names(uses[where])
            if any(where == b['name'] for b in ctx.plan['bundles']):
                parts.append('%s (definitions bundle `%s` of this split)' % (names, where))
            else:
                parts.append('%s (the published bundle `%s`)' % (names, where.split('.')[-1]))
        out += ['**Definitions.** The statement is written with %s.' % '; '.join(parts), '']
    bs, ss, ps = ctx.importers('Theorems.Thm_' + C.slug(name))
    used = ['the proof%s of %s' % ('s' if len(ps) > 1 else '', _names(ps))] if ps else []
    if ss:
        used.append('the statement%s %s' % ('s' if len(ss) > 1 else '', _names(ss)))
    if bs:
        used.append('the definitions bundle%s %s' % ('s' if len(bs) > 1 else '', _names(bs)))
    if used:
        subj = ' and '.join(used)
        out += ['**Used by.** %s%s of this split import%s it.' % (
            subj[0].upper(), subj[1:], 's' if len(ps) + len(ss) + len(bs) == 1 else ''), '']
    else:
        out += ['**Used by.** No other item of this split imports it.', '']
    return '\n'.join(out)


KIND = [('definition', 'definitions'), ('inductive type or structure', 'inductive types or structures'),
        ('instance', 'instances'), ('theorem', 'theorems'), ('other declaration', 'other declarations')]


def kind_of(rec):
    if rec.get('i'):
        return 'instance'
    k = rec.get('k')
    if k == 'theorem':
        return 'theorem'
    if k == 'inductive':
        return 'inductive type or structure'
    if k in ('def', 'opaque', 'abbrev', 'axiom'):
        return 'definition'
    return 'other declaration'


def bundle_prose(ctx, b):
    name = b['name']
    text = ctx.read(ctx.lib, 'Def_%s.lean' % name)
    counts = {}
    types = []
    for n in b['nodes']:
        k = kind_of(ctx.consts.get(n) or {})
        counts[k] = counts.get(k, 0) + 1
        if k in ('definition', 'inductive type or structure'):
            types.append(C.pubname(n))
    kinds = [_plural(counts[one], one, many) for one, many in KIND if counts.get(one)]
    mods = sorted(set(m.split('.')[-1] for m in re.findall(r'^-- module (\S+)', text, re.M)) - SHIM_MODULES)
    title = 'Definitions bundle %s of the split of OpenAI, %s' % (name, ctx.meta['title'])
    if len(title) > 200:
        title = 'OpenAI split: definitions bundle %s' % name
    src = ctx.source_head() + '; definitions carved from %s at commit %s' % (ctx.lean_dirs(), ctx.meta['commit'][:7])
    out = ['---', 'title: ' + title, 'source: ' + src, 'template: ' + MARK, '---',
           "A definitions bundle of the split of OpenAI's proof of %s, carved from OpenAI's openai/math "
           "development (%s, [github.com/openai/math](%s) at commit %s, Apache License 2.0) and %s. "
           "The declarations and their proofs are OpenAI's." % (
               _names(ctx.targets), ctx.release(), REPO, ctx.meta['commit'][:7], ctx.ported()), '']
    line = '**Contents.** It holds %s of OpenAI\'s Lean%s.' % (
        _plural(len(b['nodes']), 'declaration', 'declarations'),
        # a bundle whose declarations have no recorded kind (PinchedHartogs extension 2026-10-25)
        '' if not kinds else ': ' + (', '.join(kinds[:-1]) + ' and ' + kinds[-1] if len(kinds) > 1 else kinds[0]))
    if types:
        cap = 40
        shown = sorted(types)[:cap]
        line += ' The definitions and types are %s%s.' % (
            ', '.join('`%s`' % t for t in shown), ' and %d more' % (len(types) - cap) if len(types) > cap else '')
    out += [line, '']
    if mods:
        refs = module_refs(ctx, mods)
        out += ['**Sources.** They come from these modules of %s, in whole or in part: %s.' % (
            ctx.lean_dirs(), ', '.join(refs)), '']
    own = {x['name'] for x in ctx.plan['bundles']}
    imps = imports_of(text)
    pub = [i.split('.')[-1] for i in imps if i.startswith('Definitions.') and i.split('Def_', 1)[-1] not in own]
    ours = [i.split('Def_', 1)[-1] for i in imps if i.startswith('Definitions.') and i.split('Def_', 1)[-1] in own]
    thms = [ctx.slug_name.get(i.split('Thm_', 1)[-1], i) for i in imps if i.startswith('Theorems.')]
    parts = []
    if pub:
        parts.append('the published bundle%s %s' % ('s' if len(pub) > 1 else '', _names(pub)))
    if ours:
        parts.append('the bundle%s %s of this split' % ('s' if len(ours) > 1 else '', _names(ours)))
    if thms:
        parts.append('the published statement%s %s' % ('s' if len(thms) > 1 else '', _names(thms)))
    out += ['**Imports.** %s' % ('It imports %s.' % '; '.join(parts) if parts else
                                 'It imports no bundle or statement, only Mathlib.'), '']
    bs, ss, ps = ctx.importers('Definitions.Def_' + name)
    parts = []
    if bs:
        parts.append('the bundle%s %s' % ('s' if len(bs) > 1 else '', _names(bs)))
    if ss:
        parts.append('the statement%s %s' % ('s' if len(ss) > 1 else '', _names(ss)))
    if ps:
        parts.append('the proof%s of %s' % ('s' if len(ps) > 1 else '', _names(ps)))
    out += ['**Imported by** (directly, in this split): %s.' % ('; '.join(parts) if parts else 'none'), '']
    return '\n'.join(out)


LINK_MODULES = 12


def module_refs(ctx, mods):
    """Module names, each linked to its file at the commit when there are only a few."""
    refs = []
    for m in mods:
        lk = ctx.link(m) if len(mods) <= LINK_MODULES else None
        refs.append('[`%s`](%s)' % (m, lk) if lk else '`%s`' % m)
    return refs


def _patch_notes(ctx, sol):
    """The `why` of each recorded port repair whose new text is in this file (deduplicated)."""
    files = []
    p = ctx.cfg.get('patches')
    if isinstance(p, str):
        files.append(p if os.path.isabs(p) else os.path.join(ctx.d, p))
    files.append(os.path.join(ctx.d, 'port_patches.json'))
    seen = {}
    for f in files:
        if not os.path.exists(f):
            continue
        try:
            ps = json.load(open(f, encoding='utf-8'))
        except ValueError:
            continue
        for x in ps if isinstance(ps, list) else ():
            new = x.get('new', x.get('literal_new')) or ''
            why = ' '.join((x.get('why') or '').split())
            if why and len(new.strip()) >= 30 and new in sol:
                seen[why] = seen.get(why, 0) + 1
    return seen


def explanation(ctx, node):
    name = C.statement_name(ctx.plan, node)
    decl, ns, opens = stub_statement(ctx.stub(node))
    sol = ctx.solution(node)
    m = re.search(r'^theorem solution\s*:\s*type_of%\s*@(\S+)', sol, re.M)
    oai = m.group(1) if m else None
    piece = ctx.plan['pieces'].get(node, {})
    keep = [k for k in piece.get('keep', ())]
    mods = sorted({ctx.module_short(k) for k in keep if ctx.module_short(k)} - SHIM_MODULES)
    refs = module_refs(ctx, mods)
    imps = imports_of(sol)
    own = {x['name'] for x in ctx.plan['bundles']}
    pubb = [i.split('.')[-1] for i in imps if i.startswith('Definitions.') and i.split('Def_', 1)[-1] not in own]
    ours = [i.split('Def_', 1)[-1] for i in imps if i.startswith('Definitions.') and i.split('Def_', 1)[-1] in own]
    thms = [ctx.slug_name.get(i.split('Thm_', 1)[-1], i) for i in imps if i.startswith('Theorems.')]
    tex = name.replace('_', r'\_')
    out = ['$$\\mathtt{%s}$$' % tex, '',
           "This file proves the published statement `%s`, an intermediate lemma of the split of OpenAI's "
           'proof of %s. In Lean%s:' % (name, _names(ctx.targets), _context_line(ns, opens)),
           '', '```lean', decl, '```', '']
    clean = not re.search(r'(?<![\w.])(sorry|admit)(?![\w])', sol) and not re.search(r'^\s*axiom\s', sol, re.M)
    hyp = '**Hypotheses used.** Those of the statement'
    if clean:
        hyp += '. The file contains no `sorry` and declares no `axiom`.'
    else:
        hyp += '.'
    if thms:
        hyp += ' It also uses the published statement%s %s, imported as %s.' % (
            's' if len(thms) > 1 else '', _names(thms), 'lemmas' if len(thms) > 1 else 'a lemma')
    out += [hyp, '']
    idea = ("**Proof idea.** The proof is OpenAI's (%s). The file is carved from OpenAI's openai/math "
            'development: it keeps the %s of that development that this proof reaches' % (
                ctx.release(), _plural(len(keep), 'declaration', 'declarations')))
    if refs:
        idea += ', from the module%s %s of %s' % ('s' if len(refs) > 1 else '', ', '.join(refs), ctx.lean_dirs())
    idea += ', %s.' % ctx.ported()
    out += [idea, '']
    steps = []
    dparts = []
    if pubb:
        dparts.append('the published bundle%s %s' % ('s' if len(pubb) > 1 else '', _names(pubb)))
    if ours:
        dparts.append('the definitions bundle%s %s of this split' % ('s' if len(ours) > 1 else '', _names(ours)))
    if dparts:
        steps.append("OpenAI's definitions come from %s, which the file imports." % ' and '.join(dparts))
    if thms:
        steps.append('The published statement%s %s %s imported rather than re-proved.' % (
            's' if len(thms) > 1 else '', _names(thms), 'are' if len(thms) > 1 else 'is'))
    if oai:
        steps.append("OpenAI's own proof of the statement, kept as `%s`, closes it; `theorem solution` is "
                     'that theorem.' % oai.rsplit('.', 1)[-1])
    out += ['**Steps.**'] + ['%d. %s' % (i + 1, s) for i, s in enumerate(steps)] + ['']
    changes = []
    if oai:
        changes.append("OpenAI's copy of the theorem is renamed `%s`, so that `solution` is the only "
                       'declaration matching the published statement.' % oai.rsplit('.', 1)[-1])
    cm = re.search(r'section OAICompat434\n(.*?)\nend OAICompat434', sol, re.S)
    if cm:
        compat = re.findall(r'^theorem (\S+)', cm.group(1), re.M)
        if compat:
            changes.append('%s, %s of newer Lean versions that this environment lacks, %s declared '
                           'at the top of the file in namespace `OAI`.' % (
                               _names(compat), 'lemmas' if len(compat) > 1 else 'a lemma',
                               'are' if len(compat) > 1 else 'is'))
    if 'set_option linter.all false' in sol:
        changes.append('Module sections start with `set_option` lines that turn linters off, for speed; '
                       'linters only emit warnings, so this does not change what is proved.')
    for why, n in _patch_notes(ctx, sol).items():
        changes.append('A recorded proof repair%s: %s' % (
            ' (%d places)' % n if n > 1 else '', why if why.endswith('.') else why + '.'))
    if changes:
        out += ['**What the port changed.**'] + ['- ' + c for c in changes] + ['']
    out += ["**Source and credit.** The mathematics and the Lean code are OpenAI's: *%s*, OpenAI Math Release, "
            '%s, in the repository [github.com/openai/math](%s) (result family %s; Lean in %s at commit %s, '
            'Apache License 2.0).' % (ctx.meta['title'], ctx.meta['date'], REPO, ctx.meta['family'],
                                      ctx.lean_dirs(), ctx.meta['commit'][:7]), '']
    return '\n'.join(out)


# ---------------------------------------------------------------- writing

def _manifest(P, sub):
    p = os.path.join(P, sub, MANIFEST)
    return json.load(open(p)) if os.path.exists(p) else {}


def is_template(P, rel):
    """Is publish/<rel> (prose/X.md or explanations/X.md) an unchanged generated file?"""
    sub, f = rel.split('/', 1)
    p = os.path.join(P, rel)
    if not os.path.exists(p):
        return False
    text = open(p, encoding='utf-8').read()
    if sub == 'prose':
        try:
            fields, _ = front_matter(text)
        except ValueError:
            return False
        if fields.get('template') != MARK:
            return False
    return _manifest(P, sub).get(f) == _sha(text)


def write_templates(carve_dir, meta=None, force=False):
    """Write every template; returns {'written', 'kept', 'needs_written'} (relative paths / labels)."""
    ctx = Context(carve_dir, meta)
    P = ctx.P
    texts = {}
    for b in ctx.plan['bundles']:
        texts['prose/%s.md' % b['name']] = bundle_prose(ctx, b)
    need = []
    for n in ctx.plan['stubs']:
        why = 'goal' if (n in ctx.ext or n in ctx.targets) else 'forced' if n in ctx.forced else None
        if why:
            if n not in ctx.ext:
                need.append('statement %s (%s)' % (C.statement_name(ctx.plan, n), why))
            continue
        texts['prose/%s.md' % C.slug(C.statement_name(ctx.plan, n))] = statement_prose(ctx, n)
    for n in ctx.plan['pieces']:
        why = 'goal' if (n in ctx.ext or n in ctx.targets) else 'forced' if n in ctx.forced else None
        if why:
            need.append('explanation %s (%s)' % (C.statement_name(ctx.plan, n), why))
            continue
        texts['explanations/%s.md' % C.slug(C.statement_name(ctx.plan, n))] = explanation(ctx, n)
    rep = {'written': [], 'kept': [], 'needs_written': need}
    mans = {s: _manifest(P, s) for s in ('prose', 'explanations')}
    for rel, t in sorted(texts.items()):
        sub, f = rel.split('/', 1)
        p = os.path.join(P, rel)
        if os.path.exists(p) and not force and not is_template(P, rel):
            rep['kept'].append(rel)
            continue
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w', encoding='utf-8').write(t)
        mans[sub][f] = _sha(t)
        rep['written'].append(rel)
    for s, m in mans.items():
        os.makedirs(os.path.join(P, s), exist_ok=True)
        json.dump(m, open(os.path.join(P, s, MANIFEST), 'w'), indent=1, sort_keys=True)
    return rep
