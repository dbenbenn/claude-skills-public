#!/usr/bin/env python3
"""Audit the prose that explains a source-audit gap: does the natural-language statement's note
account for each gap accurately, and does it claim anything the Lean or a citation does not back?

usage: caveat_audit.py stage   MISSION_DIR NAME [--cite FILE ...] [--force]   -> prints the auditor prompt
       caveat_audit.py collect MISSION_DIR NAME                     -> verdict into readbacks/, exit 1
                                                                       unless `CAVEATS: adequate`

The source audit (source_audit.py) never sees the natural-language statement, by design: prose
must not talk it out of a real gap. So when the human decides a gap is to be *documented* rather
than fixed, nothing checks the documentation. This auditor does. It is given the quoted source
sentence and its page images, the blind read-back (what the Lean says), the source auditor's
claims and coverage (the gaps), the title and natural-language statement, and any cited text
(`--cite`, e.g. an extracted book the note relies on). It answers: is each gap named and
explained accurately; is every assertion in the prose true and backed by the Lean or a citation;
does the prose say more or less than the Lean; is the title accurate.

First use: Monod M6 (2026-09-29), whose note documents two gaps (measurability of the relation,
σ-finiteness and non-singularity). It judged the note adequate, verified the σ-finiteness
argument step by step, and caught one overstatement ("on a standard Borel space", which the page
never says).
"""
import os, re, shutil, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # p2mlib
from stage_auditor import ROOT
import draft
import source_audit as SA

BRIEF = """# Caveat audit

You are auditing the PROSE that accompanies one formalized statement from a mathematics paper.
Read nothing outside this directory; write only `verdict.md` here.

Files:
- `milestone.md`: the milestone description; its opening quotation is the source sentence, any
  *Route* / *External* paragraph is the captain's explanation.
- `page-*.png`: the source pages. Read the sentence and its context on the image.
- `readback.md`: a blind reviewer's plain-mathematics description of the Lean statement. Treat it
  as ground truth for what the Lean says.
- `claims.md`, `coverage.md`: an earlier auditor's atomic claims of the source sentence and its
  comparison of the Lean against them (the gaps it found: MISSING / WEAKER / EXTRA).
- `nls.md`: the title and the natural-language statement shown to readers beside the Lean,
  including any *Formalization Note*.
- `cite-*`: texts the prose cites, if any.
- `bundle-*.md`: the natural-language notes of the mission's definition bundles. A definition's
  reading, any ambiguity in the source and any counterexample are explained ONCE there, and the
  statement prose deliberately does not repeat them (the human reviewer's rule). A gap that comes
  from a shared definition is accounted for when the bundle note explains it.

Answer, each in its own section of `verdict.md`:
1. For each gap in `coverage.md`, is it named in the prose and explained accurately? Would a
   mathematician reading the title, statement and note understand exactly how the Lean differs
   from the source sentence?
2. Is every factual assertion in the title, statement, note and milestone prose correct? Check it
   against `readback.md` (the Lean), the page images, and any cited text. Flag every step that is
   asserted without justification, and every overclaim (e.g. attributing to the source what it
   only implies).
3. Does the natural-language statement say anything the Lean does not, or omit anything the Lean
   assumes or concludes?
4. Is the title accurate for the Lean?

End `verdict.md` with one line: `CAVEATS: adequate` or `CAVEATS: inadequate: <items>`.
Reply in at most eight lines.
"""


def slug(mdir, name):
    return ('cav-%s-%s' % (os.path.basename(os.path.abspath(mdir)), name))[:150]


def stage(mdir, name, cites, force=False):
    mdir = os.path.abspath(mdir)
    M = draft.load(mdir)
    T = SA.item(M, name)
    rb = os.path.join(mdir, 'readbacks', name)
    for ext in ('readback', 'claims', 'coverage'):
        if not os.path.exists(rb + '.%s.md' % ext):
            sys.exit('missing readbacks/%s.%s.md -- run the read-back and source audit first' % (name, ext))
    # refuse to restage over a live auditor (it deleted the directory before 2026-10-02; the guard
    # stage_auditor has had since four auditors lost their work)
    from p2mlib.staging import fresh_dir, render_pages
    d = fresh_dir(ROOT, slug(mdir, name), force=force)
    open(os.path.join(d, 'brief.md'), 'w', encoding='utf-8').write(BRIEF)
    for ext in ('readback', 'claims', 'coverage'):
        shutil.copy(rb + '.%s.md' % ext, os.path.join(d, ext + '.md'))
    open(os.path.join(d, 'milestone.md'), 'w', encoding='utf-8').write(T.get('milestone_description', '') + '\n')
    open(os.path.join(d, 'nls.md'), 'w', encoding='utf-8').write(
        '# Title\n\n%s\n\n# Natural-language statement\n\n%s\n' % (T.get('title', ''), T.get('nls', '')))
    own = bool(T.get('source_pdf'))
    pdf = os.path.join(mdir, T.get('source_pdf') or getattr(M, 'SOURCE_PDF', ''))
    off = T.get('pdf_page_offset', 0) if own else getattr(M, 'PDF_PAGE_OFFSET', 0)
    want = SA.pages(T['page']) + ([] if own else SA.pages(getattr(M, 'CONTEXT_PAGES', ''))) \
        + SA.pages(T.get('context_pages', ''))
    # a bundle drawing on several papers renders every part, as source_audit does: with only the
    # first paper's pages the F-amenability bundle's caveat auditor could not check the Kaimanovich,
    # JMMS or Monod quotations (2026-09-30)
    parts = T.get('source_parts')
    if parts:
        for part_pdf, part_pages, part_off in parts:
            render_pages(os.path.join(mdir, part_pdf), SA.pages(part_pages), part_off, d,
                         tag=os.path.splitext(os.path.basename(part_pdf))[0])
    else:
        render_pages(pdf, sorted(set(want)), off, d)
    for c in cites:
        shutil.copy(c, os.path.join(d, 'cite-' + os.path.basename(c)))
    # the bundle notes: statements do not relitigate a shared definition (dbenbenn, 2026-10-01),
    # so without them the auditor flags every statement that uses a corrected definition, as it
    # did on Moore's Lemma 3.10 (Exel's composition law, explained only in the §3 bundle note)
    for D in getattr(M, 'DEFINITIONS', []):
        if D.get('nls'):
            open(os.path.join(d, 'bundle-%s.md' % D['name']), 'w', encoding='utf-8').write(
                '# %s\n\n%s\n' % (D.get('title', D['name']), D['nls']))
    print('Work only inside %s. Everything below is relative to it.\n\nRead brief.md and follow it '
          'exactly. Do not read or write anything outside this directory.' % d)


def collect(mdir, name):
    mdir = os.path.abspath(mdir)
    d = os.path.join(ROOT, slug(mdir, name))
    v = os.path.join(d, 'verdict.md')
    if not os.path.exists(v):
        sys.exit('no verdict.md in %s' % d)
    dst = os.path.join(mdir, 'readbacks', name + '.caveats.md')
    shutil.copy(v, dst)
    m = re.search(r'^CAVEATS:\s*(.+)$', open(v, encoding='utf-8').read(), re.M)
    line = m.group(1).strip() if m else '(no CAVEATS line)'
    print('CAVEATS', line, '->', dst)
    shutil.rmtree(d)
    sys.exit(0 if line.lower().startswith('adequate') else 1)


if __name__ == '__main__':
    a = sys.argv[1:]
    if len(a) >= 3 and a[0] == 'stage':
        force = '--force' in a
        a = [x for x in a if x != '--force']
        cites = a[a.index('--cite') + 1:] if '--cite' in a else []
        stage(a[1], a[2], cites, force)
    elif len(a) == 3 and a[0] == 'collect':
        collect(a[1], a[2])
    else:
        sys.exit(__doc__)
