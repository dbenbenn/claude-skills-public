#!/usr/bin/env python3
"""Source-side audit: what does the source sentence claim, and does the formalization say it?

usage: source_audit.py stage   MISSION_DIR NAME [--pages 12-14]   -> phase 1 prompt
       source_audit.py decisions MISSION_DIR                   -> DECISIONS.md: every finding on the
                                                                  goal and milestones, for the human
                                                                  to decide (the gap review; see
                                                                  decisions.py)
       source_audit.py reveal  MISSION_DIR NAME                   -> phase 2 message
       source_audit.py collect MISSION_DIR NAME                   -> claims/coverage into readbacks/

The blind read-back (stage_auditor.py) says what the Lean says, and by design never sees the
source, so it cannot notice that the Lean says less than the source. Garrido III's M3 showed the
cost: "aua = (u_1, u_0)" also asserts aua in St(1), the statement dropped it, the natural-language
statement's "that is" hid the drop, and the read-back auditor's notes listed "Not that a u a in
St(1)" among five boilerplate non-claims where nobody would notice it.

This auditor works from the other side, in two enforced phases:

  1. `stage` gives it only the source: the quoted sentence (the “…” of the milestone description,
     never the captain's Route prose or the natural-language statement) and page images, context
     pages included, since notation is set there. It writes claims.md -- every atomic claim,
     notation-carried ones marked -- and replies.
  2. `reveal` then copies the item's blind readback.md into its directory and prints the message
     to continue it with; it writes coverage.md: each claim COVERED / WEAKER / MISSING, a near-miss
     object for each gap, and a VERDICT line.

`collect` files claims.md and coverage.md beside the item's read-back and exits 1 unless the
verdict is `faithful`. mission.py (draft.py's) may set SOURCE_PDF (path relative to MISSION_DIR)
CONTEXT_PAGES ('12-13') and PDF_PAGE_OFFSET (PDF page minus printed page, for a journal
reprint whose PDF does not start at the printed page 1); an item may add `context_pages` (e.g. '4,7', where the notions it
uses are defined), and a cited external result its own `source_pdf` (and `pdf_page_offset`);
--pages overrides the item's own page field.

The goal is audited like any milestone: it keeps its milestone_description (the quoted sentence)
in the mission data even though draft.py never posts it as a milestone.
"""
import os, re, shutil, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from stage_auditor import ROOT, teardown  # same staging root as the read-back auditors
import draft


def item(M, name):
    # a definitions bundle is audited too, under the key of its read-back (`Def_<name>`): its
    # `source_pages` are where the source sets up its objects (Monod 2026-09-29: G, H and amenable
    # relations were never defined, and nothing compared the bundle with the source)
    if name.startswith('Def_'):
        for D in getattr(M, 'DEFINITIONS', []):
            if 'Def_' + D['name'] == name:
                if not D.get('source_pages'):
                    sys.exit('%s: give the bundle `source_pages` in mission.py' % name)
                return dict(D, name=name, page=D['source_pages'], bundle=True)
    for T in M.THEOREMS:
        if T['name'] == name:
            return T
    for R in getattr(M, 'REFERENCES', []):   # a published item the mission audits (has `page`)
        if R['theorem_name'] == name and R.get('page'):
            return dict(R, name=name)
    sys.exit('no theorem %s in mission.py' % name)


def pages(spec):
    out = set()
    for part in str(spec).replace('–', '-').split(','):
        m = re.match(r'\s*(\d+)(?:\s*-\s*(\d+))?', part)
        if m:
            a, b = int(m.group(1)), int(m.group(2) or m.group(1))
            out |= set(range(a, b + 1))
    return sorted(out)


def slug(mdir, name):
    return ('src-%s-%s' % (os.path.basename(os.path.abspath(mdir)), name))[:150]


def stage(mdir, name, page_spec=None):
    mdir = os.path.abspath(mdir)
    M = draft.load(mdir)
    T = item(M, name)
    # an item from another source (a cited external result) names its own PDF, and then the
    # mission's context pages and page offset do not apply to it
    own = bool(T.get('source_pdf'))
    pdf = os.path.join(mdir, T.get('source_pdf') or getattr(M, 'SOURCE_PDF', ''))
    if not os.path.isfile(pdf):
        sys.exit('set SOURCE_PDF in mission.py, or source_pdf on the item (path to the source PDF)')
    # the goal is a milestone for auditing purposes; an older mission's goal may carry no
    # milestone description, so an item may give its sentence directly as `source_quote`
    # the opening paragraph only: that is where the source's sentence is quoted; quotations in a
    # later *Route* or *External* paragraph explain how the source gets there and are not claims of
    # this statement (Monod M7 handed its auditor two Route quotes as "the sentence under audit")
    # (cut at the first *Route* / *External* paragraph, not at a blank line: a quoted sentence may
    # contain a displayed formula set off by blank lines, as Monod's Proposition 9 does)
    opening = re.split(r'\n\n\*(?:Route|External)\b', T.get('milestone_description') or '')[0]
    quote = re.findall(r'[“"](.+?)[”"]', opening, re.S)
    if not quote and T.get('source_quote'):
        quote = [T['source_quote']]
    if not quote and not T.get('bundle'):
        sys.exit('%s: no quoted sentence (milestone description or source_quote)' % name)
    d = os.path.join(ROOT, slug(mdir, name))
    if os.path.exists(d):
        sys.exit('REFUSING: %s exists -- collect/teardown it first' % d)
    os.makedirs(os.path.join(d, 'scratch'))
    shutil.copy(os.path.join(HERE, 'source-audit-bundle-brief.md' if T.get('bundle') else 'source-audit-brief.md'),
                os.path.join(d, 'brief.md'))
    # the item's own page, the mission's context pages, and the item's own context pages -- where
    # the notions its sentence uses are defined (Γ ∉ EG's auditor could not see EG's definition)
    want = (pages(page_spec or T['page']) + ([] if own else pages(getattr(M, 'CONTEXT_PAGES', '')))
            + pages(T.get('context_pages', '')))
    # pages are the source's own numbers (what `source` cites); a journal reprint's PDF starts
    # elsewhere, so mission.py sets PDF_PAGE_OFFSET = PDF page - printed page (CFP: -213)
    off = T.get('pdf_page_offset', 0) if own else getattr(M, 'PDF_PAGE_OFFSET', 0)
    # a bundle may draw on several papers: `source_parts` = [(pdf, pages, pdf_page_offset), ...],
    # each rendered as `<tag>-page-NNN` so the auditor can tell them apart (F-amenability, 2026-09-30)
    parts = T.get('source_parts')
    if parts:
        want = []
        for part_pdf, part_pages, part_off in parts:
            tag = os.path.splitext(os.path.basename(part_pdf))[0]
            for p in pages(part_pages):
                subprocess.run(['pdftoppm', '-f', str(p + part_off), '-l', str(p + part_off), '-r', '130',
                                '-png', os.path.join(mdir, part_pdf), os.path.join(d, '%s-page-%03d' % (tag, p))],
                               check=True)
                want.append('%s p. %d' % (tag, p))
    else:
        for p in sorted(set(want)):
            subprocess.run(['pdftoppm', '-f', str(p + off), '-l', str(p + off), '-r', '130', '-png',
                            pdf, os.path.join(d, 'page-%03d' % p)], check=True)
    with open(os.path.join(d, 'source.md'), 'w', encoding='utf-8') as f:
        if T.get('bundle'):
            where = ('; '.join('%s pp. %s' % (os.path.basename(pp), pg) for pp, pg, _ in parts) if parts
                     else '%s, pp. %s' % (os.path.basename(pdf), T['page']))
            f.write('# Definitions under audit\n\nSources: %s: where the sources set up the objects '
                    'the results are about.\n\n' % where)
        else:
            f.write('# Sentence under audit\n\nSource: %s, p. %s (%s)\n\n' % (
                os.path.basename(pdf), T['page'], T.get('result', '')))
            for q in quote:
                f.write('> %s\n\n' % ' '.join(q.split()))
        f.write('Page images of %s are in this directory.\n' % ', '.join(map(str, want if parts else sorted(set(want)))))
    print('Work only inside %s. Everything below is relative to it.\n\n'
          'Read brief.md and do PHASE 1 only: read source.md and the page images, write claims.md,\n'
          'then reply in at most five lines. There is no formalization in your directory yet, and\n'
          'you must not look for one. Do not read or write anything outside this directory.' % d)


def reveal(mdir, name):
    mdir = os.path.abspath(mdir)
    d = os.path.join(ROOT, slug(mdir, name))
    cp = os.path.join(d, 'claims.md')
    # phase 2 starts from a COMPLETE claims list, not an existing file: an agent creates the file
    # before it has finished writing it, so the brief makes `END OF CLAIMS` the last line written
    if not (os.path.exists(cp) and 'END OF CLAIMS' in open(cp, encoding='utf-8').read()):
        sys.exit('REFUSING: %s is %s -- phase 1 is not finished'
                 % (cp, 'incomplete' if os.path.exists(cp) else 'missing'))
    shutil.copy(os.path.join(mdir, 'readbacks', name + '.readback.md'), os.path.join(d, 'readback.md'))
    if name.startswith('Def_'):
        write_bundle_context(mdir, name, os.path.join(d, 'context.md'))
        print('Continue with PHASE 2 of brief.md: readback.md and context.md are now in your directory.\n'
              'Compare them with claims.md, write coverage.md exactly as Phase 2 specifies, and reply in at\n'
              'most five lines. Do not change claims.md.')
        return
    print('Continue with PHASE 2 of brief.md: readback.md is now in your directory. Compare it with\n'
          'claims.md, write coverage.md (with near-misses and the VERDICT line), and reply in at\n'
          'most five lines. Do not change claims.md.')


def write_bundle_context(mdir, name, dst):
    """context.md for phase 2 of a bundle audit: what else the formalization has.

    The first bundle audit (Monod, 2026-09-29) saw only the bundle's read-back and flagged 27 rows,
    most of them notions provided by another bundle, by Mathlib, or inline in a statement, or needed
    only by proofs or by results the mission leaves out. This gives phase 2 that context."""
    M = draft.load(mdir)
    # statement preambles from the payloads, not draft.desired(): that needs every read-back, and
    # the bundle is audited before (or while) the statements get theirs
    pre = [p for p, _ in (M.payloads().values() if hasattr(M, 'payloads') else [])]
    ws = draft.WS if hasattr(draft, 'WS') else os.path.expanduser('~/claude/prove2me_workspace')
    mods = set()
    for f in [os.path.join(mdir, 'lib', name + '.lean')]:
        if os.path.exists(f):
            mods |= set(re.findall(r'^import Definitions\.(Def_\w+)', open(f, encoding='utf-8').read(), re.M))
    for pr in pre:
        mods |= set(re.findall(r'^import Definitions\.(Def_\w+)', pr or '', re.M))
    mods.discard(name)
    out = ['# Context for the definitions audit\n',
           '## Other definition files the formalization imports\n']
    for m in sorted(mods):
        f = os.path.join(ws, 'Definitions', m + '.lean')
        names = re.findall(r'^(?:noncomputable )?(?:def|structure|abbrev|class|inductive) (\S+)',
                           open(f, encoding='utf-8').read(), re.M) if os.path.exists(f) else []
        out.append('- `%s`: %s' % (m, ', '.join('`%s`' % n for n in names) or '(file not found)'))
    out.append('\nMathlib\'s own notions (groups, subgroups, commutators and derived subgroups, free '
               'groups, orders, measures, …) count as available.\n')
    out.append('## The statements of the formalization\n')
    for T in M.THEOREMS:
        out.append('### %s\n\n%s\n' % (T.get('title') or T['name'], T.get('nls') or ''))
    desc = os.path.join(mdir, 'description.md')
    if os.path.exists(desc):
        m = re.search(r'^## (?:Formalization scope|What is left out)\s*\n(.*?)(?=^## |\Z)', open(desc, encoding='utf-8').read(), re.M | re.S)
        if m:
            out.append('## What the formalization leaves out\n\n' + m.group(1).strip() + '\n')
    open(dst, 'w', encoding='utf-8').write('\n'.join(out))


def collect(mdir, name):
    mdir = os.path.abspath(mdir)
    d = os.path.join(ROOT, slug(mdir, name))
    rdir = os.path.join(mdir, 'readbacks')
    ok = True
    for f, tgt in (('claims.md', name + '.claims.md'), ('coverage.md', name + '.coverage.md')):
        p = os.path.join(d, f)
        if not os.path.exists(p):
            print('MISSING', f); ok = False; continue
        shutil.copy(p, os.path.join(rdir, tgt))
    cov = os.path.join(rdir, name + '.coverage.md')
    verdict = re.search(r'VERDICT:\s*(.+)', open(cov, encoding='utf-8').read()) if os.path.exists(cov) else None
    print('VERDICT', verdict.group(1).strip() if verdict else '(none)')
    # advisory: a faithful statement can still hide the source's object (CFP §7's 𝒯′ was a
    # bijection with binary words; the graph was never named). Printed, never a failure.
    direct = re.search(r'DIRECTNESS:\s*(.+)', open(cov, encoding='utf-8').read()) if os.path.exists(cov) else None
    if direct and not direct.group(1).strip().lower().startswith('direct'):
        print('DIRECTNESS', direct.group(1).strip(), '  <- consider restating to name the source object')
    if ok:
        teardown(slug(mdir, name), force=True)
    return ok and verdict and verdict.group(1).strip().lower().startswith(('faithful', 'literal'))


if __name__ == '__main__':
    a = sys.argv[1:]
    if len(a) == 2 and a[0] == 'decisions':
        import decisions
        decisions.build(os.path.abspath(a[1]))
        sys.exit(0)
    if len(a) < 3 or a[0] not in ('stage', 'reveal', 'collect'):
        sys.exit(__doc__)
    if a[0] == 'stage':
        stage(a[1], a[2], a[a.index('--pages') + 1] if '--pages' in a else None)
    elif a[0] == 'reveal':
        reveal(a[1], a[2])
    else:
        sys.exit(0 if collect(a[1], a[2]) else 1)
