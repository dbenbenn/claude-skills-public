#!/usr/bin/env python3
"""Source-side audit: what does the source sentence claim, and does the formalization say it?

usage: source_audit.py stage   MISSION_DIR NAME [--pages 12-14]   -> phase 1 prompt
       source_audit.py reveal  MISSION_DIR NAME [--finished]      -> phase 2 message
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
and CONTEXT_PAGES ('12-13'); --pages overrides the item's own page field.
"""
import os, re, shutil, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from stage_auditor import ROOT, teardown  # same staging root as the read-back auditors
import draft


def item(M, name):
    for T in M.THEOREMS:
        if T['name'] == name:
            return T
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
    pdf = os.path.join(mdir, getattr(M, 'SOURCE_PDF', ''))
    if not os.path.isfile(pdf):
        sys.exit('set SOURCE_PDF in mission.py (path to the source PDF)')
    quote = re.findall(r'[“"](.+?)[”"]', T.get('milestone_description') or '', re.S)
    if not quote:
        sys.exit('%s: no quoted sentence in its milestone description' % name)
    d = os.path.join(ROOT, slug(mdir, name))
    if os.path.exists(d):
        sys.exit('REFUSING: %s exists -- collect/teardown it first' % d)
    os.makedirs(os.path.join(d, 'scratch'))
    shutil.copy(os.path.join(HERE, 'source-audit-brief.md'), os.path.join(d, 'brief.md'))
    want = pages(page_spec or T['page']) + pages(getattr(M, 'CONTEXT_PAGES', ''))
    for p in sorted(set(want)):
        subprocess.run(['pdftoppm', '-f', str(p), '-l', str(p), '-r', '130', '-png', pdf,
                        os.path.join(d, 'page-%02d' % p)], check=True)
    with open(os.path.join(d, 'source.md'), 'w', encoding='utf-8') as f:
        f.write('# Sentence under audit\n\nSource: %s, p. %s (%s)\n\n' % (
            os.path.basename(pdf), T['page'], T.get('result', '')))
        for q in quote:
            f.write('> %s\n\n' % ' '.join(q.split()))
        f.write('Page images of pp. %s are in this directory.\n' % ', '.join(map(str, sorted(set(want)))))
    print('Work only inside %s. Everything below is relative to it.\n\n'
          'Read brief.md and do PHASE 1 only: read source.md and the page images, write claims.md,\n'
          'then reply in at most five lines. There is no formalization in your directory yet, and\n'
          'you must not look for one. Do not read or write anything outside this directory.' % d)


def reveal(mdir, name, finished=False):
    mdir = os.path.abspath(mdir)
    d = os.path.join(ROOT, slug(mdir, name))
    cp = os.path.join(d, 'claims.md')
    # phase 2 starts from a COMPLETE claims list, not an existing file: an agent creates the file
    # before it has finished writing it. The brief makes `END OF CLAIMS` the last thing written;
    # --finished is for an agent staged before that rule, and only after its completion notice.
    done = os.path.exists(cp) and 'END OF CLAIMS' in open(cp, encoding='utf-8').read()
    if not done and not finished:
        sys.exit('REFUSING: %s is %s -- phase 1 is not finished (pass --finished only after the '
                 "agent's completion notification)" % (cp, 'incomplete' if os.path.exists(cp) else 'missing'))
    if not os.path.exists(cp):
        sys.exit('REFUSING: no claims.md in %s' % d)
    shutil.copy(os.path.join(mdir, 'readbacks', name + '.readback.md'), os.path.join(d, 'readback.md'))
    print('Continue with PHASE 2 of brief.md: readback.md is now in your directory. Compare it with\n'
          'claims.md, write coverage.md (with near-misses and the VERDICT line), and reply in at\n'
          'most five lines. Do not change claims.md.')


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
    if ok:
        teardown(slug(mdir, name), force=True)
    return ok and verdict and verdict.group(1).strip().lower().startswith('faithful')


if __name__ == '__main__':
    a = sys.argv[1:]
    if len(a) < 3 or a[0] not in ('stage', 'reveal', 'collect'):
        sys.exit(__doc__)
    if a[0] == 'stage':
        stage(a[1], a[2], a[a.index('--pages') + 1] if '--pages' in a else None)
    elif a[0] == 'reveal':
        reveal(a[1], a[2], finished='--finished' in a)
    else:
        sys.exit(0 if collect(a[1], a[2]) else 1)
