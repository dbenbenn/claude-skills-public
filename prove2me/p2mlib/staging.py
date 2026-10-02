"""Auditor staging directories and source page images -- one copy, with the guards.

`stage_auditor.stage` refused to restage over a live directory after four auditors lost their
work mid-run; `caveat_audit.stage` deleted it instead (tests/test_caveat_audit.py). Both stage
through `fresh_dir` now. `render_pages` was copied between source_audit and caveat_audit."""
import os
import shutil
import subprocess
import sys


def fresh_dir(root, slug, force=False, done_marker=None):
    """Create root/slug for a new auditor. An existing directory is refused unless `force`; with
    `force` it is removed, never following symlinks into shared libraries."""
    d = os.path.join(root, slug)
    if os.path.exists(d):
        if not force:
            sys.exit('REFUSING to stage %s: %s exists -- collect and tear it down first, or pass --force' % (slug, d))
        remove(d)
    os.makedirs(os.path.join(d, 'scratch'))
    return d


def remove(d):
    """Remove a staging directory without ever following a symlink out of it."""
    for e in os.listdir(d) if os.path.isdir(d) else []:
        q = os.path.join(d, e)
        if os.path.islink(q):
            os.unlink(q)
    shutil.rmtree(d, ignore_errors=True)


def render_pages(pdf, pages, offset, dest, tag=''):
    """Render source pages (the source's own numbers; PDF page = page + offset) to PNG in `dest`,
    named `[<tag>-]page-NNN`."""
    out = []
    for p in pages:
        stem = os.path.join(dest, ('%s-page-%03d' % (tag, p)) if tag else 'page-%03d' % p)
        subprocess.run(['pdftoppm', '-f', str(p + offset), '-l', str(p + offset), '-r', '130', '-png', pdf, stem],
                       check=True)
        out.append(stem)
    return out
