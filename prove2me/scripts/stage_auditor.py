#!/usr/bin/env python3
"""Stage a sealed working directory for one blind auditor, and tear it down after.

Why: a blind read-back is only blind if the auditor cannot casually reach the things it must
not see — the doctrine file, the mission repo, a sibling auditor's scratch. Containers or a
mount namespace would enforce that, but neither is available here (no docker group, uid_map
writes refused), and a Claude Code subagent's own file tools would run outside a container
anyway. So this enforces what it can, structurally rather than by instruction:

  * the auditor is pointed at ONE staged directory containing only the brief, its task files
    and an empty scratch/ -- it never visits the mission repo or the captain's private notes, so the
    brief's captain-only rationale is unreachable in practice rather than merely forbidden;
  * every path in the prompt is relative to that directory, which is also what stops absolute
    paths leaking into the published citations;
  * scratch/ is per-auditor, so concurrent auditors cannot collide;
  * teardown is the captain's job, not the auditor's. Auditors are demonstrably unreliable
    about cleanup: thirteen probe files were once left in the shared workspace by auditors
    that reported having tidied up.

Usage:
  stage_auditor.py stage <slug> <artifact.lean> [imported-def.lean ...] -> prints the prompt
  stage_auditor.py collect <slug> <dest-dir>                        -> moves testimony out
  stage_auditor.py teardown <slug> [--force]                        -> removes the staging dir
                                                                       (refuses while readback.md or
                                                                        audit.md is missing)
"""
import os, shutil, sys, subprocess
import re


def strip(text):
    """Lean source with every comment removed: block comments (nested), docstrings and line
    comments. Blind staging depends on this — a docstring handed to an auditor is the intended
    reading leaking into a reading that is supposed to be independent."""
    out, i, n = [], 0, len(text)
    while i < n:
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
            i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j == -1 else j
        else:
            out.append(text[i]); i += 1
    return re.sub(r'\n{3,}', '\n\n', ''.join(out)).strip() + '\n'


def write_stripped(dst, src):
    """Copy a Lean file into the staging directory with its comments removed."""
    open(dst, 'w', encoding='utf-8').write(strip(open(src, encoding='utf-8').read()))


HERE = os.path.dirname(os.path.abspath(__file__))
BRIEF = os.path.join(HERE, 'readback-brief.md')
ROOT = os.environ.get('AUDITOR_STAGE_ROOT') or os.path.join(
    os.environ.get('CLAUDE_JOB_DIR', '/tmp'), 'auditors')
def _workspace():
    """The prove2.me Lean workspace: $P2M_WORKSPACE, else the first of the known locations."""
    for p in [os.environ.get('P2M_WORKSPACE'), '~/claude/prove2me_workspace', '~/prove2me_workspace']:
        if p and os.path.isdir(os.path.expanduser(p)):
            return os.path.expanduser(p)
    raise SystemExit('prove2.me workspace not found; set P2M_WORKSPACE')
WS = _workspace()
LIBS = os.path.join(WS, '.lake', 'packages')

def _toolchain():
    try: tc = open(os.path.join(WS, 'lean-toolchain')).read().strip().replace('/', '--').replace(':', '---')
    except OSError: return ''
    p = os.path.expanduser('~/.elan/toolchains/' + tc)
    return p if os.path.isdir(p) else ''
TOOLCHAIN = _toolchain()

def _rev():
    import json
    try:
        m = json.load(open(os.path.join(WS, 'lake-manifest.json')))
        for pk in m.get('packages', []):
            if pk.get('name', '').lower() == 'mathlib': return 'mathlib ' + pk.get('rev', '?')
    except Exception: pass
    return 'unknown'
REV = _rev()

def stage(slug, statement, extras):
    d = os.path.join(ROOT, slug)
    if os.path.exists(d): shutil.rmtree(d)
    os.makedirs(os.path.join(d, 'scratch'))
    shutil.copy(BRIEF, os.path.join(d, 'readback-brief.md'))
    names = []
    for f in [statement] + list(extras):
        b = os.path.basename(f)
        shutil.copy(f, os.path.join(d, b))
        names.append(b)
    # Expose each library at its CANONICAL root, so the auditor's natural relative path is
    # already the citation form everyone else can resolve (`Mathlib/Algebra/...:76`). The layout
    # does the work that an instruction in the brief used to ask for, which is why the brief no
    # longer has to forbid absolute paths or explain how to strip a prefix.
    roots = 0
    for pkg in sorted(os.listdir(LIBS)):
        pdir = os.path.join(LIBS, pkg)
        if not os.path.isdir(pdir): continue
        for sub in sorted(os.listdir(pdir)):
            # a Lean library root is a capitalised directory matching the package name
            if (os.path.isdir(os.path.join(pdir, sub)) and sub[:1].isupper()
                    and sub.lower() == pkg.lower()):
                os.symlink(os.path.join(pdir, sub), os.path.join(d, sub)); roots += 1
    core = os.path.join(TOOLCHAIN, 'src', 'lean', 'Init')
    if os.path.isdir(core):
        os.symlink(core, os.path.join(d, 'Init')); roots += 1
    # the revision, so "say which revision you read" is answerable from inside the seal
    with open(os.path.join(d, 'REVISION'), 'w') as f:
        f.write(REV + '\n')
    # A wrapper so the auditor can ELABORATE probes without knowing where the lake project is.
    # Sealing it off otherwise costs the rfl/#synth probes, which are where the best testimony
    # comes from -- an auditor that can only grep takes an instance declaration on trust.
    probe = os.path.join(d, 'probe')
    with open(probe, 'w') as f:
        f.write('#!/bin/sh\n'
                '# usage: ./probe scratch/p.lean   -- elaborates the file, prints Lean output\n'
                'set -e\n'
                'test -n "$1" || { echo "usage: ./probe <file.lean>" >&2; exit 2; }\n'
                'exec sh -c \'cd "%s" && exec lake env lean "$1"\' _ "$(cd "$(dirname "$0")" '
                '&& pwd)/$1"\n' % WS)
    os.chmod(probe, 0o755)
    print(f"STAGED {d}  ({roots} library roots, {REV})\n")
    # Name the artifact and its imports separately. Listed together as "task files", an
    # auditor given a definition bundle plus the bundle it imports rendered both -- seven
    # definitions in a read-back that gets published beside six (Chou mission, 2026-09-18).
    imports = ('' if len(names) == 1 else
               '\nImported definitions, already published, given so you can expand what the artifact uses: '
               + ', '.join(names[1:]) + '. Do not render their declarations on their own; expand them '
               'inline where the artifact uses them.')
    print(f"""Work only inside {d}. Everything below is relative to it.

Read readback-brief.md and follow it exactly. Library source is here at its normal root, so
Mathlib/... and Init/... resolve directly; REVISION names the revision you are reading.
To elaborate a probe, write it to scratch/ and run  ./probe scratch/yourfile.lean
Leave probe files where they are -- you do not need to clean up.

Artifact: {names[0]} -- render every declaration in this file.{imports}

Write two files in this directory: readback.md (the publishable testimony) and audit.md
(your working notes). The brief says what belongs in each; do not merge them.

Do not read or write anything outside this directory. Reply with at most five lines:
conventions you settled and whether source settled them; anything unsettled; whether the
declaration's name is an accurate label; which imported definition files, if any, the
artifact does not use.""")

def collect(slug, dest):
    """Pull both artifacts out, and check the publishable one against the platform's spec.

    readback.md goes in the `readback` field of a draft item; audit.md never does. The checks
    below are the ones a moderator would apply to it: mission_auditor.md asks for plain
    mathematical English in Markdown+KaTeX with no judgment, so Lean identifiers and a verdict
    on the naming are signs the two artifacts have been merged again."""
    import re
    d = os.path.join(ROOT, slug)
    os.makedirs(dest, exist_ok=True)
    out = {}
    for name, tgt in (('readback.md', slug + '.readback.md'), ('audit.md', slug + '.audit.md')):
        src = os.path.join(d, name)
        if not os.path.exists(src):
            print(f"MISSING {name}"); continue
        shutil.copy(src, os.path.join(dest, tgt)); out[name] = os.path.join(dest, tgt)
        print(f"COLLECTED {os.path.join(dest, tgt)}")
    au = out.get('audit.md')
    if au:
        # An unused `import Definitions.*` is a dependency the statement would carry forever
        # once its preamble freezes; the auditor reports it, so print it where it gets read.
        for l in open(au).read().splitlines():
            if re.search(r'(?i)import', l) and re.search(r'(?i)unused|not used|uses nothing|nothing from|never used|does not use', l):
                print('IMPORTS ' + l.strip()[:160])
    rb = out.get('readback.md')
    if rb:
        t = open(rb).read()
        # Naming the declaration in a heading is legitimate -- the testimony has to say what
        # it is about. Scan the body only, or the check cries wolf and stops being read.
        t = '\n'.join(l for l in t.splitlines() if not l.lstrip().startswith('#'))
        checks = [
            ("Lean identifiers (want 0; use $math$)", len(re.findall(r'`[^`]+`', t))),
            ("absolute paths (want 0)", len(re.findall(r'/home/[a-z]+/', t))),
            ("naming verdicts (want 0; belongs in audit.md)",
             len(re.findall(r'(?i)name (?:check|is accurate|is an accurate)|accurate label', t))),
            ("file:line citations (want 0; belongs in audit.md)",
             len(re.findall(r'\.lean:\d+', t))),
            ("KaTeX math spans (want > 0)", len(re.findall(r'\$[^$]+\$', t))),
        ]
        print("\nreadback.md against mission_auditor.md:")
        for label, n in checks:
            want_zero = "want 0" in label
            ok = (n == 0) if want_zero else (n > 0)
            print(f"  {'ok ' if ok else 'FAIL'} {label}: {n}")
    n = sum(len(fs) for _, _, fs in os.walk(os.path.join(d, 'scratch')))
    print(f"\nprobe files left in scratch/: {n} (discarded at teardown)")

def teardown(slug, force=False):
    """Remove a staging directory -- but refuse while the auditor may still be writing.

    An auditor writes readback.md first and audit.md second, so a directory holding the
    first but not the second belongs to an agent that has not finished. Tearing it down
    then destroys its task files, library symlinks and probes mid-flight: the agent
    notices the deletion and rewrites its deliverables from memory, unable to re-run a
    single probe. Worse, a `collect` racing the same window copies a draft readback and
    silently misses audit.md, and that draft is what gets published.

    This happened: four auditors were torn down while finalising, two published read-backs
    were pre-final, and two sets of working notes were lost outright. Waiting on the
    filesystem is the wrong signal -- wait for the agent's completion notification -- but
    the guard belongs here too, because attention is not a mechanism."""
    d = os.path.join(ROOT, slug)
    if not force and os.path.isdir(d):
        missing = [f for f in ('readback.md', 'audit.md') if not os.path.exists(os.path.join(d, f))]
        if missing:
            print(f"REFUSING to tear down {slug}: missing {', '.join(missing)} "
                  f"-- the auditor may still be writing. Pass --force to override.")
            return
    for e in os.listdir(d) if os.path.isdir(d) else []:   # never follow into shared libraries
        q = os.path.join(d, e)
        if os.path.islink(q): os.unlink(q)
    shutil.rmtree(d, ignore_errors=True)
    print(f"TORN DOWN {d}")

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'stage': stage(sys.argv[2], sys.argv[3], sys.argv[4:])
    elif cmd == 'collect': collect(sys.argv[2], sys.argv[3])
    elif cmd == 'teardown': teardown(sys.argv[2], force='--force' in sys.argv[3:])
    else: sys.exit(__doc__)
