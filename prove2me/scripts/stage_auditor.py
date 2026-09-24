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
  * every staged Lean file is stripped of comments (see strip()). One leak remains by design:
    ./probe elaborates against the workspace's compiled modules, which keep their docstrings, so
    an auditor that goes looking (meta code calling findDocString?) could read them. Probes are
    for #check/#reduce/rfl, and the brief does not invite that;
  * teardown is the captain's job, not the auditor's. Auditors are demonstrably unreliable
    about cleanup: thirteen probe files were once left in the shared workspace by auditors
    that reported having tidied up.

Usage:
  stage_auditor.py stage <slug> <artifact.lean> [imported-def.lean ...] [--force]
                                                                    -> prints the prompt
                                                                       (refuses an existing slug
                                                                        without --force)
  stage_auditor.py collect <slug> <dest-dir>                        -> moves testimony out
  stage_auditor.py stage-all MISSION_DIR [NAME ...] [--force]         -> one auditor per item of
                                                                       mission.py (draft.py's), each
                                                                       prompt saved to _prompts/
  stage_auditor.py collect-all MISSION_DIR [NAME ...] [--teardown]    -> every staged item into
                                                                       MISSION_DIR/readbacks/; exit 1
                                                                       on any MISSING or FAIL
  stage_auditor.py teardown <slug> [--force]                        -> removes the staging dir
                                                                       (refuses while readback.md or
                                                                        audit.md is missing)
"""
import os, shutil, sys, subprocess
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

def fresh_oleans(files):
    """Build the project library modules this auditor will read, before sealing anything.

    The auditor reads the .lean text we stage, but `./probe` elaborates against the workspace's
    *compiled* libraries. Those two can disagree: edit a definition, stage the new text, and the
    probe still sees the old .olean. Nothing in the staged directory reveals it, so the auditor
    reasons about one artifact and tests another, and its testimony can be confidently wrong.
    That happened on the Garrido re-audit; an auditor noticed the mismatch itself, which is luck
    rather than a check.

    `lake build` is the authority on what is out of date -- it tracks content, not timestamps,
    so this is a no-op when everything is current and a rebuild exactly when one is needed. An
    earlier version of this gate compared mtimes instead and refused to stage after `touch`ing a
    file whose content had not changed, because lake correctly declined to rebuild it.
    """
    mods = set()
    for f in files:
        rel = os.path.relpath(os.path.abspath(f), WS)
        if not rel.startswith('..') and rel.endswith('.lean'):
            mods.add(rel[:-5].replace(os.sep, '.'))
        try:
            text = open(f, encoding='utf-8').read()
        except OSError:
            continue
        for m in re.findall(r'^import\s+((?:Definitions|Theorems)\.\S+)', text, re.M):
            if os.path.exists(os.path.join(WS, m.replace('.', os.sep) + '.lean')):
                mods.add(m)
    if not mods:
        return
    r = subprocess.run(['lake', 'build'] + sorted(mods), cwd=WS,
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write((r.stdout + r.stderr)[-1200:] + '\n')
        raise SystemExit('REFUSING TO STAGE: %s does not build' % ', '.join(sorted(mods)))
    built = [l for l in (r.stdout + r.stderr).split('\n') if 'Built' in l]
    print('library checked (%d module%s)%s'
          % (len(mods), '' if len(mods) == 1 else 's',
             '; rebuilt %d' % len(built) if built else '; already current'))


def stage(slug, statement, extras, force=False):
    d = os.path.join(ROOT, slug)
    # Re-staging over a live directory is the teardown hazard by another door: an auditor still
    # working there loses its files mid-flight. Tear down first (which has the guard), or --force.
    if os.path.exists(d) and not force:
        sys.exit(f"REFUSING to stage {slug}: {d} exists -- tear it down first, or pass --force")
    bases = [os.path.basename(f) for f in [statement] + list(extras)]
    if len(set(bases)) != len(bases):
        sys.exit(f"REFUSING to stage {slug}: two staged files share a basename: {bases}")
    fresh_oleans([statement] + list(extras))
    if os.path.exists(d): teardown(slug, force=True)
    os.makedirs(os.path.join(d, 'scratch'))
    shutil.copy(BRIEF, os.path.join(d, 'readback-brief.md'))
    names = []
    for f in [statement] + list(extras):
        b = os.path.basename(f)
        # stripped, not copied: until 2026-09-24 this was a plain copy and strip() sat unused,
        # so every bundle auditor read the docstrings it was meant to reconstruct blind
        write_stripped(os.path.join(d, b), f)
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
artifact does not use. Write the same five lines to reply.md before you reply.""")

def collect(slug, dest):
    """Pull both artifacts out, and check the publishable one against the platform's spec.

    readback.md goes in the `readback` field of a draft item; audit.md never does. The checks
    below are the ones a moderator would apply to it: mission_auditor.md asks for plain
    mathematical English in Markdown+KaTeX with no judgment, so Lean identifiers and a verdict
    on the naming are signs the two artifacts have been merged again."""
    import re
    d = os.path.join(ROOT, slug)
    os.makedirs(dest, exist_ok=True)
    out, failed = {}, False
    # the five-line reply used to live only in the captain's session transcript; keep it beside
    # the testimony (optional: auditors staged before 2026-09-24 did not write it)
    rp = os.path.join(d, 'reply.md')
    if os.path.exists(rp):
        shutil.copy(rp, os.path.join(dest, slug + '.reply.md'))
        print(f"COLLECTED {os.path.join(dest, slug + '.reply.md')}")
    for name, tgt in (('readback.md', slug + '.readback.md'), ('audit.md', slug + '.audit.md')):
        src = os.path.join(d, name)
        if not os.path.exists(src):
            print(f"MISSING {name}"); failed = True; continue
        shutil.copy(src, os.path.join(dest, tgt)); out[name] = os.path.join(dest, tgt)
        print(f"COLLECTED {os.path.join(dest, tgt)}")
    au = out.get('audit.md')
    if au:
        # An unused `import Definitions.*` is a dependency the statement would carry forever
        # once its preamble freezes; the auditor reports it, so print it where it gets read.
        # The flag exists to surface an import the artifact does not use. Auditors answer the
        # question either way, so most matching lines are denials -- "No imported definition
        # file goes entirely unused", "a used file, not an unused import" -- and printing those
        # buries the real ones. Drop a line whose unusedness is itself negated.
        # NB: inline (?i) is only legal at the start of a pattern in modern Python, so the
        # flag goes in the compile call.
        # `no` followed by a comma is an answer ("No, the import ... is not used"), not a denial
        denial = re.compile(r'\b(?:no(?!,)|none)\b.{0,120}?(?:unused|not use)'
                            r'|not an unused'
                            r'|\bis\b\W{0,2}used\b', re.I)
        for l in open(au).read().splitlines():
            # a bullet may name the file ("Def_Bar is not used") without the word "import"
            if not (re.search(r'(?i)import|\bDef_\w+|definition file|\.lean\b', l)
                    and re.search(r'(?i)unused|not used|uses nothing|nothing from|never used'
                                  r'|does not use', l)):
                continue
            if denial.search(l):
                continue
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
            failed = failed or not ok
    n = sum(len(fs) for _, _, fs in os.walk(os.path.join(d, 'scratch')))
    print(f"\nprobe files left in scratch/: {n} (discarded at teardown)")
    return failed

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
            sys.exit(f"REFUSING to tear down {slug}: missing {', '.join(missing)} "
                     f"-- the auditor may still be writing. Pass --force to override.")
    if not os.path.isdir(d):
        sys.exit(f"NO SUCH staging directory: {d}")
    for e in os.listdir(d) if os.path.isdir(d) else []:   # never follow into shared libraries
        q = os.path.join(d, e)
        if os.path.islink(q): os.unlink(q)
    shutil.rmtree(d, ignore_errors=True)
    print(f"TORN DOWN {d}")

def mission_items(mdir):
    """[(key, artifact path, [imported bundle paths])] for every item of MISSION_DIR/mission.py:
    each definition bundle as its lib/ file, each theorem as its exact publish payload (preamble +
    formal_statement) written to a scratch file -- what the platform will freeze is what the
    auditor reads. Keys are the read-back names draft.py expects: Def_<name> or <name>."""
    import draft
    M = draft.load(os.path.abspath(mdir))
    src = os.path.join(ROOT, '_src', os.path.basename(os.path.abspath(mdir)))
    os.makedirs(src, exist_ok=True)
    def bundles(text):
        return [os.path.join(WS, m.replace('.', os.sep) + '.lean')
                for m in re.findall(r'^import (Definitions\.\S+)', text, re.M)]
    out = []
    for D in M.DEFINITIONS:
        path = os.path.join(os.path.abspath(mdir), 'lib', 'Def_%s.lean' % D['name'])
        out.append(('Def_' + D['name'], path, bundles(open(path, encoding='utf-8').read())))
    pay = M.payloads()
    for T in M.THEOREMS:
        pre, fs = pay[T['name']]
        path = os.path.join(src, T['name'] + '.lean')
        open(path, 'w', encoding='utf-8').write(pre + '\n\n' + fs + '\n')
        out.append((T['name'], path, bundles(pre)))
    return out


def slug_of(mdir, key):
    return ('%s-%s' % (os.path.basename(os.path.abspath(mdir)), key))[:150]


def stage_all(mdir, names, force=False):
    """Stage one auditor per item (or per NAME given); each prompt goes to _prompts/<slug>.txt."""
    import io, contextlib
    pdir = os.path.join(ROOT, '_prompts'); os.makedirs(pdir, exist_ok=True)
    items = [i for i in mission_items(mdir) if not names or i[0] in names]
    if names and len(items) != len(set(names)):
        sys.exit('unknown item(s): %s' % sorted(set(names) - {i[0] for i in items}))
    for key, art, extras in items:
        slug = slug_of(mdir, key)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            stage(slug, art, extras, force=force)
        prompt = buf.getvalue().split('\n\n', 1)[-1] if buf.getvalue().startswith('library') else buf.getvalue()
        prompt = prompt[prompt.find('Work only inside'):]
        open(os.path.join(pdir, slug + '.txt'), 'w').write(prompt)
        print('staged %-60s %d bundle(s)   prompt: %s' % (key[:60], len(extras), os.path.join(pdir, slug + '.txt')))


def collect_all(mdir, names, teardown_after=False):
    """Collect every staged item into MISSION_DIR/readbacks/<key>.{readback,audit}.md; exit 1 if
    any item is missing a file or fails a check, printing every IMPORTS line."""
    import tempfile
    rdir = os.path.join(os.path.abspath(mdir), 'readbacks'); os.makedirs(rdir, exist_ok=True)
    bad = []
    for key, _, _ in mission_items(mdir):
        if names and key not in names:
            continue
        slug = slug_of(mdir, key)
        if not os.path.isdir(os.path.join(ROOT, slug)):
            if names:
                bad.append(key); print('NOT STAGED', key)
            continue
        tmp = tempfile.mkdtemp()
        print('== %s' % key)
        failed = collect(slug, tmp)
        # a failing pair never replaces the read-back in readbacks/ (it may be an auditor that has
        # not finished, or testimony that breaks the spec); it goes to readbacks/_failed/ to inspect
        dest = os.path.join(rdir, '_failed') if failed else rdir
        os.makedirs(dest, exist_ok=True)
        for kind in ('readback', 'audit', 'reply'):
            f = os.path.join(tmp, '%s.%s.md' % (slug, kind))
            if os.path.exists(f):
                shutil.move(f, os.path.join(dest, '%s.%s.md' % (key, kind)))
        shutil.rmtree(tmp, ignore_errors=True)
        if failed:
            bad.append(key)
        elif teardown_after:
            teardown(slug)
    print('\ncollected into %s; %s' % (rdir, 'FAILED: ' + ', '.join(bad) if bad else 'all clean'))
    return not bad


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if a not in ('--force', '--teardown')]
    force = '--force' in sys.argv[1:]
    if args and args[0] in ('stage-all', 'collect-all'):
        if len(args) < 2:
            sys.exit(__doc__)
        if args[0] == 'stage-all':
            stage_all(args[1], args[2:], force=force)
        else:
            sys.exit(0 if collect_all(args[1], [a for a in args[2:] if a != '--teardown'],
                                      teardown_after='--teardown' in sys.argv) else 1)
        sys.exit(0)
    need = {'stage': 3, 'collect': 3, 'teardown': 2}
    if not args or args[0] not in need or len(args) < need[args[0]]:
        sys.exit(__doc__)
    cmd = args[0]
    if cmd == 'stage': stage(args[1], args[2], args[3:], force=force)
    elif cmd == 'collect': sys.exit(1 if collect(args[1], args[2]) else 0)
    else: teardown(args[1], force=force)
