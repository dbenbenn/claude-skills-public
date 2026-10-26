#!/usr/bin/env python3
"""Session start: sync the platform's rulebook and workspace to upstream head, then check that the
live platform still behaves as our scripts assume.

usage: sync_workspace.py [--no-live]

1. git fetch the prove2me workspace and list the incoming commits (each platform release is one).
2. Save the incoming diff of references/ and SKILL.md to sync_diff.txt in the job's tmp dir (or
   /tmp), to be READ before any rule is relied on.
3. Fast-forward (never merge or reset).
4. Run the live read-only contract tests (tests/test_live_contract.py, P2M_LIVE=1). Those tests pin
   the API assumptions that once broke scripts: paging, the solution endpoint, sketch-node shape,
   deprecated_at. They run here so they never depend on remembering (dbenbenn, 2026-10-02: "of
   course then it's up to you to remember to rerun them sometimes").
5. Run workspace_audit.py --quiet (also with --no-live): one line on which untracked workspace files
   have no copy on GitHub. Informational; it never changes the exit status.
6. Count the untriaged lessons the headless workers filed in the lessons inbox ($P2M_LESSONS_INBOX,
   default ~/claude/p2m-standalone/openai-ports/lessons-inbox, one .md per lesson besides README.md).
   The main agent triages them into SKILL.md (merged into the existing rule, a tool fix, or dropped)
   and deletes each file. Informational.

Exit status 1 if the fast-forward fails or a contract test fails.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from p2m import _workspace  # noqa: E402


def git(ws, *args):
    return subprocess.run(['git', '-C', ws] + list(args), capture_output=True, text=True)


INBOX = os.path.expanduser(os.environ.get('P2M_LESSONS_INBOX',
                                           '~/claude/p2m-standalone/openai-ports/lessons-inbox'))


def inbox_line(inbox=INBOX):
    """One line naming the untriaged lessons in the inbox, or None when there are none."""
    try:
        names = [f for f in os.listdir(inbox) if f.endswith('.md') and f != 'README.md']
    except FileNotFoundError:
        return None
    if not names:
        return None
    return ('lessons inbox: %d untriaged in %s -- main agent: triage each into the skill '
            '(merge, tool fix, or drop), then delete it' % (len(names), inbox))


def main():
    ws = _workspace()
    if git(ws, 'fetch', '-q', 'origin').returncode:
        sys.exit('git fetch failed')
    incoming = git(ws, 'log', '--oneline', 'HEAD..origin/main').stdout.strip()
    if incoming:
        print('incoming platform commits:\n' + incoming)
        diff = git(ws, 'diff', 'HEAD..origin/main', '--', 'references', 'SKILL.md').stdout
        out = os.path.join(os.environ.get('CLAUDE_JOB_DIR', '/tmp'), 'tmp' if os.environ.get('CLAUDE_JOB_DIR') else '',
                           'sync_diff.txt')
        os.makedirs(os.path.dirname(out), exist_ok=True)
        open(out, 'w', encoding='utf-8').write(diff)
        print('rulebook diff (%d lines) saved to %s -- read it before relying on any rule' % (diff.count('\n'), out))
        r = git(ws, 'merge', '--ff-only', 'origin/main')
        if r.returncode:
            sys.exit('fast-forward failed: ' + r.stderr.strip())
        print('fast-forwarded to', git(ws, 'log', '--oneline', '-1').stdout.strip())
    else:
        print('workspace at head:', git(ws, 'log', '--oneline', '-1').stdout.strip())
    audit = subprocess.run([sys.executable, os.path.join(HERE, 'workspace_audit.py'), '--quiet'],
                           capture_output=True, text=True)
    print((audit.stdout or audit.stderr[-1500:]).rstrip())
    line = inbox_line()
    if line:
        print(line)
    if '--no-live' in sys.argv:
        return
    tests = os.path.join(os.path.dirname(HERE), 'tests', 'test_live_contract.py')
    r = subprocess.run([sys.executable, '-m', 'pytest', '-q', '-p', 'no:cacheprovider', tests],
                       env=dict(os.environ, P2M_LIVE='1'), capture_output=True, text=True)
    last = (r.stdout.strip().split('\n') or [''])[-1]
    print('live contract tests:', last)
    if r.returncode:
        print(r.stdout[-3000:])
        sys.exit('!! the platform no longer behaves as the scripts assume -- fix p2mlib/scripts before relying on them')


if __name__ == '__main__':
    main()
