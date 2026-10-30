"""push_records.py: headless workers push their records from the ONE shared p2m-standalone checkout
without touching its index, HEAD, stash or anyone else's files (lessons oaiq-112, oaiq-113,
oaiq-123: a `pull --rebase --autostash` there was interrupted and left the checkout mid-rebase for
11 hours, 2026-10-29). Every test runs on a tmp bare origin and local clones; no network."""
import os
import subprocess
import sys
import tempfile

import pytest

from conftest import SCRIPTS

import push_records

SCRIPT = os.path.join(SCRIPTS, 'push_records.py')


def git(cwd, *args, check=True):
    r = subprocess.run(['git', '-C', str(cwd)] + list(args), capture_output=True, text=True)
    if check and r.returncode:
        raise AssertionError('git %s: %s' % (' '.join(args), r.stderr))
    return r.stdout.strip()


def write(root, rel, text):
    p = os.path.join(str(root), rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, 'w') as f:
        f.write(text)


def read(root, rel):
    with open(os.path.join(str(root), rel)) as f:
        return f.read()


def clone(origin, dest, who):
    subprocess.run(['git', 'clone', '-q', str(origin), str(dest)], check=True, capture_output=True)
    git(dest, 'config', 'user.name', who)
    git(dest, 'config', 'user.email', '%s@example.com' % who)
    return dest


@pytest.fixture
def world(tmp_path, monkeypatch):
    """origin (bare), `shared` (the shared checkout) and `other` (someone pushing from elsewhere)."""
    monkeypatch.setenv('GIT_CONFIG_GLOBAL', os.devnull)
    monkeypatch.setenv('GIT_CONFIG_NOSYSTEM', '1')
    tmpdir = tmp_path / 'tmpdir'
    tmpdir.mkdir()
    monkeypatch.setenv('TMPDIR', str(tmpdir))
    monkeypatch.setattr(tempfile, 'tempdir', None)        # in-process runs use it too
    origin = tmp_path / 'origin.git'
    subprocess.run(['git', 'init', '-q', '--bare', '-b', 'main', str(origin)], check=True)
    seed = tmp_path / 'seed'
    subprocess.run(['git', 'init', '-q', '-b', 'main', str(seed)], check=True)
    git(seed, 'config', 'user.name', 'seed')
    git(seed, 'config', 'user.email', 'seed@example.com')
    write(seed, 'README.md', 'records\n')
    write(seed, '.gitignore', '*.olean\n')
    write(seed, 'openai-ports/oaiq-001/RESUME.md', 'start\n')
    write(seed, 'openai-ports/oaiq-001/old.md', 'old\n')
    write(seed, 'openai-ports/oaiq-002/RESUME.md', 'two\n')
    write(seed, 'openai-ports/wave/RESUME.md', 'wave\n')
    write(seed, 'other/x.md', 'x\n')
    git(seed, 'add', '.')
    git(seed, 'commit', '-qm', 'seed')
    git(seed, 'remote', 'add', 'origin', str(origin))
    git(seed, 'push', '-q', 'origin', 'main')
    shared = clone(origin, tmp_path / 'shared', 'worker')
    other = clone(origin, tmp_path / 'other', 'elsewhere')
    return {'origin': origin, 'shared': shared, 'other': other, 'tmpdir': tmpdir, 'tmp': tmp_path}


def run(world, *args):
    r = subprocess.run([sys.executable, SCRIPT, '--repo', str(world['shared'])] + list(args),
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def origin_files(world):
    return set(git(world['origin'], 'ls-tree', '-r', '--name-only', 'main').splitlines())


def origin_show(world, rel):
    return git(world['origin'], 'show', 'main:%s' % rel)


def snapshot(shared):
    """Everything a run must leave alone in the shared checkout besides `main` and the index."""
    return {'stash': git(shared, 'stash', 'list'),
            'worktrees': git(shared, 'worktree', 'list', '--porcelain').count('worktree '),
            'other_x': read(shared, 'other/x.md')}


def assert_no_leftovers(world):
    assert os.listdir(str(world['tmpdir'])) == [], 'a temp file or index was left behind'
    assert git(world['shared'], 'worktree', 'list', '--porcelain').count('worktree ') == 1


# ---- the normal case ---------------------------------------------------------------------------

def test_pushes_exactly_the_paths_and_leaves_everyone_else_alone(world):
    sh = world['shared']
    # another worker's state in the same checkout: an untracked file, a staged file, an edit
    write(sh, 'openai-ports/oaiq-002/notes.md', 'their notes\n')
    write(sh, 'openai-ports/oaiq-002/staged.md', 'their staged file\n')
    git(sh, 'add', 'openai-ports/oaiq-002/staged.md')
    write(sh, 'other/x.md', 'their uncommitted edit\n')
    # our records
    write(sh, 'openai-ports/oaiq-001/RESUME.md', 'progress\n')
    write(sh, 'openai-ports/oaiq-001/new.md', 'new\n')
    write(sh, 'openai-ports/oaiq-001/build.olean', 'ignored binary\n')
    before = snapshot(sh)
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'oaiq-001: records',
                  '-m', 'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>')
    assert rc == 0, out
    files = origin_files(world)
    assert 'openai-ports/oaiq-001/new.md' in files
    assert 'openai-ports/oaiq-001/build.olean' not in files           # ignored stays out
    assert 'openai-ports/oaiq-002/notes.md' not in files               # not ours
    assert 'openai-ports/oaiq-002/staged.md' not in files              # staged by someone else
    assert origin_show(world, 'openai-ports/oaiq-001/RESUME.md') == 'progress'
    assert origin_show(world, 'other/x.md') == 'x'
    msg = git(world['origin'], 'log', '-1', '--format=%an|%ae|%B', 'main')
    assert msg.startswith('worker|worker@example.com|oaiq-001: records')
    assert msg.endswith('Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>')
    # the shared checkout: other people's files untouched, the staged one still staged
    assert snapshot(sh) == before
    assert read(sh, 'openai-ports/oaiq-002/notes.md') == 'their notes\n'
    assert git(sh, 'diff', '--cached', '--name-only') == 'openai-ports/oaiq-002/staged.md'
    # main was fast-forwarded (index only), so our records read as clean and theirs as theirs
    assert git(sh, 'rev-parse', 'main') == git(world['origin'], 'rev-parse', 'main')
    status = git(sh, 'status', '--porcelain')
    assert 'oaiq-001' not in status
    assert ' M other/x.md' in status.splitlines()
    assert 'fast-forwarded' in out
    assert_no_leftovers(world)


def test_absolute_paths_and_single_files(world):
    sh = world['shared']
    write(sh, 'openai-ports/wave/RESUME.md', 'wave, appended\n')
    rc, out = run(world, os.path.join(str(sh), 'openai-ports/wave/RESUME.md'), '-m', 'wave')
    assert rc == 0, out
    assert origin_show(world, 'openai-ports/wave/RESUME.md') == 'wave, appended'


def test_nothing_to_push(world):
    head = git(world['origin'], 'rev-parse', 'main')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'nothing')
    assert rc == 0, out
    assert 'nothing to push' in out
    assert git(world['origin'], 'rev-parse', 'main') == head
    assert_no_leftovers(world)


def test_message_from_file(world, tmp_path):
    write(world['shared'], 'openai-ports/oaiq-001/a.md', 'a\n')
    msgf = tmp_path / 'msg.txt'
    msgf.write_text('from a file\n\nbody\n')
    rc, out = run(world, 'openai-ports/oaiq-001', '-F', str(msgf))
    assert rc == 0, out
    assert git(world['origin'], 'log', '-1', '--format=%B', 'main') == 'from a file\n\nbody'


# ---- someone else pushed in between ------------------------------------------------------------

def test_non_fast_forward_is_retried_on_the_new_origin(world, monkeypatch, capsys):
    sh, other = world['shared'], world['other']
    write(sh, 'openai-ports/oaiq-001/mine.md', 'mine\n')
    real_fetch = push_records.fetch
    calls = []

    def fetch_then_race(top):
        sha = real_fetch(top)
        if not calls:                    # right after our first fetch, another clone pushes
            write(other, 'openai-ports/oaiq-002/theirs.md', 'theirs\n')
            git(other, 'add', '.')
            git(other, 'commit', '-qm', 'theirs')
            git(other, 'push', '-q', 'origin', 'main')
        calls.append(sha)
        return sha
    monkeypatch.setattr(push_records, 'fetch', fetch_then_race)
    monkeypatch.setattr(push_records, 'BACKOFF', 0)
    rc = push_records.main(['openai-ports/oaiq-001', '-m', 'mine', '--repo', str(sh)])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert len(calls) == 2 and calls[0] != calls[1]
    log = git(world['origin'], 'log', '--format=%s', 'main').splitlines()
    assert log[:2] == ['mine', 'theirs']
    assert {'openai-ports/oaiq-001/mine.md', 'openai-ports/oaiq-002/theirs.md'} <= origin_files(world)
    assert '2 attempts' in out
    # theirs.md never existed in the shared tree: the index-only fast-forward does not create it
    assert not os.path.exists(os.path.join(str(sh), 'openai-ports/oaiq-002/theirs.md'))
    assert_no_leftovers(world)


def test_warns_when_our_copy_replaces_a_newer_origin_version(world):
    sh, other = world['shared'], world['other']
    write(other, 'openai-ports/wave/RESUME.md', 'edited elsewhere\n')
    git(other, 'commit', '-qam', 'elsewhere')
    git(other, 'push', '-q', 'origin', 'main')
    write(sh, 'openai-ports/wave/RESUME.md', 'edited here\n')
    rc, out = run(world, 'openai-ports/wave', '-m', 'here')
    assert rc == 0, out
    assert 'warning' in out and 'openai-ports/wave/RESUME.md' in out
    assert origin_show(world, 'openai-ports/wave/RESUME.md') == 'edited here'


# ---- the shared checkout in a state nobody should touch ----------------------------------------

def _stuck_rebase(world):
    """The 2026-10-29 state: a conflicting `pull --rebase` left the shared checkout mid-rebase."""
    sh, other = world['shared'], world['other']
    write(other, 'other/x.md', 'origin side\n')
    git(other, 'commit', '-qam', 'origin side')
    git(other, 'push', '-q', 'origin', 'main')
    write(sh, 'other/x.md', 'local side\n')
    git(sh, 'commit', '-qam', 'local side')
    git(sh, 'pull', '-q', '--rebase', 'origin', 'main', check=False)
    assert os.path.isdir(os.path.join(str(sh), '.git', 'rebase-merge'))


def test_mid_rebase_checkout_is_left_alone_but_records_still_push(world):
    sh = world['shared']
    _stuck_rebase(world)
    head = git(sh, 'rev-parse', 'HEAD')
    main = git(sh, 'rev-parse', 'refs/heads/main')
    index = open(os.path.join(str(sh), '.git', 'index'), 'rb').read()
    write(sh, 'openai-ports/oaiq-001/during.md', 'during the rebase\n')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'during')
    assert rc == 0, out
    assert 'openai-ports/oaiq-001/during.md' in origin_files(world)
    assert 'rebase' in out and 'not moved' in out
    assert os.path.isdir(os.path.join(str(sh), '.git', 'rebase-merge'))
    assert git(sh, 'rev-parse', 'HEAD') == head
    assert git(sh, 'rev-parse', 'refs/heads/main') == main
    assert open(os.path.join(str(sh), '.git', 'index'), 'rb').read() == index
    assert_no_leftovers(world)


def test_local_commits_not_on_origin_keep_main_where_it_is(world):
    sh = world['shared']
    write(sh, 'other/x.md', 'an unpushed local commit\n')
    git(sh, 'commit', '-qam', 'unpushed')
    main = git(sh, 'rev-parse', 'main')
    write(sh, 'openai-ports/oaiq-001/a.md', 'a\n')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'a')
    assert rc == 0, out
    assert 'openai-ports/oaiq-001/a.md' in origin_files(world)
    assert origin_show(world, 'other/x.md') == 'x'          # the unpushed commit stays local
    assert git(sh, 'rev-parse', 'main') == main
    assert 'not on origin' in out and 'not moved' in out


# ---- deletions ---------------------------------------------------------------------------------

def test_deleted_files_stay_on_origin_unless_delete(world):
    sh = world['shared']
    os.remove(os.path.join(str(sh), 'openai-ports/oaiq-001/old.md'))
    write(sh, 'openai-ports/oaiq-001/RESUME.md', 'one\n')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'keep')
    assert rc == 0, out
    assert 'openai-ports/oaiq-001/old.md' in origin_files(world)
    assert '--delete' in out                                  # says what it left
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'drop', '--delete')
    assert rc == 0, out
    files = origin_files(world)
    assert 'openai-ports/oaiq-001/old.md' not in files
    assert 'openai-ports/oaiq-001/RESUME.md' in files
    assert 'openai-ports/oaiq-002/RESUME.md' in files
    # the shared tree still has no old.md, and nothing was restored into it
    assert not os.path.exists(os.path.join(str(sh), 'openai-ports/oaiq-001/old.md'))


def test_a_whole_deleted_folder_needs_delete(world):
    sh = world['shared']
    for f in ('RESUME.md', 'old.md'):
        os.remove(os.path.join(str(sh), 'openai-ports/oaiq-001', f))
    os.rmdir(os.path.join(str(sh), 'openai-ports/oaiq-001'))
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'gone')
    assert rc == 0, out
    assert 'nothing to push' in out and '--delete' in out
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'gone', '--delete')
    assert rc == 0, out
    assert not any(f.startswith('openai-ports/oaiq-001/') for f in origin_files(world))


# ---- refusals ----------------------------------------------------------------------------------

def test_refuses_openai_lean_unless_allowed(world):
    sh = world['shared']
    head = git(world['origin'], 'rev-parse', 'main')
    write(sh, 'openai-ports/oaiq-001/Port.lean', 'theorem t : True := trivial\n')
    write(sh, 'openai-ports/oaiq-001/notes.md', 'n\n')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'lean')
    assert rc == 1
    assert 'Port.lean' in out and '--allow-lean' in out
    assert git(world['origin'], 'rev-parse', 'main') == head
    assert_no_leftovers(world)
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'lean', '--allow-lean')
    assert rc == 0, out
    assert 'openai-ports/oaiq-001/Port.lean' in origin_files(world)


def test_lean_outside_openai_ports_is_fine(world):
    write(world['shared'], 'artin/Own.lean', 'theorem t : True := trivial\n')
    rc, out = run(world, 'artin', '-m', 'own lean')
    assert rc == 0, out
    assert 'artin/Own.lean' in origin_files(world)


def test_deleting_tracked_lean_is_not_staging_it(world):
    sh, other = world['shared'], world['other']
    write(other, 'openai-ports/oaiq-001/Old.lean', 'old\n')
    git(other, 'add', '.')
    git(other, 'commit', '-qm', 'old lean')
    git(other, 'push', '-q', 'origin', 'main')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'drop lean', '--delete')
    assert rc == 0, out
    assert 'openai-ports/oaiq-001/Old.lean' not in origin_files(world)


@pytest.mark.parametrize('bad', ['.', '', '..', '../elsewhere', '/etc/passwd', '.git', '.git/config'])
def test_refuses_paths_outside_or_the_whole_repo(world, bad):
    head = git(world['origin'], 'rev-parse', 'main')
    rc, out = run(world, bad, '-m', 'bad')
    assert rc != 0
    assert git(world['origin'], 'rev-parse', 'main') == head


def test_refuses_a_path_that_matches_nothing(world):
    rc, out = run(world, 'openai-ports/oaiq-999', '-m', 'typo')
    assert rc == 1 and 'oaiq-999' in out


def test_refuses_too_many_files(world):
    sh = world['shared']
    for i in range(6):
        write(sh, 'openai-ports/oaiq-001/carve/f%d.md' % i, '%d\n' % i)
    head = git(world['origin'], 'rev-parse', 'main')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'many', '--max-files', '5')
    assert rc == 1 and '--max-files' in out
    assert git(world['origin'], 'rev-parse', 'main') == head
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'many', '--max-files', '6')
    assert rc == 0, out


def test_requires_a_message(world):
    write(world['shared'], 'openai-ports/oaiq-001/a.md', 'a\n')
    rc, out = run(world, 'openai-ports/oaiq-001')
    assert rc != 0


# ---- failure and dry run -----------------------------------------------------------------------

def test_failed_push_leaves_nothing_behind(world, monkeypatch, capsys):
    sh = world['shared']
    write(sh, 'openai-ports/oaiq-001/a.md', 'a\n')
    hook = os.path.join(str(world['origin']), 'hooks', 'pre-receive')
    with open(hook, 'w') as f:
        f.write('#!/bin/sh\necho refused by policy >&2\nexit 1\n')
    os.chmod(hook, 0o755)
    monkeypatch.setattr(push_records, 'BACKOFF', 0)
    main = git(sh, 'rev-parse', 'main')
    rc = push_records.main(['openai-ports/oaiq-001', '-m', 'a', '--repo', str(sh)])
    out = capsys.readouterr()
    assert rc == 1
    assert 'refused by policy' in out.out + out.err
    assert git(sh, 'rev-parse', 'main') == main
    assert 'oaiq-001/a.md' in git(sh, 'status', '--porcelain', '-uall')
    assert_no_leftovers(world)


def test_dry_run_pushes_nothing_and_writes_no_objects(world):
    sh = world['shared']
    write(sh, 'openai-ports/oaiq-001/a.md', 'a dry run\n')
    head = git(world['origin'], 'rev-parse', 'main')
    objects = git(sh, 'count-objects', '-v')
    main = git(sh, 'rev-parse', 'main')
    rc, out = run(world, 'openai-ports/oaiq-001', '-m', 'dry', '--dry-run')
    assert rc == 0, out
    assert 'A openai-ports/oaiq-001/a.md' in out
    assert 'dry run' in out
    assert git(world['origin'], 'rev-parse', 'main') == head
    assert git(sh, 'count-objects', '-v') == objects
    assert git(sh, 'rev-parse', 'main') == main
    assert_no_leftovers(world)
