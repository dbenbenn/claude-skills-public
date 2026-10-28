"""p2mlib.snapshot / scripts/skill_snapshot.py: a skill checkout materialised read-only under a
cache, so a carve's many tool processes all run one version of the code (2026-10-25: a push
mid-run mixed old and new carve.py inside one carve)."""
import os
import subprocess
import sys
import time

import pytest

from conftest import SCRIPTS

from p2mlib import snapshot


def git(repo, *a):
    return subprocess.run(['git', '-C', str(repo), '-c', 'user.name=t', '-c', 'user.email=t@t', *a],
                          check=True, capture_output=True, text=True).stdout.strip()


@pytest.fixture
def repo(tmp_path):
    r = tmp_path / 'skills'
    (r / 'prove2me' / 'scripts').mkdir(parents=True)
    (r / 'prove2me' / 'scripts' / 'tool.py').write_text('print("v1")\n')
    git(r, 'init', '-q', '-b', 'main')
    git(r, 'add', '-A')
    git(r, 'commit', '-qm', 'v1')
    return r


@pytest.fixture
def cache(tmp_path):
    return tmp_path / 'cache'


def test_snapshot_of_head_is_created_read_only_and_reused(repo, cache):
    p = snapshot.snapshot(str(repo), cache=str(cache))
    sha = git(repo, 'rev-parse', 'HEAD')
    assert os.path.basename(p) == sha and os.path.dirname(p) == str(cache)
    f = os.path.join(p, 'prove2me', 'scripts', 'tool.py')
    assert open(f).read() == 'print("v1")\n'
    with pytest.raises(PermissionError):
        open(f, 'w')
    with pytest.raises(PermissionError):
        open(os.path.join(p, 'new.txt'), 'w')
    ino = os.stat(f).st_ino
    assert snapshot.snapshot(str(repo), cache=str(cache)) == p           # reused, not rebuilt
    assert os.stat(f).st_ino == ino


def test_a_later_commit_gets_its_own_snapshot_and_the_old_one_is_unchanged(repo, cache):
    p1 = snapshot.snapshot(str(repo), cache=str(cache))
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("v2")\n')
    git(repo, 'commit', '-qam', 'v2')
    p2 = snapshot.snapshot(str(repo), cache=str(cache))
    assert p1 != p2
    assert open(os.path.join(p1, 'prove2me/scripts/tool.py')).read() == 'print("v1")\n'
    assert open(os.path.join(p2, 'prove2me/scripts/tool.py')).read() == 'print("v2")\n'


def test_dirty_tree_snapshots_head_with_a_warning_unless_allowed(repo, cache, capsys):
    # 2026-10-28 (oaiq-055): agents share one checkout, so it is dirty most of the time with someone
    # else's work in progress; refusing blocked every new carve, and the way out (--allow-dirty)
    # snapshotted that half-done code. Without --allow-dirty the snapshot is HEAD, with a warning.
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("dirty")\n')
    head = snapshot.snapshot(str(repo), cache=str(cache))
    assert '-dirty-' not in os.path.basename(head)
    assert open(os.path.join(head, 'prove2me/scripts/tool.py')).read() == 'print("v1")\n'
    err = capsys.readouterr().err
    assert 'uncommitted' in err and 'tool.py' in err and 'not in this snapshot' in err
    p = snapshot.snapshot(str(repo), cache=str(cache), allow_dirty=True)
    assert '-dirty-' in os.path.basename(p)
    assert open(os.path.join(p, 'prove2me/scripts/tool.py')).read() == 'print("dirty")\n'
    assert snapshot.snapshot(str(repo), cache=str(cache), allow_dirty=True) == p   # same content, same hash
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("dirty2")\n')
    assert snapshot.snapshot(str(repo), cache=str(cache), allow_dirty=True) != p


def test_dirty_snapshot_includes_untracked_but_not_ignored_files(repo, cache):
    (repo / '.gitignore').write_text('*.pyc\n')
    git(repo, 'add', '-A')
    git(repo, 'commit', '-qm', 'ignore')
    (repo / 'prove2me' / 'new.py').write_text('x = 1\n')
    (repo / 'prove2me' / 'junk.pyc').write_text('junk')
    p = snapshot.snapshot(str(repo), cache=str(cache), allow_dirty=True)
    assert os.path.exists(os.path.join(p, 'prove2me', 'new.py'))
    assert not os.path.exists(os.path.join(p, 'prove2me', 'junk.pyc'))


def test_snapshot_of_an_explicit_revision(repo, cache):
    sha1 = git(repo, 'rev-parse', 'HEAD')
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("v2")\n')
    git(repo, 'commit', '-qam', 'v2')
    p = snapshot.snapshot(str(repo), rev=sha1, cache=str(cache))
    assert os.path.basename(p) == sha1


def test_prune_removes_old_snapshots_only(repo, cache):
    p1 = snapshot.snapshot(str(repo), cache=str(cache))
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("v2")\n')
    git(repo, 'commit', '-qam', 'v2')
    p2 = snapshot.snapshot(str(repo), cache=str(cache))
    old = time.time() - 40 * 86400
    os.utime(p1, (old, old))
    gone = snapshot.prune(str(cache), max_age_days=30)
    assert gone == [p1] and not os.path.exists(p1) and os.path.isdir(p2)


def test_reuse_refreshes_age_so_a_snapshot_in_use_is_not_pruned(repo, cache):
    p1 = snapshot.snapshot(str(repo), cache=str(cache))
    old = time.time() - 40 * 86400
    os.utime(p1, (old, old))
    snapshot.snapshot(str(repo), cache=str(cache))
    assert snapshot.prune(str(cache), max_age_days=30) == []


def test_cli_prints_the_path(repo, cache):
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'skill_snapshot.py'), '--repo', str(repo),
                        '--cache', str(cache)], capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == os.path.join(str(cache), git(repo, 'rev-parse', 'HEAD'))
    (repo / 'prove2me' / 'scripts' / 'tool.py').write_text('print("d")\n')
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'skill_snapshot.py'), '--repo', str(repo),
                        '--cache', str(cache)], capture_output=True, text=True)
    assert r.returncode == 0 and r.stdout.strip() == os.path.join(str(cache), git(repo, 'rev-parse', 'HEAD'))
    assert 'prove2me/scripts/tool.py' in r.stderr and 'not in this snapshot' in r.stderr
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'skill_snapshot.py'), '--repo', str(repo),
                        '--cache', str(cache), '--allow-dirty'], capture_output=True, text=True)
    assert r.returncode == 0 and '-dirty-' in r.stdout


def test_inside_detects_a_path_in_the_cache(repo, cache):
    p = snapshot.snapshot(str(repo), cache=str(cache))
    assert snapshot.snapshot_root_of(os.path.join(p, 'prove2me', 'scripts', 'tool.py'), cache=str(cache)) == p
    assert snapshot.snapshot_root_of(str(repo / 'prove2me' / 'scripts' / 'tool.py'), cache=str(cache)) is None


def test_default_repo_inside_a_snapshot_is_the_live_skills_repo(tmp_path, monkeypatch):
    # oaiq-059: --upgrade --detach re-ran inside a snapshot, whose parent is no git repo ("not a git repository")
    import importlib.util
    cache = tmp_path / 'cache'
    fake = cache / 'abc123' / 'prove2me' / 'p2mlib'
    fake.mkdir(parents=True)
    src = open(os.path.join(os.path.dirname(__file__), '..', 'p2mlib', 'snapshot.py')).read()
    (fake / 'snapshot.py').write_text(src)
    monkeypatch.setenv('P2M_SNAPSHOT_CACHE', str(cache))
    spec = importlib.util.spec_from_file_location('snap_copy', fake / 'snapshot.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    assert m.default_repo() == os.path.expanduser('~/.claude/skills')
