"""scripts/oai_fetch.py: an import closure comes from a local git clone of openai/math first, and
from raw.githubusercontent.com only for what the clone lacks, with backoff on HTTP 429
(2026-10-27: eleven worker lessons, oaiq-032..049, on 429s and on the workarounds that followed)."""
import io
import os
import subprocess
import sys
import urllib.error

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
import oai_fetch as F  # noqa: E402


def git(repo, *a):
    return subprocess.run(['git', '-C', str(repo)] + list(a), check=True, capture_output=True, text=True).stdout.strip()


@pytest.fixture
def repo(tmp_path):
    r = tmp_path / 'math'
    (r / 'lean' / 'OAI' / 'X').mkdir(parents=True)
    (r / 'lean' / 'ComparatorChallenges').mkdir(parents=True)
    (r / 'lean' / 'OAI' / 'X' / 'Main.lean').write_text('import Mathlib\nimport OAI.X.Lemma\nimport ComparatorChallenges.C\n')
    (r / 'lean' / 'OAI' / 'X' / 'Lemma.lean').write_text('import OAI.Lib\n')
    (r / 'lean' / 'OAI' / 'Lib.lean').write_text('-- leaf\n')
    (r / 'lean' / 'OAI' / 'Unrelated.lean').write_text('-- not in the closure\n')
    (r / 'lean' / 'ComparatorChallenges' / 'C.lean').write_text('-- challenge\n')
    git(r, 'init', '-q')
    git(r, '-c', 'user.email=t@t', '-c', 'user.name=t', 'add', '.')
    git(r, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qm', 'one')
    sha = git(r, 'rev-parse', 'HEAD')
    # a later commit changes a file: the fetch must read the requested commit, not the work tree
    (r / 'lean' / 'OAI' / 'Lib.lean').write_text('-- leaf, edited later\n')
    git(r, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qam', 'two')
    return r, sha


def no_network(*a, **k):
    raise AssertionError('network used although the clone had the file')


def test_closure_comes_from_the_clone_at_the_commit(repo, tmp_path, monkeypatch):
    r, sha = repo
    monkeypatch.setattr(F.urllib.request, 'urlopen', no_network)
    dest = tmp_path / 'dest'
    n, total, src = F.fetch(str(dest), 'OAI.X.Main', sha, git_repo=str(r))
    got = sorted(os.path.relpath(os.path.join(d, f), dest) for d, _, fs in os.walk(dest) for f in fs)
    assert got == ['lean/ComparatorChallenges/C.lean', 'lean/OAI/Lib.lean', 'lean/OAI/X/Lemma.lean', 'lean/OAI/X/Main.lean']
    assert (dest / 'lean' / 'OAI' / 'Lib.lean').read_text() == '-- leaf\n'
    assert n == 4 and src == {'git': 4}


def test_files_already_there_are_reused(repo, tmp_path, monkeypatch):
    r, sha = repo
    monkeypatch.setattr(F.urllib.request, 'urlopen', no_network)
    dest = tmp_path / 'dest'
    (dest / 'lean' / 'OAI' / 'X').mkdir(parents=True)
    (dest / 'lean' / 'OAI' / 'X' / 'Main.lean').write_text('import OAI.Lib\n')
    n, _, src = F.fetch(str(dest), 'OAI.X.Main', sha, git_repo=str(r))
    assert n == 2 and src == {'local': 1, 'git': 1}


class FakeResp(io.BytesIO):
    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


def test_missing_from_the_clone_falls_back_to_raw_with_backoff_on_429(repo, tmp_path, monkeypatch):
    r, sha = repo
    (r / 'lean' / 'OAI' / 'X' / 'Main.lean').write_text('import OAI.New\n')
    git(r, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qam', 'three')
    sha3 = git(r, 'rev-parse', 'HEAD')
    calls, sleeps = [], []

    def urlopen(url, timeout=None):
        calls.append(url)
        if len(calls) < 3:
            raise urllib.error.HTTPError(url, 429, 'Too Many Requests', {'Retry-After': '7'}, None)
        return FakeResp(b'-- from the network\n')
    monkeypatch.setattr(F.urllib.request, 'urlopen', urlopen)
    monkeypatch.setattr(F.time, 'sleep', sleeps.append)
    dest = tmp_path / 'dest'
    n, _, src = F.fetch(str(dest), 'OAI.X.Main', sha3, git_repo=str(r))
    assert src == {'git': 1, 'network': 1} and len(calls) == 3
    assert calls[0].endswith('/%s/lean/OAI/New.lean' % sha3)
    assert sleeps[0] >= 7 and sleeps[1] >= sleeps[0]          # Retry-After honoured, then growing
    assert (dest / 'lean' / 'OAI' / 'New.lean').read_text() == '-- from the network\n'


def test_raw_gives_up_after_its_retries(tmp_path, monkeypatch):
    def urlopen(url, timeout=None):
        raise urllib.error.HTTPError(url, 429, 'Too Many Requests', {}, None)
    monkeypatch.setattr(F.urllib.request, 'urlopen', urlopen)
    monkeypatch.setattr(F.time, 'sleep', lambda s: None)
    with pytest.raises(SystemExit) as e:
        F.fetch(str(tmp_path / 'dest'), 'OAI.X.Main', 'abc', git_repo=None)
    assert '429' in str(e.value)


def test_default_clone_is_found(tmp_path, monkeypatch):
    monkeypatch.setenv('P2M_OAI_GIT', str(tmp_path))
    (tmp_path / '.git').mkdir()
    assert F.default_git_repo() == str(tmp_path)
    monkeypatch.setenv('P2M_OAI_GIT', str(tmp_path / 'absent'))
    monkeypatch.setattr(F, 'CANDIDATES', ())
    assert F.default_git_repo() is None


def test_a_foreign_package_in_the_closure_is_reported_until_it_is_placed(repo, tmp_path, monkeypatch, capsys):
    # oaiq-083: 12 modules imported PrimeNumberTheoremAnd/StrongPNT, which openai/math does not contain;
    # the build then failed on "unknown module prefix" and skipped ~1460 modules
    r, sha = repo
    # module-system forms count too, and `import all M` is M, not a package called `all`
    (r / 'lean' / 'OAI' / 'Lib.lean').write_text('import Mathlib.Data.Nat.Basic\nimport all Mathlib.Foo\nimport Batteries\n'
                                                 'public import StrongPNT.Main\nimport PrimeNumberTheoremAnd.Mathlib.X\n')
    git(r, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-qam', 'foreign')
    sha2 = git(r, 'rev-parse', 'HEAD')
    monkeypatch.setattr(F.urllib.request, 'urlopen', no_network)
    dest = tmp_path / 'dest'
    foreign = {}
    F.fetch(str(dest), 'OAI.X.Main', sha2, git_repo=str(r), foreign=foreign)
    assert F.missing_packages(foreign, str(dest)) == {'PrimeNumberTheoremAnd': ['OAI.Lib'], 'StrongPNT': ['OAI.Lib']}
    with pytest.raises(SystemExit) as e:
        F.main([str(dest), 'OAI.X.Main', '--commit', sha2, '--git', str(r)])
    assert 'StrongPNT (imported by OAI.Lib)' in str(e.value) and 'beside OAI/' in str(e.value)
    # placed beside OAI/ (as a directory or a root file): the fetch goes through
    (dest / 'lean' / 'StrongPNT').mkdir()
    (dest / 'lean' / 'PrimeNumberTheoremAnd.lean').write_text('-- placed\n')
    F.main([str(dest), 'OAI.X.Main', '--commit', sha2, '--git', str(r)])
    assert '4 modules' in capsys.readouterr().out
