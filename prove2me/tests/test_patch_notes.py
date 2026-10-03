"""patch_notes.py: PATCH live natural-language statements from <dir>/<name>/new.md, against a fake platform."""
import json

import pytest

import patch_notes as PN


class Fake:
    def __init__(self, live):
        self.live, self.patched = dict(live), []

    def call(self, m, p, b=None):
        tid = p.split('/')[2]
        if m == 'GET':
            return {'theorem_id': tid, 'natural_language_statement': self.live[tid]}
        if m == 'PATCH':
            self.patched.append(tid)
            self.live[tid] = b['natural_language_statement']
            return {'theorem_id': tid}
        raise AssertionError((m, p))


@pytest.fixture
def folder(tmp_path):
    for n, old, new in [('A', 'old a', 'new a'), ('B', 'same b', 'same b')]:
        (tmp_path / n).mkdir()
        (tmp_path / n / 'old.md').write_text(old)
        (tmp_path / n / 'new.md').write_text(new + '\n')
    (tmp_path / 'ids.json').write_text(json.dumps({'A': 'ida', 'B': 'idb'}))
    return tmp_path


def test_dry_run_patches_nothing_and_go_patches_only_changed_and_verifies(folder, capsys):
    fake = Fake({'ida': 'old a', 'idb': 'same b'})
    PN.run(str(folder), go=False, call=fake.call)
    assert fake.patched == [] and 'would PATCH A' in capsys.readouterr().out
    PN.run(str(folder), go=True, call=fake.call)
    assert fake.patched == ['ida'] and fake.live['ida'] == 'new a'
    assert 'verified A' in capsys.readouterr().out


def test_refuses_when_live_text_is_not_old_md(folder):
    # someone edited the live note since old.md was fetched: do not overwrite it blindly
    fake = Fake({'ida': 'edited elsewhere', 'idb': 'same b'})
    with pytest.raises(SystemExit):
        PN.run(str(folder), go=True, call=fake.call)
    assert fake.patched == []


def test_refuses_an_escaped_quote(folder):
    (folder / 'A' / 'new.md').write_text('a \\"quote\\"\n')
    with pytest.raises(SystemExit):
        PN.run(str(folder), go=True, call=Fake({'ida': 'old a', 'idb': 'same b'}).call)
