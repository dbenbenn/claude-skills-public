"""caveat_audit.py: what the prose auditor is given, and its verdict."""
import os
import types

import pytest

import caveat_audit as CA
from mini import make_mission


@pytest.fixture
def mdir(tmp_path, monkeypatch):
    m = make_mission(tmp_path / 'm')
    (m / 'paper.pdf').write_bytes(b'%PDF fake')
    (m / 'mission.py').write_text((m / 'mission.py').read_text() + "\nSOURCE_PDF = 'paper.pdf'\n")
    for ext in ('claims', 'coverage'):
        (m / 'readbacks' / ('t1.%s.md' % ext)).write_text('%s of t1\n' % ext)
    monkeypatch.setattr(CA, 'ROOT', str(tmp_path / 'auditors'))
    monkeypatch.setattr(CA.subprocess, 'run',
                        lambda args, check=False, **k: open(args[-1] + '.png', 'w').write('img') and types.SimpleNamespace(returncode=0))
    return m


def staged(mdir):
    return os.path.join(CA.ROOT, CA.slug(str(mdir), 't1'))


def test_stage_hands_over_prose_audits_and_bundle_notes(mdir, tmp_path):
    cite = tmp_path / 'book.txt'
    cite.write_text('the cited text')
    CA.stage(str(mdir), 't1', [str(cite)])
    files = sorted(os.listdir(staged(mdir)))
    for f in ('brief.md', 'readback.md', 'claims.md', 'coverage.md', 'milestone.md', 'nls.md',
              'cite-book.txt', 'bundle-Mini.md'):               # ed1afad: the bundle notes too
        assert f in files
    assert 'Lemma 1 — one' in open(os.path.join(staged(mdir), 'nls.md')).read()


def test_stage_needs_the_source_audit_first(mdir):
    os.remove(mdir / 'readbacks' / 't1.coverage.md')
    with pytest.raises(SystemExit):
        CA.stage(str(mdir), 't1', [])


@pytest.mark.parametrize('line,code', [('CAVEATS: adequate', 0), ('CAVEATS: inadequate: the title', 1)])
def test_collect(mdir, line, code):
    CA.stage(str(mdir), 't1', [])
    open(os.path.join(staged(mdir), 'verdict.md'), 'w').write('## 1\nfine\n\n' + line + '\n')
    with pytest.raises(SystemExit) as e:
        CA.collect(str(mdir), 't1')
    assert e.value.code == code and (mdir / 'readbacks' / 't1.caveats.md').read_text().endswith(line + '\n')


@pytest.mark.xfail(strict=True, reason="caveat_audit.stage deletes an existing staging directory, so "
                   "re-staging wipes a live auditor's files -- the hazard stage_auditor.stage refuses "
                   "(four auditors lost their work that way)")
def test_restage_refuses_a_live_directory(mdir):
    CA.stage(str(mdir), 't1', [])
    open(os.path.join(staged(mdir), 'verdict.md'), 'w').write('half written')
    with pytest.raises(SystemExit):
        CA.stage(str(mdir), 't1', [])
