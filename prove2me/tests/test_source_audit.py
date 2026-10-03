"""source_audit.py: what the auditor is given, the phase gates, rephase2, collect's verdict."""
import os
import types

import pytest

import source_audit as SRC
import stage_auditor as SA
from mini import make_mission

DESC = ('p. 2, Lemma 1: “One holds for every $n$:\n\n$$n = n,$$\n\nwhich is all we need.”\n\n'
        '*Route.* The proof says “a different quoted sentence” and that is not under audit.')


RENDERED = []


@pytest.fixture
def mdir(tmp_path, monkeypatch):
    m = make_mission(tmp_path / 'm')
    (m / 'paper.pdf').write_bytes(b'%PDF fake')
    s = (m / 'mission.py').read_text()
    s = s.replace("milestone_description='p. 2: “One holds.”'", 'milestone_description=%r' % DESC)
    (m / 'mission.py').write_text(s + "\nSOURCE_PDF = 'paper.pdf'\nCONTEXT_PAGES = '1'\n")
    root = str(tmp_path / 'auditors')
    monkeypatch.setattr(SRC, 'ROOT', root)          # imported by name from stage_auditor: two copies
    monkeypatch.setattr(SA, 'ROOT', root)
    RENDERED.clear()
    rendered = RENDERED

    def fake_run(args, check=False, **k):           # pdftoppm: record the page, write a stand-in image
        rendered.append(int(args[2]))
        open(args[-1] + '.png', 'w').write('img')
        return types.SimpleNamespace(returncode=0)
    monkeypatch.setattr(SRC.subprocess, 'run', fake_run)
    return m


def test_pages():
    assert SRC.pages('12-14, 4,7') == [4, 7, 12, 13, 14] and SRC.pages('3–4') == [3, 4]


def test_stage_gives_only_the_opening_quote_and_the_pages(mdir, capsys):
    SRC.stage(str(mdir), 't1')
    d = os.path.join(SRC.ROOT, SRC.slug(str(mdir), 't1'))
    src = open(os.path.join(d, 'source.md')).read()
    # Monod Prop 9: a quote containing a displayed formula set off by blank lines is kept whole;
    # Monod M7: quotes in a *Route* paragraph are not the sentence under audit
    assert 'One holds for every $n$: $$n = n,$$ which is all we need.' in src
    assert 'different quoted sentence' not in src
    assert sorted(RENDERED) == [1, 2] and 'PHASE 1 only' in capsys.readouterr().out
    assert not os.path.exists(os.path.join(d, 'readback.md'))          # phase 1 never sees the Lean


def test_reveal_refuses_until_claims_are_complete(mdir):
    SRC.stage(str(mdir), 't1')
    d = os.path.join(SRC.ROOT, SRC.slug(str(mdir), 't1'))
    open(os.path.join(d, 'claims.md'), 'w').write('- C1. One holds.\n')        # still being written
    with pytest.raises(SystemExit):
        SRC.reveal(str(mdir), 't1')
    open(os.path.join(d, 'claims.md'), 'a').write('END OF CLAIMS\n')
    SRC.reveal(str(mdir), 't1')
    assert os.path.exists(os.path.join(d, 'readback.md'))


def test_rephase2_keeps_claims_and_supersedes_coverage(mdir, capsys):
    r = mdir / 'readbacks'
    (r / 't1.claims.md').write_text('- C1. One holds.\nEND OF CLAIMS\n')
    (r / 't1.coverage.md').write_text('VERDICT: WEAKER: C1\n')
    SRC.rephase2(str(mdir), 't1')
    d = os.path.join(SRC.ROOT, SRC.slug(str(mdir), 't1'))
    assert open(os.path.join(d, 'claims.md')).read().endswith('END OF CLAIMS\n')
    assert os.path.exists(os.path.join(d, 'readback.md'))
    assert not (r / 't1.coverage.md').exists() and (r / 'superseded' / 't1.coverage.md').exists()
    assert 'PHASE 1 is already done' in capsys.readouterr().out


@pytest.mark.parametrize('cov,ok', [('VERDICT: faithful\nDIRECTNESS: direct\n', True),
                                    ('VERDICT: WEAKER: C1\nDIRECTNESS: direct\n', False)])
def test_collect_verdict(mdir, cov, ok):
    SRC.stage(str(mdir), 't1')
    d = os.path.join(SRC.ROOT, SRC.slug(str(mdir), 't1'))
    open(os.path.join(d, 'claims.md'), 'w').write('- C1. x\nEND OF CLAIMS\n')
    open(os.path.join(d, 'coverage.md'), 'w').write(cov)
    assert bool(SRC.collect(str(mdir), 't1')) is ok
    assert (mdir / 'readbacks' / 't1.coverage.md').read_text() == cov and not os.path.exists(d)


def test_stage_warns_when_the_bundle_has_no_source_audit_yet(mdir, capsys):
    # CFW 2026-10-03: every statement was audited before the bundle; verify caught it only at the
    # gap review. The skill runs the bundle's audit first (statement audits skip bundle encodings).
    s = (mdir / 'mission.py').read_text()
    (mdir / 'mission.py').write_text(s.replace("result='Def 1')", "result='Def 1', source_pages='1')"))
    SRC.stage(str(mdir), 't1')
    assert 'Def_Mini has no source audit yet' in capsys.readouterr().out
    os.makedirs(mdir / 'readbacks', exist_ok=True)
    (mdir / 'readbacks' / 'Def_Mini.coverage.md').write_text('VERDICT: faithful\n')
    SRC.stage(str(mdir), 'goal')
    assert 'no source audit yet' not in capsys.readouterr().out


def test_bundle_phase2_gets_the_bundle_note(mdir):
    # CFW 2026-10-03: the note quoted Definition 1(2) without its subject ("the discrete measured
    # equivalence relation R"), hiding a presupposition; phase 2 now checks the note's quotes
    s = (mdir / 'mission.py').read_text()
    (mdir / 'mission.py').write_text(s.replace("result='Def 1')", "result='Def 1', source_pages='1')"))
    SRC.stage(str(mdir), 'Def_Mini')
    d = os.path.join(SRC.ROOT, SRC.slug(str(mdir), 'Def_Mini'))
    open(os.path.join(d, 'claims.md'), 'w').write('- D1. k.\nEND OF CLAIMS\n')
    os.makedirs(mdir / 'readbacks', exist_ok=True)
    (mdir / 'readbacks' / 'Def_Mini.readback.md').write_text('k is 1.\n')
    SRC.reveal(str(mdir), 'Def_Mini')
    assert 'Defines $k$.' in open(os.path.join(d, 'note.md')).read()
    assert os.path.exists(os.path.join(d, 'context.md'))
