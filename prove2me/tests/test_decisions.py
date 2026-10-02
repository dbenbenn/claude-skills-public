"""decisions.py: one row per finding, decisions bound to the audit they answer."""
import pytest

import decisions as DE
from mini import make_mission

COV = '''# Coverage of t1

- C1 COVERED: one holds.
- **C3, C4** MISSING: the paper also says the constant is explicit,
  which the statement leaves out entirely.
- C5 COVERED.

VERDICT: WEAKER: C3, C4 (C5 is faithful, and so is the C6 aside)
DIRECTNESS: indirect -- the statement asks for an extra
hypothesis the paper does not have.
'''

CLAIMS = '''- **C3.** The constant is explicit.
- C4: It is at most 2.
'''


@pytest.fixture
def mdir(tmp_path):
    m = make_mission(tmp_path)
    (m / 'readbacks' / 't1.coverage.md').write_text(COV)
    (m / 'readbacks' / 't1.claims.md').write_text(CLAIMS)
    (m / 'readbacks' / 'goal.coverage.md').write_text('VERDICT: faithful\nDIRECTNESS: direct\n')
    return m


def test_findings_skip_parenthetical_ids_and_keep_whole_bullet(mdir):
    rows = dict(DE._findings(str(mdir / 'readbacks' / 't1.coverage.md')))
    assert set(rows) == {'C3', 'C4', 'DIRECTNESS'}                 # not C5/C6 from the aside
    assert rows['C3'].endswith('which the statement leaves out entirely.')   # 8588594: whole wrapped bullet
    assert 'extra hypothesis the paper does not have' in rows['DIRECTNESS']


def test_claims_text_bold_or_plain():
    import tempfile, os
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, 'c.md')
        open(p, 'w').write(CLAIMS)
        assert DE._claims(p) == {'C3': 'The constant is explicit.', 'C4': 'It is at most 2.'}


def test_build_check_decide_and_reopen(mdir):
    DE.build(str(mdir))
    text = (mdir / 'DECISIONS.md').read_text()
    assert '- claim: The constant is explicit.' in text                  # c634d78: the claim's own text
    bad = DE.check(str(mdir))
    assert len([b for b in bad if b[1].startswith('gap-review')]) == 3
    # the human decides every row; regenerating keeps the decisions while the audit is unchanged
    (mdir / 'DECISIONS.md').write_text(text.replace('- decided: \n', '- decided: dbenbenn, 2026-10-02: accept\n'))
    DE.build(str(mdir))
    assert DE.check(str(mdir)) == []
    # a re-audit changes coverage.md: the rows reopen and the old answer moves to `previously:`
    (mdir / 'readbacks' / 't1.coverage.md').write_text(COV + '\n(re-run)\n')
    assert any('stale' in why for _, why in DE.check(str(mdir)))
    DE.build(str(mdir))
    text = (mdir / 'DECISIONS.md').read_text()
    assert '- previously: dbenbenn, 2026-10-02: accept' in text and '- decided: \n' in text


def test_missing_file_is_bad(mdir):
    assert DE.check(str(mdir))[0][0] == 'DECISIONS.md'
