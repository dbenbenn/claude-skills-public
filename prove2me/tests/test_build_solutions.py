"""build_solutions.assemble: the merged development and the check block that becomes `theorem solution`.

Each test is a bug that shipped (git log of scripts/build_solutions.py)."""
import pytest

import build_solutions as B

CHECK = '''import Solutions.X.Statements

/-! # checks -/

namespace A.Dev

/-- open questions remain about this helper -/
theorem helper : True := trivial

theorem isMarginal_EBad' : True := trivial

end A.Dev

namespace A

open Classical CannonFloydParry

open A.Dev in
theorem chk_foo : True := by
  exact trivial

open B in
theorem chk_bar : True := trivial

theorem chk_isMarginal_EBad : True := A.Dev.isMarginal_EBad'

#print axioms A.chk_foo

end A
'''


STATEMENTS = 'namespace A\ntheorem stub : True := by sorry\nend A\n'


def build(tmp_path, name):
    sol = tmp_path / 'Solutions'
    (sol / 'X').mkdir(parents=True)
    (sol / 'X' / 'Statements.lean').write_text(STATEMENTS)
    (sol / 'Chk.lean').write_text(CHECK)
    st, text, ns = B.assemble(str(sol), ['Chk'], name, str(tmp_path))
    assert st == 'OK', st
    return text, text[text.rindex('\nsection\n'):], ns


@pytest.mark.lean
def test_open_in_directly_above_is_kept(tmp_path):
    # 874fb3a: `open X in` was copied verbatim, giving `open X in in` (20 of 31 Moore solutions)
    _, sol, _ = build(tmp_path, 'foo')
    assert 'open A.Dev in\ntheorem solution : True := by\n  exact trivial' in sol and ' in in' not in sol


@pytest.mark.lean
def test_open_in_elsewhere_is_dropped(tmp_path):
    _, sol, _ = build(tmp_path, 'bar')
    assert 'A.Dev' not in sol and 'open B in\ntheorem solution : True := trivial' in sol


@pytest.mark.lean
def test_block_stops_before_next_blocks_open_in(tmp_path):
    # e6ee4c1: the block swallowed the next block's `open B in`, leaving it dangling at EOF
    _, sol, _ = build(tmp_path, 'foo')
    assert 'open B' not in sol and sol.rstrip().endswith('exact trivial\nend')


@pytest.mark.lean
def test_prime_aware_name_match(tmp_path):
    # e6ee4c1: `isMarginal_EBad\\b` matched the dev lemma `isMarginal_EBad'` -> `theorem solution'`
    _, sol, _ = build(tmp_path, 'isMarginal_EBad')
    assert "theorem solution : True := A.Dev.isMarginal_EBad'" in sol and "solution'" not in sol


@pytest.mark.lean
def test_docstring_text_is_not_an_open_command(tmp_path):
    # a8a1cc1: a docstring line beginning "open" was copied into a solution as an `open` command
    _, sol, _ = build(tmp_path, 'foo')
    assert 'questions' not in sol


@pytest.mark.lean
def test_solution_at_top_level_with_its_namespace_opened(tmp_path):
    text, sol, ns = build(tmp_path, 'foo')
    assert ns == 'A' and 'namespace' not in sol and '\nopen A\n' in sol
    assert 'open Classical CannonFloydParry' in sol                # the scope's own opens


@pytest.mark.lean
def test_helpers_kept_check_blocks_dropped(tmp_path):
    # the check file's own helpers are merged (Moore 2026-10-01); every other check block goes
    text, _, _ = build(tmp_path, 'foo')
    assert 'theorem helper' in text and "theorem isMarginal_EBad'" in text and 'theorem stub' in text
    assert 'chk_' not in text


@pytest.mark.lean
def test_diagnostic_commands_are_dropped(tmp_path):
    # `#print axioms A.chk_foo` named the renamed block: the solution did not compile (LM 2026-10-02)
    text, _, _ = build(tmp_path, 'foo')
    assert '#print' not in text


AMBIG = '''import Solutions.X.Statements

namespace A.P5

theorem chk_baz : True := trivial

end A.P5

namespace A

alias chk_baz := A.P5.chk_baz

theorem chk_foo : True := trivial

end A
'''


@pytest.mark.lean
@pytest.mark.parametrize('name', ['foo', 'baz'])
def test_chk_alias_or_duplicate_is_refused(tmp_path, name):
    # CFW 2026-10-03: a development's own `P5.chk_baz` was stripped as a check block, while the
    # `alias chk_baz := P5.chk_baz` survived (an alias reports no names), so every solution failed
    # with "Unknown constant"; refuse with a reason instead of emitting a broken file
    sol = tmp_path / 'Solutions'
    (sol / 'X').mkdir(parents=True)
    (sol / 'X' / 'Statements.lean').write_text(STATEMENTS)
    (sol / 'Chk.lean').write_text(AMBIG)
    st, _, _ = B.assemble(str(sol), ['Chk'], name, str(tmp_path))
    assert st.startswith('CHECK-AMBIGUOUS') and 'chk_baz' in st, st
