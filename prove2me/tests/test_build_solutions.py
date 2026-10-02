"""build_solutions.find_block: the check block that becomes `theorem solution`.

Each test is a bug that shipped (git log of scripts/build_solutions.py)."""
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

end A
'''


def block(tmp_path, name):
    (tmp_path / 'Chk.lean').write_text(CHECK)
    return B.find_block(str(tmp_path), ['Chk'], name)


def test_open_in_directly_above_is_kept_without_in(tmp_path):
    # 874fb3a: `open X in` was copied verbatim, giving `open X in in` (20 of 31 Moore solutions)
    mod, ns, opens, blk = block(tmp_path, 'foo')
    assert 'A.Dev' in opens and not any(o.endswith(' in') for o in opens)


def test_open_in_elsewhere_is_dropped(tmp_path):
    mod, ns, opens, blk = block(tmp_path, 'bar')
    assert 'A.Dev' not in opens and 'B' in opens


def test_block_stops_before_next_blocks_open_in(tmp_path):
    # e6ee4c1: the block swallowed the next block's `open B in`, leaving it dangling at EOF
    mod, ns, opens, blk = block(tmp_path, 'foo')
    assert blk.startswith('theorem solution')
    assert 'open B in' not in blk and blk.rstrip().endswith('exact trivial')


def test_prime_aware_name_match(tmp_path):
    # e6ee4c1: `isMarginal_EBad\\b` matched the dev lemma `isMarginal_EBad'` -> `theorem solution'`
    mod, ns, opens, blk = block(tmp_path, 'isMarginal_EBad')
    assert blk.startswith('theorem solution :') and "solution'" not in blk


def test_docstring_text_is_not_an_open_command(tmp_path):
    # a8a1cc1: a docstring line beginning "open" was copied into a solution as an `open` command
    mod, ns, opens, blk = block(tmp_path, 'foo')
    assert not any('questions' in o for o in opens)


def test_namespace_of_block(tmp_path):
    mod, ns, opens, blk = block(tmp_path, 'foo')
    assert ns == 'A' and mod == 'Chk'
