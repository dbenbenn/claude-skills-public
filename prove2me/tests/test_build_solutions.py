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


# `lake env lean -Dpp.fullNames=true` on a solution whose check block lived in `namespace A.B`:
# at the top level, under `open A` and `open A.B`, a name both namespaces define is ambiguous,
# while inside `namespace A.B` the inner one won (CFW Corollary 13, 2026-10-03)
LEAN_OUT = '''/tmp/Sol_x.lean:11:38: error: Ambiguous term
  x
Possible interpretations:
  A.B.x n : n = n

  A.x n : n = n
/tmp/Sol_x.lean:12:9: error: Ambiguous term
  x.z
Possible interpretations:
  @A.x.z n : n = n

  A.B.x.z n : n = n
/tmp/Sol_x.lean:13:2: error: unsolved goals
'''


def test_parse_ambiguities():
    assert B.parse_ambiguities(LEAN_OUT) == [
        (11, 38, 'x', ['A.B.x', 'A.x']),
        (12, 9, 'x.z', ['A.x.z', 'A.B.x.z'])]


@pytest.mark.parametrize('ns, want', [
    ('A.B', 'A.B.x'),            # the inner namespace wins, as inside `namespace A.B`
    ('A.B.C', 'A.B.x'),          # the longest enclosing namespace
    ('A.C', 'A.x'),              # A.B does not enclose A.C
    ('C', None),                 # nothing encloses: ambiguous inside the namespace too; left alone
])
def test_qualify_ambiguous_takes_the_innermost_enclosing_namespace(ns, want):
    text = 'theorem solution (n : Nat) : n = n := x n\n'
    new, done = B.qualify_ambiguous(text, [(1, 38, 'x', ['A.B.x', 'A.x'])], ns)
    if want is None:
        assert new == text and done == []
    else:
        assert new == 'theorem solution (n : Nat) : n = n := %s n\n' % want and done == [('x', want)]


def test_qualify_ambiguous_columns_are_codepoints_and_edits_go_right_to_left():
    # Lean's columns count codepoints: `μ` before the term must not shift it
    text = 'example (μ : Nat) := (x μ, x μ)\n'
    amb = [(1, 22, 'x', ['A.x', 'A.B.x']), (1, 27, 'x', ['A.x', 'A.B.x']),
           (1, 22, 'x', ['A.x', 'A.B.x'])]                      # a repeated report is one edit
    new, done = B.qualify_ambiguous(text, amb, 'A.B')
    assert new == 'example (μ : Nat) := (A.B.x μ, A.B.x μ)\n' and len(done) == 2


def test_qualify_ambiguous_skips_a_position_that_does_not_hold_the_term():
    text = 'theorem solution : True := y\n'
    new, done = B.qualify_ambiguous(text, [(1, 27, 'x', ['A.B.x', 'A.x'])], 'A.B')
    assert new == text and done == []


@pytest.mark.lean
def test_repair_ambiguity_compiles(tmp_path):
    f = tmp_path / 'Sol_x.lean'
    f.write_text('namespace A\ntheorem x (n : Nat) : n = n := rfl\nnamespace B\n'
                 'theorem x (n : Nat) : n = n := rfl\nend B\nend A\n'
                 'section\nopen A\nopen A.B\ntheorem solution (n : Nat) : n = n := x n\nend\n')
    done = B.repair_ambiguity(str(f), 'A.B')
    assert done == [('x', 'A.B.x')]
    assert 'theorem solution (n : Nat) : n = n := A.B.x n' in f.read_text()


def test_solution_section_drops_universes_declared_at_top_level():
    # markov-heat-kernels 2026-10-04: H2, H4, H8, H9 failed with "a universe level named `u` has
    # already been declared": scope_wrap re-creates the check block's scope, including the
    # `universe u` the merged file already declares at its top level
    body = 'universe u\n\nnamespace A\ntheorem chk_x {X : Type u} : True := trivial\nend A\n'
    sol = 'section\nuniverse u v\nopen A\n\ntheorem solution {X : Type u} : True := trivial\nend\n'
    out = B.with_solution(body, sol)
    assert out.count('universe u') == 1 and 'universe v' in out
    assert out.startswith(body) and out.rstrip().endswith('end')
