"""prune_solution.prune: unreachable declarations go, roots stay."""
import pytest

import prune_solution as P

SRC = '''import Mathlib

theorem used : True := trivial

open Nat in
theorem unused : True := trivial

@[simp] theorem attributed : True := trivial

theorem solution : True := used
'''


def test_unused_goes_with_its_open_in_prefix():
    # 7fa85b1: a dropped declaration takes its `open ... in` prefix with it
    out, doomed = P.prune(SRC, verbose=False)
    assert 'theorem unused' not in out and 'open Nat in' not in out
    assert 'theorem used' in out and 'theorem solution' in out


def test_attributed_declarations_are_roots():
    # faff7c3: tactics find @[simp] lemmas without naming them
    out, _ = P.prune(SRC, verbose=False)
    assert 'theorem attributed' in out


def test_refuses_without_solution():
    with pytest.raises(SystemExit):
        P.prune('theorem foo : True := trivial\n', verbose=False)
