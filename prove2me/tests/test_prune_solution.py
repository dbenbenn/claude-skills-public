"""prune_solution.prune: unreachable declarations go, roots stay."""
import sys

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


def test_local_and_scoped_instances_are_declarations():
    # 2026-10-18: `noncomputable local instance hsNorm` was invisible to the parser, so it
    # folded into the declaration above and a bundle copy of it was never dropped (ThorpNine)
    src = ('namespace X\nnoncomputable local instance hsNorm : Norm Nat := ⟨id⟩\n'
           'scoped instance hsFinite : Inhabited Nat := ⟨0⟩\ntheorem t : True := trivial\nend X')
    assert [d[0] for d in P.parse(src.split('\n'))] == ['hsNorm', 'hsFinite', 't']


def test_refuses_a_file_that_does_not_elaborate(monkeypatch, tmp_path, capsys):
    # q167 (Viterbo capacity): an input with errors fell back to the name-based pruner, which deleted
    # load-bearing declarations; it now refuses and leaves the file alone
    from p2mlib import leaninfo
    f = tmp_path / 'Sol.lean'
    f.write_text(SRC)
    broken = leaninfo.Info(str(f), 'elaborate', [], [], [leaninfo.Message(
        'error', leaninfo.Pos(3, 0, 0), leaninfo.Pos(3, 1, 1), 'unknown identifier `foo`')])
    monkeypatch.setattr(leaninfo, 'run', lambda *a, **k: broken)
    monkeypatch.setattr(sys, 'argv', ['prune_solution.py', str(f)])
    with pytest.raises(SystemExit) as e:
        P.main()
    assert e.value.code not in (0, None)
    assert 'does not elaborate' in str(e.value) and 'unknown identifier `foo`' in str(e.value)
    assert f.read_text() == SRC
