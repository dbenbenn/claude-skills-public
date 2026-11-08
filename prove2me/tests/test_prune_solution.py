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


def _check_run(monkeypatch, tmp_path, cpu, rss):
    """main --check on a clean file whose compile took `cpu` s and peaked at `rss` MiB."""
    from p2mlib import localcheck
    f = tmp_path / 'Sol.lean'
    f.write_text(SRC)
    monkeypatch.setattr(P, 'prune_by_lean', lambda path: SRC)
    monkeypatch.setattr(localcheck, 'run_lean', lambda args, cwd, env=None: (0, '', cpu, rss))
    monkeypatch.setenv('P2M_WORKSPACE', str(tmp_path))
    monkeypatch.setattr(sys, 'argv', ['prune_solution.py', str(f), '--check'])
    P.main()


def test_check_reports_cpu_and_peak_memory_and_warns_over_the_verifier_limits(monkeypatch, tmp_path, capsys):
    # q196, q209 (2026-11-05/06): whole-file solutions of 126 s and 119 s single-threaded (52 s wall) timed out
    # twice each at the verifier's 300 s; q153 (2026-11-08): files peaking over ~7 GiB are killed for memory.
    # --check measures both, so the split happens before the first submission (dbenbenn 2026-11-08)
    from p2mlib import carvepipeline as CP
    _check_run(monkeypatch, tmp_path, 40.0, 6800)
    out = capsys.readouterr().out
    assert 'compiles clean' in out and '40 s CPU' in out and '6800 MiB' in out and 'SPLIT' not in out
    _check_run(monkeypatch, tmp_path, CP.PIECE_CAP + 19.0, 6800)
    out = capsys.readouterr().out
    assert 'SPLIT' in out and 'time' in out
    _check_run(monkeypatch, tmp_path, 40.0, CP.PIECE_RSS_LIMIT + 50)
    out = capsys.readouterr().out
    assert 'SPLIT' in out and 'memory' in out
