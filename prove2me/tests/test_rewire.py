"""rewire.py: a copy of a published theorem gets the published theorem as its proof, and the import."""
import json
import os

import pytest

import rewire as R

from p2mlib import leaninfo as LI
from p2mlib.workspace import Published

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')
DEP = Published('N.dep', 'Theorems.Thm_N_dep', ['n'])


@pytest.fixture
def info():
    # parse-only is all rewrite() needs: command ranges, names and `:=` positions
    data = json.load(open(os.path.join(FIX, 'Rewire.parse.json')))
    return LI.parse(data, open(os.path.join(FIX, 'Rewire.lean'), 'rb').read())


def test_copy_proof_replaced_by_published_call(info):
    out = R.rewrite(info, {"M.dep'": DEP})
    assert ':= by\n  simp\n' not in out                         # the old proof is gone
    # the copy's own statement and doc comment are kept
    assert "/-- a copy, primed -/\ntheorem dep' (n : ℕ) : n + 0 = n :=\n  by\n" in out
    assert 'exact N.dep n' in out
    assert out.count('import Theorems.Thm_N_dep') == 1 and out.startswith('import Theorems.Thm_N_dep')


def test_open_in_prefix_kept_and_import_added_once(info):
    out = R.rewrite(info, {"M.dep'": DEP, "M.dep''": DEP})
    assert out.count('import Theorems.Thm_N_dep') == 1
    assert "open Nat in\ntheorem dep'' (n : ℕ) : 0 + n = n :=\n  by" in out


def test_solution_and_others_untouched(info):
    out = R.rewrite(info, {"M.dep'": DEP})
    assert 'theorem solution : True := trivial' in out and 'theorem stub : 1 = 1 := by sorry' in out
    assert "theorem dep'' (n : ℕ) : 0 + n = n := Nat.zero_add n" in out


def test_add_imports_skips_present_ones():
    assert R.add_imports('import Mathlib\nimport A\n', ['A', 'B', 'B']) == 'import B\nimport Mathlib\nimport A\n'


def test_published_index(tmp_path):
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_N_dep.lean').write_text('namespace N\n\ntheorem dep (h : 1 = 1) : True := by\n  sorry\n\nend N\n')
    pub = R.published(str(tmp_path))
    assert pub['dep'][0] == 'N.dep' and pub['dep'][1] == 'Theorems.Thm_N_dep'


def test_published_index_ignores_comments(tmp_path):
    # was a strict xfail until Phase 3: one comment-aware published() (p2mlib.workspace)
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_N_dep.lean').write_text(
        '/-!\ntheorem for balls: a module docstring\n-/\nnamespace N\n\ntheorem dep : True := by\n  sorry\n\nend N\n')
    assert 'dep' in R.published(str(tmp_path))
