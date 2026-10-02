"""rewire.py: a copy of a published theorem gets the published theorem as its proof, and the import."""
import pytest

import rewire as R

PUB = {'dep': ('N.dep', 'Theorems.Thm_N_dep', [])}

SRC = '''import Mathlib

namespace N

theorem dep' (n : Nat) : n = n := by
  induction n <;> rfl

end N

theorem solution : (3 : Nat) = 3 := N.dep' 3
'''


def test_copy_proof_replaced_by_published_call():
    out = R.rewrite(SRC, {"dep'"}, PUB)
    assert 'induction n' not in out
    assert "theorem dep' (n : Nat) : n = n :=" in out          # the copy's own statement is kept
    assert 'exact N.dep' in out
    assert out.count('import Theorems.Thm_N_dep') == 1 and out.startswith('import Theorems.Thm_N_dep')


def test_import_added_once_for_two_copies():
    src = SRC.replace("end N", "theorem dep'' (n : Nat) : n = n := rfl\n\nend N")
    out = R.rewrite(src, {"dep'", "dep''"}, PUB)
    assert out.count('import Theorems.Thm_N_dep') == 1


def test_solution_itself_untouched():
    out = R.rewrite(SRC, {"dep'"}, PUB)
    assert "theorem solution : (3 : Nat) = 3 := N.dep' 3" in out


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
