"""p2mlib.copies: copies of published theorems found by statement (Phase 4.2).

Offline: candidate selection on a synthetic workspace. With P2M_LEAN=1: LeanInfo --candidates on
lean_fixtures/Copies.lean against two real, immutable Mathlib-only published theorems."""
import os

import pytest

from p2mlib import copies

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')


def test_imports_of_ignores_comments():
    text = '/- import Nope -/\n-- import AlsoNope\nimport Mathlib\nimport Definitions.Def_A\n'
    assert copies.imports_of(text) == ['Mathlib', 'Definitions.Def_A']


@pytest.fixture
def ws(tmp_path):
    def put(mod, *imps, body=''):
        p = tmp_path.joinpath(*mod.split('.')).with_suffix('.lean')
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(''.join('import %s\n' % i for i in imps) + body)
    put('Definitions.Def_A', 'Mathlib')
    put('Definitions.Def_B', 'Mathlib', 'Definitions.Def_A')
    put('Definitions.Def_C', 'Mathlib')
    put('Theorems.Thm_X_a', 'Mathlib', 'Definitions.Def_A', body='namespace X\ntheorem a : True := by sorry\nend X\n')
    put('Theorems.Thm_X_b', 'Mathlib', 'Definitions.Def_B', body='namespace X\ntheorem b : True := by sorry\nend X\n')
    put('Theorems.Thm_Y_c', 'Mathlib', 'Definitions.Def_C', body='theorem Y.c : True := by sorry\n')
    put('Theorems.Thm_M_d', 'Mathlib', body='theorem M.d : True := by sorry\n')
    copies._direct.cache_clear()
    return str(tmp_path)


def test_candidates_are_the_theorems_whose_definitions_the_file_sees(ws):
    assert copies.candidates(ws, 'import Mathlib\nimport Definitions.Def_A\n') == \
        ['Theorems.Thm_M_d', 'Theorems.Thm_X_a']
    # Def_B reaches Def_A
    assert copies.candidates(ws, 'import Definitions.Def_B\n') == \
        ['Theorems.Thm_M_d', 'Theorems.Thm_X_a', 'Theorems.Thm_X_b']
    # through a Theorems import too
    assert 'Theorems.Thm_X_b' in copies.candidates(ws, 'import Theorems.Thm_X_b\n')


def test_a_theorem_the_file_declares_is_not_a_candidate(ws):
    # importing it would clash ("already declared")
    assert copies.candidates(ws, 'import Definitions.Def_A\n', declared={'X.a'}) == ['Theorems.Thm_M_d']


@pytest.mark.lean
def test_find_by_statement_not_name():
    _, found = copies.find(os.path.join(FIX, 'Copies.lean'))
    assert found == {'Dev.my_zpow': ['HomeoLine.zpow_moves_of_moves'],
                     'Dev.fib_copy': ['BlockCycleRotation.fib_two_le']}
