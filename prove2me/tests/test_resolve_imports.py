"""resolve_imports.py helpers: what gets inlined, with what context, and what may be imported."""
import pytest

import resolve_imports as RI

SRC = '''import Mathlib

variable {d : ℕ}
  (h : d = d)

/-- the main lemma -/
theorem foo (n : ℕ) : n = n := rfl

theorem foo' (n : ℕ) : n = n := by
  rfl

open Nat in
theorem bar : True := trivial
'''


@pytest.fixture
def src(tmp_path):
    p = tmp_path / 'M.lean'
    p.write_text(SRC)
    return str(p)


def test_extract_takes_doc_comment_and_stops_at_next_command(src):
    t = RI.extract(src, 'foo')
    assert t.startswith('/-- the main lemma -/') and "foo'" not in t


def test_extract_is_prime_aware(src):
    assert RI.extract(src, "foo'").startswith("theorem foo' ") and 'rfl' in RI.extract(src, "foo'")


def test_variables_before_with_continuation(src):
    # QFS 2026-09-27: inlined lemmas written under `variable {d : ℕ}` failed with autoImplicit off
    assert RI.variables_before(src, 'foo') == ['variable {d : ℕ}\n  (h : d = d)']


def test_extract_finds_inline_attribute_declaration(tmp_path):
    p = tmp_path / 'A.lean'
    p.write_text('@[simp] theorem s (n : ℕ) : n + 0 = n := rfl\n')
    assert RI.extract(str(p), 's') is not None


def test_extract_keeps_attribute_line(tmp_path):
    p = tmp_path / 'A.lean'
    p.write_text('/-- doc -/\n@[simp]\ntheorem s (n : ℕ) : n + 0 = n := rfl\n')
    assert RI.extract(str(p), 's').startswith('/-- doc -/\n@[simp]\ntheorem s')
    assert RI.find_src(str(tmp_path), 's') == str(p)


@pytest.mark.parametrize('theorem,want', [
    ({'theorem_name': 'N.x', 'status': 'Proved', 'deprecated_at': None}, True),
    ({'theorem_name': 'N.x', 'status': 'Open', 'deprecated_at': None}, False),       # import = a reduction
    ({'theorem_name': 'N.x', 'status': 'Proved', 'deprecated_at': '2026-09-27'}, False),  # QFS: retired
])
def test_proved_decides_import_vs_inline(monkeypatch, theorem, want):
    monkeypatch.setattr(RI, 'call', lambda m, p, b=None: {'theorems': [theorem]})
    assert RI.proved('N', 'x') is want


def test_header_carries_raw_modules_before_named_theorems(tmp_path):
    # dense-subgroups 2026-10-03: a development on the Monod bundle failed with "cannot find a
    # source for HB" -- only Def_<ns>_* bundles were re-imported, and the merged modules' own
    # `import Definitions.Def_Monod_PiecewiseProjective` had been stripped
    (tmp_path / 'Definitions').mkdir()
    (tmp_path / 'Definitions' / 'Def_QFS_A.lean').write_text('')
    h = RI.header(str(tmp_path), 'Def_QFS_', ['Definitions.Def_Monod_PiecewiseProjective',
                                              'Theorems.Thm_CannonFloydParry_bijOn_dyadic',
                                              'Definitions.Def_QFS_A'], ['N.x'], 'QFS')
    assert h == ['import Definitions.Def_QFS_A', 'import Definitions.Def_Monod_PiecewiseProjective',
                 'import Theorems.Thm_CannonFloydParry_bijOn_dyadic', 'import Theorems.Thm_N_x',
                 'import Mathlib', '']
