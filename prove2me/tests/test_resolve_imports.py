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


@pytest.mark.xfail(strict=True, reason="extract() matches only lines starting `theorem`/`lemma`, so "
                   "`@[simp] theorem` is not found (Phase 4: LeanInfo declaration ranges include attributes)")
def test_extract_finds_inline_attribute_declaration(tmp_path):
    p = tmp_path / 'A.lean'
    p.write_text('@[simp] theorem s (n : ℕ) : n + 0 = n := rfl\n')
    assert RI.extract(str(p), 's') is not None


@pytest.mark.xfail(strict=True, reason="an attribute line above the declaration is not carried into the "
                   "inlined copy, so an inlined @[simp] lemma silently leaves the simp set")
def test_extract_keeps_attribute_line(tmp_path):
    p = tmp_path / 'A.lean'
    p.write_text('@[simp]\ntheorem s (n : ℕ) : n + 0 = n := rfl\n')
    assert RI.extract(str(p), 's').startswith('@[simp]')


@pytest.mark.parametrize('theorem,want', [
    ({'theorem_name': 'N.x', 'status': 'Proved', 'deprecated_at': None}, True),
    ({'theorem_name': 'N.x', 'status': 'Open', 'deprecated_at': None}, False),       # import = a reduction
    ({'theorem_name': 'N.x', 'status': 'Proved', 'deprecated_at': '2026-09-27'}, False),  # QFS: retired
])
def test_proved_decides_import_vs_inline(monkeypatch, theorem, want):
    monkeypatch.setattr(RI, 'call', lambda m, p, b=None: {'theorems': [theorem]})
    assert RI.proved('N', 'x') is want
