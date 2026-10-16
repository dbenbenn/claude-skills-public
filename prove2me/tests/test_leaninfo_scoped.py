"""LeanInfo's parse-only mode reads Mathlib's `scoped[NS] notation` (it shapes later parsing)."""
import pytest

from p2mlib import leaninfo


@pytest.mark.lean
def test_parse_only_reads_mathlib_scoped_notation(tmp_path):
    # Erdős 3 v2: unread, every use of `○` / `𝟭_[…]` truncated its command at the notation, so a
    # local notation used past it looked unused and the command's identifiers were incomplete
    f = tmp_path / 'ScopedProbe.lean'
    f.write_text('import Mathlib\n\nscoped[P2MTest] notation "⊞" => (1 : Nat)\n\nopen scoped P2MTest\n\n'
                 'theorem probe_scoped : ⊞ + 1 = 2 := by\n  rfl\n')
    info = leaninfo.run(str(f), parse_only=True, idents=True, use_cache=False)
    thm = [c for c in info.commands if 'probe_scoped' in (c.names or [])]
    assert thm, [c.short_kind for c in info.commands]
    assert info.slice(thm[0].start.byte, thm[0].end.byte).rstrip().endswith('rfl')
