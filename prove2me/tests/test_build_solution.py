"""build_solution.py: which imports of the merged modules are carried into the solution."""
import build_solution as BS


def test_external_imports_keeps_bundles_and_published_theorems_only(tmp_path):
    a = tmp_path / 'A.lean'
    a.write_text('import Mathlib\nimport Definitions.Def_Monod_PiecewiseProjective\n'
                 'import Solutions.M51.Blueprint\nimport Theorems.Thm_Monod_x\n\ntheorem a : True := trivial\n')
    b = tmp_path / 'B.lean'
    b.write_text('import Definitions.Def_Monod_PiecewiseProjective\nimport Definitions.Def_CFP\n')
    assert BS.external_imports([str(a), str(b)]) == [
        'Definitions.Def_Monod_PiecewiseProjective', 'Theorems.Thm_Monod_x', 'Definitions.Def_CFP']


def test_external_imports_skips_dropped_theorems(tmp_path):
    # a --drop target is imported by resolve_imports only if it is Proved; carrying the stub's
    # import here would turn an inlined copy into a reduction
    a = tmp_path / 'A.lean'
    a.write_text('import Theorems.Thm_DenseSL2_exists_elliptic\nimport Theorems.Thm_Monod_x\n')
    assert BS.external_imports([str(a)], drop=['DenseSL2.exists_elliptic']) == ['Theorems.Thm_Monod_x']
