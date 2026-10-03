"""build_solution.py: which imports of the merged modules are carried into the solution."""
import os
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


def test_package_defaults_to_the_module_path_root(tmp_path):
    # 2026-10-03: the default was QuadraticFormsSobolev (from the QFS mission), so a module under
    # Solutions/ merged only itself and resolve_imports failed on the unmerged LN development
    (tmp_path / 'Solutions' / 'LN').mkdir(parents=True)
    (tmp_path / 'Solutions' / 'LNS').mkdir(parents=True)
    (tmp_path / 'Solutions' / 'LN' / 'A.lean').write_text('import Mathlib\ntheorem a : True := trivial\n')
    (tmp_path / 'Solutions' / 'LNS' / 'P.lean').write_text('import Mathlib\nimport Solutions.LN.A\n')
    assert BS.package_of('Solutions/LNS/P.lean') == 'Solutions'
    mods = BS.closure(str(tmp_path), BS.package_of('Solutions/LNS/P.lean'), 'Solutions/LNS/P.lean',
                      ['Solutions/LN', 'Solutions/LNS'])
    assert [os.path.relpath(m, tmp_path) for m in mods] == ['Solutions/LN/A.lean', 'Solutions/LNS/P.lean']


TWO_NAMESPACES = '''section
namespace Dev.PartB
theorem cover : True := trivial
end Dev.PartB
end

section
namespace Dev
alias cover := Dev.PartB.cover
end Dev
end

section
namespace LN
theorem cover : True := Dev.cover
theorem graph : True := cover
end LN
end
'''


def test_drop_matches_the_qualified_name_when_it_exists():
    # Lusin-Novikov standalone (2026-10-03): --drop LN.cover also dropped Dev.PartB.cover and the
    # alias Dev.cover (same last component), which the kept code still needed
    lines, dropped = BS.drop_declarations(TWO_NAMESPACES.split('\n'), ['LN.cover'])
    text = '\n'.join(lines)
    assert dropped == ['LN.cover']
    assert 'namespace Dev.PartB\ntheorem cover' in text and 'alias cover := Dev.PartB.cover' in text
    assert 'theorem graph' in text and 'theorem cover : True := Dev.cover' not in text


def test_drop_falls_back_to_the_short_name():
    # a development copy under another namespace (no exact match) is still dropped, as before
    lines, dropped = BS.drop_declarations(TWO_NAMESPACES.split('\n'), ['Published.graph'])
    assert dropped == ['LN.graph'] and 'theorem graph' not in '\n'.join(lines)


def test_dropped_theorems_without_a_workspace_statement_are_listed_for_fetching(tmp_path):
    # Lusin-Novikov (2026-10-03): resolve_imports cannot import a dropped theorem whose statement
    # file was never fetched; it tried to inline a same-named development lemma instead
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_LN_have.lean').write_text('')
    assert BS.missing_statements(str(tmp_path), ['LN.have', 'LN.need', 'short']) == ['LN.need']
