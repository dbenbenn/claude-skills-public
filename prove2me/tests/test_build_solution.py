"""build_solution.py: which imports of the merged modules are carried into the solution."""
import os

import pytest

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


def test_assembler_recognizes_the_blueprint_by_its_path(tmp_path):
    # CFW (2026-10-03): the route blueprint is Solutions/CFW/Route.lean; only modules named
    # *Blueprint were recognized, so its import would have been kept beside its inlined text
    import assemble_blueprint as AB
    ws = tmp_path
    bp = ws / 'Solutions' / 'CFW' / 'Route.lean'
    parts = ['import Solutions.CFW.Route\nimport Mathlib\n', 'import Solutions.LN.Blueprint\n']
    assert AB.blueprint_modules(str(bp), parts, str(ws)) == {'Solutions.CFW.Route', 'Solutions.LN.Blueprint'}


def test_wrapper_drops_universes_the_body_already_declares():
    # Garrido full strength (2026-10-04): the development declares `universe u v` at the top of its
    # file, and so does the published statement; the wrapper re-declared it and Lean answered
    # "a universe level named `u` has already been declared"
    body = 'universe u v\n\nsection\nnamespace Garrido\ntheorem foo : True := trivial\nend Garrido\nend\n'
    stmt = 'universe u v\n\ntheorem solution {G : Type u} : True := by\n  trivial\n'
    assert BS.drop_redeclared_universes(body, stmt) == '\ntheorem solution {G : Type u} : True := by\n  trivial\n'


def test_wrapper_keeps_new_universes_and_ignores_sectioned_ones():
    # a universe declared inside a section is out of scope after `end`; only names already at the
    # top level are dropped, and a line keeps the names that are new
    body = 'universe u\n\nsection\nuniverse w\nend\n'
    stmt = 'universe u v w\n\ntheorem solution : True := trivial\n'
    assert BS.drop_redeclared_universes(body, stmt) == 'universe v w\n\ntheorem solution : True := trivial\n'


def test_module_body_keeps_doc_lines_that_start_with_import():
    # 2026-10-18: a docstring line "import the stub of a7e19a77 nor ... -/" was dropped as an import,
    # taking the comment's closing -/ with it ("unterminated comment" in the merged solution)
    src = ('import Mathlib\nimport Solutions.Artin.T12.L3E_MainP\n\n/-! # L3E_DevP\n\nDoes not\n'
           'import the stub of a7e19a77 nor of the E6 draft. -/\n\ntheorem t : True := trivial\n')
    body = BS.module_body(src)
    assert 'import Mathlib' not in body and 'L3E_MainP' not in body
    assert 'import the stub of a7e19a77 nor of the E6 draft. -/' in body
    assert body.lstrip().startswith('/-! # L3E_DevP')


def test_wrapped_module_keeps_its_imports_for_merge():
    # 2026-10-29 (oaiq-111): the wrapped copies were written without their import header, so
    # merge.py's parse check (13b5bf0) read them without `import Mathlib` and refused every merge
    import merge
    text = 'import Mathlib\nimport Solutions.TaoBR111.CubeA\n\nopen Real\n\ntheorem a : True := trivial\n'
    w = BS.wrap_module(text)
    assert merge.header([w]) == 'import Mathlib\n'
    assert 'section\nopen Real\n\ntheorem a : True := trivial\n\nend\n' in w


def test_wrapper_applies_the_dev_theorem_when_the_target_name_is_not_declared():
    # 2026-10-29 (oaiq-111): developments name their theorem `<target>_dev`; the wrapper applied
    # the published name, which resolve_imports then inlined as the target's own sorried statement
    text = 'namespace TaoBR\ntheorem restr_zero_of_restr_dev (n : Nat) : True := trivial\nend TaoBR\n'
    assert BS.dev_theorem(text, 'TaoBR.restr_zero_of_restr') == 'TaoBR.restr_zero_of_restr_dev'
    text2 = 'namespace TaoBR\ntheorem restr_zero_of_restr (n : Nat) : True := trivial\nend TaoBR\n'
    assert BS.dev_theorem(text2, 'TaoBR.restr_zero_of_restr') == 'TaoBR.restr_zero_of_restr'


SUB_NAMESPACE_DEV = '''section
namespace TaoBR
namespace RSU
/-- the development's theorem -/
theorem restr_sparse_of_restr_uniform_dev (n : Nat) : True := trivial
end RSU
end TaoBR
end
'''


def test_dev_theorem_in_a_sub_namespace_is_found_by_its_last_component():
    # 2026-11-03 (q158): the development's theorem was TaoBR.RSU.restr_sparse_of_restr_uniform_dev;
    # the wrapper applied the non-existent TaoBR.restr_sparse_of_restr_uniform_dev and
    # resolve_imports died on an unrelated parse error in a scratch file it deleted
    assert (BS.dev_theorem(SUB_NAMESPACE_DEV, 'TaoBR.restr_sparse_of_restr_uniform')
            == 'TaoBR.RSU.restr_sparse_of_restr_uniform_dev')


def test_dev_theorem_prefers_the_targets_own_dev_name_and_sees_aliases():
    # the lesson's fix, an alias in the target's namespace, is used as written
    text = SUB_NAMESPACE_DEV + ('\nnamespace TaoBR\nalias restr_sparse_of_restr_uniform_dev := '
                                'RSU.restr_sparse_of_restr_uniform_dev\nend TaoBR\n')
    assert (BS.dev_theorem(text, 'TaoBR.restr_sparse_of_restr_uniform')
            == 'TaoBR.restr_sparse_of_restr_uniform_dev')


def test_dev_theorem_missing_fails_up_front():
    # a commented-out declaration does not count, nor does the target's short name elsewhere
    text = ('/- theorem foo_dev : True := trivial -/\nnamespace Other\n'
            'theorem foo (n : Nat) : True := trivial\nend Other\n')
    with pytest.raises(SystemExit) as e:
        BS.dev_theorem(text, 'N.foo')
    msg = str(e.value)
    assert 'no `N.foo_dev` in the development' in msg and 'alias' in msg


def test_dev_theorem_ambiguous_lists_the_candidates():
    text = ('namespace N.A\ntheorem foo_dev : True := trivial\nend N.A\n'
            'namespace N.B\nlemma foo_dev : True := trivial\nend N.B\n')
    with pytest.raises(SystemExit) as e:
        BS.dev_theorem(text, 'N.foo')
    assert 'N.A.foo_dev' in str(e.value) and 'N.B.foo_dev' in str(e.value)


def test_dev_theorem_warns_when_the_development_declares_the_target(capsys):
    # the verifier's trap (references/verifier-failures.md): a solution file declaring the target's
    # full name with a different signature gets a locationless WA
    text = 'namespace TaoBR\ntheorem restr_zero_of_restr (n : Nat) : True := trivial\nend TaoBR\n'
    assert BS.dev_theorem(text, 'TaoBR.restr_zero_of_restr') == 'TaoBR.restr_zero_of_restr'
    assert 'declares the target' in capsys.readouterr().err
    BS.dev_theorem('namespace TaoBR\ntheorem restr_zero_of_restr_dev : True := trivial\nend TaoBR\n',
                   'TaoBR.restr_zero_of_restr')
    assert capsys.readouterr().err == ''
