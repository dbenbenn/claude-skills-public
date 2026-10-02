"""draft.extract_payloads: each statement's preamble imports exactly the bundles it uses."""
import draft


def payloads(tmp_path, text, ns, bundles):
    p = tmp_path / 'Thm.lean'
    p.write_text(text)
    return draft.extract_payloads(str(p), ns, bundles)


BUNDLES = {'Definitions.Def_A': ['A.Word', 'A.Step'], 'Definitions.Def_P': ['Step']}


def test_qualified_and_bare_names_resolve_to_different_bundles(tmp_path):
    # LodhaMoorePosCommute (2026-10-02): bare `Step` is the new bundle's, `A.Step` the old one's
    out = payloads(tmp_path, 'namespace P\n\ntheorem t : ∀ w : A.Word, Relation.ReflTransGen Step w w := by\n  sorry\n\nend P\n',
                   'P', BUNDLES)
    pre, fs = out['t']
    assert 'import Definitions.Def_A' in pre and 'import Definitions.Def_P' in pre


def test_dotted_use_does_not_match_bare_identifier(tmp_path):
    out = payloads(tmp_path, 'namespace Q\n\ntheorem t (h : A.Step [] []) : True := by\n  sorry\n\nend Q\n', 'Q', BUNDLES)
    pre, _ = out['t']
    assert 'Def_P' not in pre and 'Def_A' in pre


def test_unused_bundle_is_not_imported(tmp_path):
    out = payloads(tmp_path, 'namespace Q\n\ntheorem t : True := by\n  sorry\n\nend Q\n', 'Q', BUNDLES)
    assert out['t'][0] == 'import Mathlib'


def test_universe_declared_for_type_u(tmp_path):
    out = payloads(tmp_path, 'namespace Q\n\ntheorem t (α : Type u) : True := by\n  sorry\n\nend Q\n', 'Q', {})
    assert 'universe u' in out['t'][0]
