"""publish_standalone.long_titles: the platform refuses a title over 200 characters (2026-10-10:
'theorem_title must be at most 200 characters', after the bundle in the same run had published)."""
import publish_standalone as ps


def test_long_titles_flags_only_overlong():
    payloads = [{'theorem_name': 'NS.ok', 'theorem_title': 'x' * 200},
                {'theorem_name': 'NS.long', 'theorem_title': 'y' * 201}]
    defs = [{'definition_name': 'D', 'definition_title': 'z' * 250}]
    assert ps.long_titles(payloads, defs) == ['Def_D', 'NS.long']
    assert ps.long_titles(payloads[:1], []) == []
