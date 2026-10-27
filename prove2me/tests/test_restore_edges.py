"""p2mlib.restore_edges: swap a false bundle import for the imports the edge check says it was
standing in for (work/false_edges.json 'restore'), in the generated bundle files."""
import json

from p2mlib import restore_edges


def test_swaps_false_import_for_restore_list(tmp_path):
    d = tmp_path / 'lib'
    d.mkdir()
    (d / 'Def_X021.lean').write_text(
        'import Mathlib\nimport Definitions.Def_X012\nimport Definitions.Def_X003\n\ndef a := 1\n')
    fe = tmp_path / 'false_edges.json'
    fe.write_text(json.dumps({'false_edges': [{
        'file': 'Def_X021.lean', 'import': 'Definitions.Def_X012',
        'restore': ['Definitions.Def_X001', 'Definitions.Def_X003']}]}))
    n = restore_edges.apply(str(fe), [str(d)])
    assert n == 1
    assert (d / 'Def_X021.lean').read_text() == (
        'import Mathlib\nimport Definitions.Def_X001\nimport Definitions.Def_X003\n\ndef a := 1\n')


def test_skips_edges_without_restore_and_is_idempotent(tmp_path):
    d = tmp_path / 'lib'
    d.mkdir()
    (d / 'Def_X.lean').write_text('import Definitions.Def_B\n')
    fe = tmp_path / 'f.json'
    fe.write_text(json.dumps({'false_edges': [
        {'file': 'Def_X.lean', 'import': 'Definitions.Def_B', 'restore': []}]}))
    assert restore_edges.apply(str(fe), [str(d)]) == 0
    assert (d / 'Def_X.lean').read_text() == 'import Definitions.Def_B\n'
