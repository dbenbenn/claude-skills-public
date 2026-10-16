"""p2mlib.localcheck: the pure parts of a local check that predicts the verifier (Erdős 3, 2026-10-16)."""
from p2mlib import localcheck as L

SOL = """import Mathlib
import Definitions.Def_B1
import Theorems.Thm_Other

theorem foo_oai : True := trivial

theorem solution : type_of% @foo_oai := @foo_oai
"""
PRE = "import Mathlib\nimport Definitions.Def_B0\n"
FS = "theorem foo : True := by sorry\n"


def test_server_check_text_merges_imports_and_appends_the_check():
    t = L.server_check_text(SOL, PRE, FS, 'foo')
    head = [l for l in t.split('\n') if l.startswith('import ')]
    assert head == ['import Mathlib', 'import Definitions.Def_B1', 'import Theorems.Thm_Other',
                    'import Definitions.Def_B0']
    assert t.index('theorem foo_oai') < t.index('theorem foo :') < t.index('theorem _check')
    assert t.rstrip().endswith('theorem _check : type_of% @foo := @solution')
    # every import comes before any other text
    first_non_import = next(i for i, l in enumerate(t.split('\n')) if l and not l.startswith('import '))
    assert all(not l.startswith('import ') for l in t.split('\n')[first_non_import:])


def test_content_key_follows_imported_lib_files(tmp_path):
    lib = tmp_path / 'lib'; lib.mkdir()
    (lib / 'Def_B1.lean').write_text('def b := 1\n')
    sol = tmp_path / 'Sol.lean'; sol.write_text(SOL)
    k1 = L.content_key(str(sol), str(lib))
    assert k1 == L.content_key(str(sol), str(lib))
    (lib / 'Def_B1.lean').write_text('def b := 2\n')
    assert L.content_key(str(sol), str(lib)) != k1
    assert L.content_key(str(sol), str(lib), version='2') != L.content_key(str(sol), str(lib))
