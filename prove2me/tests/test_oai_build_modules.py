"""scripts/oai_build_modules.py: module names may end in a prime (OpenAI's IntegralDensityMeasureLp'
beside IntegralDensityMeasureLp; WeakHessian, oaiq-052)."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
import oai_build_modules as B  # noqa: E402


def test_module_imports_keep_a_trailing_prime(tmp_path):
    (tmp_path / 'A.lean').write_text("import Mathlib\nimport P.B'\nimport P.C\nimport P.D.E'\n")
    assert B.module_imports(str(tmp_path), 'P', 'A') == ["B'", 'C', "D.E'"]


# ---- one elaboration per module (2026-10-27) ---------------------------------------------------
# Modules compile through p2mlib.leaninfo.build_module, which also leaves `carve.py graph` its
# reading; the logged time is LeanInfo's build_ms (the compile, not its reporting).

def _port(tmp_path):
    ws = tmp_path / 'ws'
    d = ws / 'Solutions' / 'F'
    d.mkdir(parents=True)
    (d / 'A.lean').write_text('theorem a : True := trivial\n')
    (d / 'Main.lean').write_text('import Solutions.F.A\ntheorem m : True := a\n')
    return str(ws)


def test_build_compiles_through_leaninfo_in_import_order(monkeypatch, tmp_path, capsys):
    from p2mlib import leaninfo
    ws = _port(tmp_path)
    calls = []

    def fake(path, module, olean, ilean, ws=None, **k):
        calls.append((module, olean, ilean))
        open(olean, 'w').close()
        return True, 2.5, []
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    monkeypatch.setattr(B.subprocess, 'run', lambda *a, **k: (_ for _ in ()).throw(AssertionError('plain lean')))
    ok, lines = B.build(ws, 'F', 'Main')
    assert ok and [c[0] for c in calls] == ['Solutions.F.A', 'Solutions.F.Main']
    assert calls[0][1].endswith(os.path.join('.lake', 'build', 'lib', 'lean', 'Solutions', 'F', 'A.olean'))
    assert calls[0][2].endswith('A.ilean')
    assert lines[0] == '✔ [1/2] Built Solutions.F.A (2.5s)'


def test_build_failure_prints_lean_style_errors(monkeypatch, tmp_path, capsys):
    from p2mlib import leaninfo
    ws = _port(tmp_path)
    monkeypatch.setattr(leaninfo, 'build_module', lambda path, *a, **k: (False, 1.0, ['%s:2:0: error: boom' % path]))
    ok, lines = B.build(ws, 'F', 'Main')
    out = capsys.readouterr().out
    assert not ok and lines[-1].startswith('✖ [1/2] FAILED Solutions.F.A') and 'A.lean:2:0: error: boom' in out


def test_build_falls_back_to_lean_without_the_compiled_tool(monkeypatch, tmp_path):
    from p2mlib import leaninfo
    ws = _port(tmp_path)
    monkeypatch.setattr(leaninfo, 'build_module', lambda *a, **k: None)
    seen = []

    class R:
        returncode, stdout, stderr = 0, '', ''

    def run(args, **k):
        seen.append(args)
        open(args[args.index('-o') + 1], 'w').close()
        return R()
    monkeypatch.setattr(B.subprocess, 'run', run)
    ok, _ = B.build(ws, 'F', 'Main')
    assert ok and seen[0][:3] == ['lake', 'env', 'lean'] and '-DautoImplicit=false' in seen[0]
