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
    assert not ok and lines[0].startswith('✖ [1/2] FAILED Solutions.F.A') and 'A.lean:2:0: error: boom' in out
    assert lines[-1].startswith('- [2/2] Skipped Solutions.F.Main')


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


def test_build_keeps_going_past_a_failed_module(monkeypatch, tmp_path, capsys):
    # oaiq-038/048: the build stopped at the first failing module, so each Mathlib-drift fix cost a
    # 5-13 min rebuild just to reach the next failure (24 cycles for LogConcave). Modules that do not
    # import a failed one still build, and every failure is reported in one run.
    from p2mlib import leaninfo
    ws = tmp_path / 'ws'
    d = ws / 'Solutions' / 'F'
    d.mkdir(parents=True)
    (d / 'A.lean').write_text('x\n')                                   # fails
    (d / 'B.lean').write_text('import Solutions.F.A\n')                # skipped: imports A
    (d / 'C.lean').write_text('y\n')                                   # fails too
    (d / 'D.lean').write_text('z\n')                                   # builds
    (d / 'Main.lean').write_text('import Solutions.F.B\nimport Solutions.F.C\nimport Solutions.F.D\n')
    built = []

    def fake(path, module, olean, ilean, ws=None, **k):
        m = module.rsplit('.', 1)[-1]
        if m in ('A', 'C'):
            return False, 1.0, ['%s:1:0: error: drift in %s' % (path, m)]
        built.append(m)
        open(olean, 'w').close()
        return True, 1.0, []
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    ok, lines = B.build(str(ws), 'F', 'Main')
    out = capsys.readouterr().out
    assert not ok and built == ['D']
    assert 'drift in A' in out and 'drift in C' in out
    assert any('Skipped Solutions.F.B' in l and 'Solutions.F.A' in l for l in lines)
    assert any('Skipped Solutions.F.Main' in l for l in lines)
    assert '2 modules failed' in out
