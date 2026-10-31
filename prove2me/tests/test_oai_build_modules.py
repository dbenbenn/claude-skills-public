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


# ---- a rebuild keeps the times of the modules it replays (2026-10-29) ------------------------------
# The pipeline's build step writes --elab-log build_elab.log, which carve_prep config reads for the cost
# model; a replayed module has no time, and a module missing from the log is costed at a default 2 s.
# oaiq-047's build_elab.log held 37 modules after a resumed build had replayed 1222 (oaiq-091: 0 of 419),
# so most of the plan was costed at the default.

def _run_main(monkeypatch, tmp_path, ws, fake, *extra):
    from p2mlib import leaninfo
    monkeypatch.setenv('P2M_LOCK_DIR', str(tmp_path / 'locks'))
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    log, elab = str(tmp_path / 'build.log'), str(tmp_path / 'build_elab.log')
    try:
        B.main(['F', 'Main', '--ws', ws, '--log', log, '--elab-log', elab, '--overhead', '1', *extra])
    except SystemExit as e:
        return e.code, log, elab
    return 0, log, elab


def _fake_build(secs, fail=()):
    def fake(path, module, olean, ilean, ws=None, **k):
        m = module.rsplit('.', 1)[-1]
        if m in fail:
            return False, 1.0, ['%s:1:0: error: drift' % path]
        open(olean, 'w').close()
        return True, secs[m], []
    return fake


def _times(path):
    import re
    return {m: float(t) for m, t in re.findall(r'Built (\S+) \(([\d.]+)s\)', open(path).read())}


def test_a_rebuild_keeps_the_replayed_modules_times(monkeypatch, tmp_path):
    ws = _port(tmp_path)
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 11.0, 'Main': 5.0}))
    assert code == 0 and _times(elab) == {'Solutions.F.A': 10.0, 'Solutions.F.Main': 4.0}
    main = os.path.join(ws, 'Solutions', 'F', 'Main.lean')
    os.utime(main, (os.path.getmtime(main) + 100,) * 2)           # the port rewrote Main only
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 99.0, 'Main': 7.0}))
    assert code == 0 and 'Replayed Solutions.F.A' in open(log).read()
    assert _times(elab) == {'Solutions.F.A': 10.0, 'Solutions.F.Main': 6.0}


def test_failed_rounds_keep_the_times_for_the_round_that_succeeds(monkeypatch, tmp_path):
    # repair rounds: each fails on another module and replays what the earlier ones built
    ws = _port(tmp_path)
    for _ in range(2):
        code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 11.0, 'Main': 5.0}, fail=('Main',)))
        assert code == 1
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 99.0, 'Main': 5.0}))
    assert code == 0 and _times(elab) == {'Solutions.F.A': 10.0, 'Solutions.F.Main': 4.0}
    # and an elab log from before this was kept (no build.log of a failed round) still serves
    os.remove(log)
    main = os.path.join(ws, 'Solutions', 'F', 'Main.lean')
    os.utime(main, (os.path.getmtime(main) + 100,) * 2)
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 99.0, 'Main': 3.0}))
    assert _times(elab) == {'Solutions.F.A': 10.0, 'Solutions.F.Main': 2.0}


def test_a_replayed_module_without_a_logged_time_takes_it_from_the_leaninfo_cache(monkeypatch, tmp_path):
    # the carves whose build_elab.log was already cut short: the compile cached LeanInfo's build_ms
    # beside the reading, so `--redo build` recovers every time
    from p2mlib import leaninfo
    monkeypatch.setattr(leaninfo, 'CACHE', str(tmp_path / 'cache'))
    ws = _port(tmp_path)
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 11.0, 'Main': 5.0}))
    os.remove(log)
    os.remove(elab)
    src = os.path.join(ws, 'Solutions', 'F', 'A.lean')
    key = leaninfo._key(src, False, ws, (), True, 'Solutions.F.A', True, leaninfo.BUILD_OPTIONS)
    os.makedirs(leaninfo.CACHE)
    open(os.path.join(leaninfo.CACHE, key + '.json'), 'w').write('{"build_ms": 8000}')
    main = os.path.join(ws, 'Solutions', 'F', 'Main.lean')
    os.utime(main, (os.path.getmtime(main) + 100,) * 2)
    code, log, elab = _run_main(monkeypatch, tmp_path, ws, _fake_build({'A': 99.0, 'Main': 3.0}))
    assert code == 0 and _times(elab) == {'Solutions.F.A': 7.0, 'Solutions.F.Main': 2.0}


def test_an_unchanged_port_replays_under_another_snapshot_and_leaninfo(monkeypatch, tmp_path):
    # oaiq-088 item 1: four skill-snapshot changes each rebuilt all 2,385 modules (`Built`, never
    # `Replayed`). The build's staleness reads nothing of the snapshot: a module is rebuilt when its .lean
    # is newer than its .olean or an import was rebuilt / has a newer .olean, and the port rewrites only
    # files whose text changed (oai_port_modules.write_changed). Every one of those rebuilds began with
    # `Built ...Compat`: each snapshot's lean/compat_4_34.lean differed, and every module imports Compat.
    import oai_port_modules as PM
    from p2mlib import leaninfo
    ws = tmp_path / 'ws'
    out = ws / 'Solutions' / 'F'
    files = {'Compat.lean': 'import Mathlib\n\nnamespace OAI\ntheorem c : True := trivial\nend OAI\n',
             'A.lean': 'import Mathlib\nimport Solutions.F.Compat\ntheorem a : True := trivial\n',
             'Main.lean': 'import Mathlib\nimport Solutions.F.Compat\nimport Solutions.F.A\ntheorem m : True := a\n'}
    assert sorted(PM.write_changed(str(out), files)) == ['A.lean', 'Compat.lean', 'Main.lean']
    built = []

    def fake(path, module, olean, ilean, ws=None, **k):
        built.append(module)
        open(olean, 'w').close()
        return True, 1.0, []
    clock = [1_000_000_000]

    def tick(p):
        clock[0] += 10
        os.utime(p, (clock[0], clock[0]))

    def build():
        built.clear()
        ok, lines = B.build(str(ws), 'F', 'Main')
        assert ok
        for f in ('Compat', 'A', 'Main'):
            o = ws / '.lake' / 'build' / 'lib' / 'lean' / 'Solutions' / 'F' / (f + '.olean')
            if ('Solutions.F.' + f) in built:
                tick(o)
        return lines
    for f in files:
        tick(out / f)
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    monkeypatch.setattr(leaninfo, 'native_tool', lambda ws: '/snapshot-1/leaninfo')
    build()
    assert built == ['Solutions.F.Compat', 'Solutions.F.A', 'Solutions.F.Main']
    # a new snapshot: another LeanInfo binary, the same ported text written again
    monkeypatch.setattr(leaninfo, 'native_tool', lambda ws: '/snapshot-2/leaninfo')
    monkeypatch.setattr(leaninfo, 'TOOL', str(tmp_path / 'OtherLeanInfo.lean'))
    assert PM.write_changed(str(out), files) == []
    lines = build()
    assert built == [] and all('Replayed' in l for l in lines)
    # the legitimate case (oaiq-095 item 3): a new compat shim rewrites Compat.lean, and everything rebuilds
    files['Compat.lean'] = files['Compat.lean'].replace('end OAI', 'theorem d : True := trivial\nend OAI')
    assert PM.write_changed(str(out), files) == ['Compat.lean']
    tick(out / 'Compat.lean')
    build()
    assert built == ['Solutions.F.Compat', 'Solutions.F.A', 'Solutions.F.Main']


# ---- transparency failures in one round (q128-finitistic-retry, 2026-10-30) -------------------------
# 15 modules of oaiq-023 failed only the "not type-correct under the `implicit` transparency level" check and
# built with module-scope `set_option backward.isDefEq.respectTransparency false`; since a failed module skips
# its importers, they surfaced over seven rounds (~3 h). A failed module whose errors carry that note is now
# compiled once more as a copy with the option (try_module.with_option); when the copy builds, its .olean
# stands in so the importers build this round, and the module is reported as needing a patch. The build
# still fails, and the stand-in never replays.

NOTE = ('%s:3:2: error: simp made no progress\n\nNote: The target expression is not type-correct under the '
        '`implicit` transparency level, which may have triggered the failure.')


def _chain(tmp_path):
    ws = tmp_path / 'ws'
    d = ws / 'Solutions' / 'F'
    d.mkdir(parents=True)
    (d / 'A.lean').write_text('import Mathlib\n\nnamespace OAI\ntheorem a : True := by simp\nend OAI\n')
    (d / 'B.lean').write_text('import Solutions.F.A\ntheorem b : True := OAI.a\n')
    (d / 'Main.lean').write_text('import Solutions.F.B\ntheorem m : True := b\n')
    return str(ws)


class _Lean:
    """`lake env lean ... -o OLEAN FILE` stub: builds when the option is in FILE (or `ok`), else fails."""
    def __init__(self, ok=False):
        self.calls, self.ok = [], ok

    def __call__(self, args, cwd=None, env=None, **k):
        import types
        import try_module as T
        text = open(args[-1]).read()
        self.calls.append((args, text))
        if self.ok or T.OPT in text:
            open(args[args.index('-o') + 1], 'w').write('substitute')
            open(args[args.index('-i') + 1], 'w').close()
            return types.SimpleNamespace(returncode=0, stdout='', stderr='')
        return types.SimpleNamespace(returncode=1, stdout='%s:3:2: error: still broken\n' % args[-1], stderr='')


def _leaninfo(note_for=('A',), fail=()):
    built = []

    def fake(path, module, olean, ilean, ws=None, **k):
        m = module.rsplit('.', 1)[-1]
        if m in note_for:
            return False, 1.0, [NOTE % path]
        if m in fail:
            return False, 1.0, ['%s:1:0: error: drift' % path]
        built.append(m)
        open(olean, 'w').close()
        return True, 1.0, []
    return fake, built


def test_a_transparency_failure_that_the_option_fixes_lets_its_importers_build(monkeypatch, tmp_path, capsys):
    from p2mlib import leaninfo
    import try_module as T
    ws = _chain(tmp_path)
    fake, built = _leaninfo()
    lean = _Lean()
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    monkeypatch.setattr(B.subprocess, 'run', lean)
    ok, lines = B.build(ws, 'F', 'Main')
    out = capsys.readouterr().out
    assert not ok                                          # the port text still needs the patch
    assert built == ['B', 'Main']                          # importers built this round
    args, text = lean.calls[0]
    olean = os.path.join(ws, '.lake', 'build', 'lib', 'lean', 'Solutions', 'F', 'A.olean')
    assert args[:3] == ['lake', 'env', 'lean'] and args[args.index('-o') + 1] == olean
    root = args[args.index('-R') + 1]
    assert args[-1] == os.path.join(root, 'Solutions', 'F', 'A.lean')       # the module's own name
    assert text == T.with_option(open(os.path.join(ws, 'Solutions', 'F', 'A.lean')).read())[0]
    assert not os.path.exists(args[-1])                    # the copy is temporary
    assert open(olean).read() == 'substitute'
    assert any('Solutions.F.A' in l and 'transparency option' in l for l in lines)
    assert not any('Built Solutions.F.A' in l for l in lines)
    last = out.rstrip().split('\n')[-1]
    assert 'Solutions.F.A' in last and 'needs a patch' in last
    assert open(os.path.join(ws, 'Solutions', 'F', 'A.lean')).read().count(T.OPT) == 0   # FILE untouched


def test_a_stand_in_olean_never_replays(monkeypatch, tmp_path):
    from p2mlib import leaninfo
    ws = _chain(tmp_path)
    fake, built = _leaninfo()
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    monkeypatch.setattr(B.subprocess, 'run', _Lean())
    B.build(ws, 'F', 'Main')
    ok, lines = B.build(ws, 'F', 'Main')                   # nothing patched: A is compiled again
    assert not ok and not any('Replayed Solutions.F.A' in l for l in lines)
    # patched: A builds for real, the mark goes, and its importers rebuild against it
    fake2, built2 = _leaninfo(note_for=())
    monkeypatch.setattr(leaninfo, 'build_module', fake2)
    ok, lines = B.build(ws, 'F', 'Main')
    assert ok and built2 == ['A', 'B', 'Main']
    ok, lines = B.build(ws, 'F', 'Main')
    assert ok and all('Replayed' in l for l in lines)


def test_no_option_copy_without_the_transparency_note(monkeypatch, tmp_path):
    from p2mlib import leaninfo
    ws = _chain(tmp_path)
    fake, built = _leaninfo(note_for=(), fail=('A',))
    lean = _Lean(ok=True)
    monkeypatch.setattr(leaninfo, 'build_module', fake)
    monkeypatch.setattr(B.subprocess, 'run', lean)
    ok, lines = B.build(ws, 'F', 'Main')
    assert not ok and lean.calls == [] and built == []


def test_a_module_the_option_does_not_fix_fails_as_before(monkeypatch, tmp_path, capsys):
    from p2mlib import leaninfo
    ws = _chain(tmp_path)
    fake, built = _leaninfo()
    monkeypatch.setattr(leaninfo, 'build_module', fake)

    def broken(args, **k):
        import types
        return types.SimpleNamespace(returncode=1, stdout='%s:4:2: error: still broken\n' % args[-1], stderr='')
    monkeypatch.setattr(B.subprocess, 'run', broken)
    ok, lines = B.build(ws, 'F', 'Main')
    out = capsys.readouterr().out
    assert not ok and built == []
    assert lines[0].startswith('✖ [1/3] FAILED Solutions.F.A') and 'not type-correct' in out
    assert any('Skipped Solutions.F.B' in l for l in lines)
    assert not os.path.exists(os.path.join(ws, '.lake', 'build', 'lib', 'lean', 'Solutions', 'F', 'A.olean'))


def test_the_lean_fallback_tries_the_option_too(monkeypatch, tmp_path):
    # without the compiled LeanInfo the errors come from `lean`'s output, the note on a later line
    from p2mlib import leaninfo
    import types
    import try_module as T
    ws = _chain(tmp_path)
    monkeypatch.setattr(leaninfo, 'build_module', lambda *a, **k: None)
    calls = []

    def run(args, **k):
        calls.append(args)
        text = open(args[-1]).read()
        if args[-1].endswith('A.lean') and T.OPT not in text:
            return types.SimpleNamespace(returncode=1, stdout=NOTE % args[-1], stderr='')
        open(args[args.index('-o') + 1], 'w').close()
        return types.SimpleNamespace(returncode=0, stdout='', stderr='')
    monkeypatch.setattr(B.subprocess, 'run', run)
    ok, lines = B.build(ws, 'F', 'Main')
    assert not ok and len(calls) == 4 and any('Built Solutions.F.Main' in l for l in lines)
