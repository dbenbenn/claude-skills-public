"""LeanInfo (lean/LeanInfo.lean) and its wrapper p2mlib.leaninfo.

Offline: the wrapper on recorded JSON (lean_fixtures/*.json). With P2M_LEAN=1: the tool itself
must reproduce the recordings exactly, and the cache must answer a second run."""
import json
import os

import pytest

from p2mlib import leaninfo as LI

FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean_fixtures')


def recorded(name, mode=''):
    data = json.load(open(os.path.join(FIX, name + mode + '.json')))
    return LI.parse(data, open(os.path.join(FIX, name + '.lean'), 'rb').read())


@pytest.fixture(scope='module')
def info():
    return recorded('Structure')


def test_primes_namespaces_private(info):
    names = {d.name for d in info.decls if not d.generated}
    assert {"A.foo'", 'A.s1', 'A.s2', 'A.viaIn', 'A.hidden', 'A.usesHidden', 'inSec1', 'inSec2',
            'f', 'f_zero', 'P', 'solution'} <= names
    assert info.decl('A.hidden').private and not info.decl('A.usesHidden').private


def test_ranges_include_doc_comment_and_attributes(info):
    assert info.slice(info.decl("A.foo'").start.byte, info.decl("A.foo'").end.byte).startswith('/-- doc -/')
    assert info.slice(info.decl('A.s1').start.byte, info.decl('A.s1').end.byte).startswith('@[simp] theorem s1')
    assert info.slice(info.decl('A.s2').start.byte, info.decl('A.s2').end.byte).startswith('@[simp]\ntheorem s2')
    assert info.commands[info.decl('A.s2').command].attrs == ['simp']


def test_open_in_is_one_command(info):
    c = info.commands[info.decl('A.viaIn').command]
    assert c.short_kind == 'in' and c.inner_kind.endswith('declaration') and c.names == ['A.viaIn']
    assert info.slice(c.start.byte, c.end.byte).startswith('open Nat in\ntheorem viaIn')


def test_comment_line_starting_theorem_is_not_a_declaration(info):
    docs = [c for c in info.commands if c.short_kind == 'moduleDoc'
            and 'theorem for balls' in info.slice(c.start.byte, c.end.byte)]
    assert len(docs) == 1 and docs[0].names == []
    assert not any(d.name in ('for', 'balls') for d in info.decls)


def test_section_and_variable_are_their_own_commands(info):
    # the FAmenChild B2 case: a `section … variable … end` spanning declarations
    kinds = [c.short_kind for c in info.commands]
    i = kinds.index('section')
    assert kinds[i:i + 5] == ['section', 'variable', 'declaration', 'declaration', 'end']
    assert info.commands[i + 2].names == ['inSec1'] and info.commands[i + 3].names == ['inSec2']


def test_dependencies_fold_auxiliaries(info):
    assert info.decl('f').uses_local == []                      # f.match_1 folded away
    assert info.decl('f_zero').uses_local == ['f']
    assert info.decl('A.usesHidden').uses_local == ['A.hidden']
    assert info.decl('solution').uses_local == ["A.foo'", 'f', 'f_zero']


def test_dependencies_include_names_the_source_resolves(info):
    # simp rewrites by an rfl lemma through dsimp, leaving no trace in the term; the pruner deleted
    # Moore's bits_001 / bits_01 / bits_10 that way (2026-10-02) and the solution stopped compiling
    assert info.decl('viaSimp').uses_local == ['f', 'f_one']


def test_value_start_is_the_assignment(info):
    # rewire keeps a copy's header up to here and replaces the rest
    for name in ("A.foo'", 'viaLemma', 'A.viaIn', 'f'):
        c = info.commands[info.decl(name).command]
        assert info.slice(c.value_start.byte, c.value_start.byte + 2) == ':='
    assert info.commands[info.decl('P').command].value_start is None


def test_generated_constants_flagged(info):
    gen = {d.name for d in info.decls if d.generated}
    assert {'P.rec', 'P.casesOn', 'P.mk', 'P.a'} <= gen and 'P' not in gen
    assert info.decl('instInhabitedP').command == \
        [c.index for c in info.commands if info.slice(c.start.byte, c.end.byte).startswith('instance')][0]


def test_command_spans_tile_the_file(info):
    spans = [info.command_span(i) for i in range(len(info.commands))]
    text = info.text_bytes.decode('utf-8')
    head = text[:info.commands[0].start.byte]                      # `import Mathlib` header
    assert head + ''.join(info.slice(a, b) for a, b in spans) == text


def test_unknown_identifiers():
    assert recorded('Broken').unknown_identifiers() == ['nonexistent_lemma']


def test_parse_only_agrees_on_commands():
    a, b = recorded('Structure'), recorded('Structure', '.parse')
    assert [(c.kind, c.names, c.start.byte) for c in a.commands] == [(c.kind, c.names, c.start.byte) for c in b.commands]
    assert b.decls == []


@pytest.mark.lean
@pytest.mark.parametrize('name,parse_only', [(n, p) for n in ('Structure', 'Broken', 'Notation', 'Rewire') for p in (False, True)])
def test_tool_reproduces_recording(name, parse_only):
    info = LI.run(os.path.join(FIX, name + '.lean'), parse_only=parse_only, use_cache=False)
    want = recorded(name, '.parse' if parse_only else '')
    for x in (info, want):
        x.path = os.path.basename(x.path)
    assert info == want


@pytest.mark.lean
def test_cache_answers_second_run(monkeypatch, tmp_path):
    monkeypatch.setattr(LI, 'CACHE', str(tmp_path))
    f = os.path.join(FIX, 'Broken.lean')
    first = LI.run(f)

    def boom(*a, **k):
        raise AssertionError('Lean was run although the cache had the answer')
    monkeypatch.setattr(LI.subprocess, 'run', boom)
    assert LI.run(f) == first


def test_parse_only_knows_scoped_and_in_file_notation():
    # FAmenChild PartB2: `ℝ≥0∞` parses only after `open scoped ENNReal` is elaborated
    p = recorded('Notation', '.parse')
    assert p.errors == [] and [n for c in p.commands for n in c.names] == ['g', 'g_le', 'n1']
    e = recorded('Notation')
    assert {d.name for d in e.decls if not d.generated} == {'g', 'g_le', 'n1'}


def test_cache_key_changes_when_an_import_is_built(tmp_path):
    # markov-heat-kernels 2026-10-04: a stub whose .lean existed but was not yet built made the
    # first run fail; the key hashed only the .lean, so after `lake build` the failure was served
    # from the cache. The built .olean is part of the key.
    ws = tmp_path / 'ws'
    (ws / 'Theorems').mkdir(parents=True)
    (ws / 'Theorems' / 'Stub.lean').write_text('theorem t : True := trivial\n')
    f = ws / 'Use.lean'
    f.write_text('import Theorems.Stub\n')
    before = LI._key(str(f), False, str(ws))
    olean = ws / '.lake' / 'build' / 'lib' / 'lean' / 'Theorems' / 'Stub.olean'
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b'built')
    assert LI._key(str(f), False, str(ws)) != before


def test_cache_key_changes_when_a_candidate_is_built(tmp_path):
    # Artin 2026-10-09: copies.find imports every published statement as a candidate; one
    # published minutes earlier had no .olean yet, the run failed with "object file ... does not
    # exist", and the key (built-ness of the file's own imports only) kept serving that failure
    # after `lake build`. Candidates' built state is part of the key too.
    ws = tmp_path / 'ws'
    (ws / 'Theorems').mkdir(parents=True)
    (ws / 'Theorems' / 'Cand.lean').write_text('theorem c : True := trivial\n')
    f = ws / 'Use.lean'
    f.write_text('theorem u : True := trivial\n')
    before = LI._key(str(f), False, str(ws), candidates=['Theorems.Cand'])
    olean = ws / '.lake' / 'build' / 'lib' / 'lean' / 'Theorems' / 'Cand.olean'
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b'built')
    assert LI._key(str(f), False, str(ws), candidates=['Theorems.Cand']) != before


# ---- the native build of LeanInfo (2026-10-27) -------------------------------------------------
# `lean --run LeanInfo.lean` re-elaborated the tool and interpreted it on every module: +3 s and
# ~2 GB per call. The compiled tool printed byte-identical JSON at 19-44% less CPU.

class _Done:
    def __init__(self, rc=0, out=''):
        self.returncode, self.stdout, self.stderr = rc, out, ''


def _ws(tmp_path, toolchain='leanprover/lean4:v4.33.1\n'):
    ws = tmp_path / 'ws'
    ws.mkdir(exist_ok=True)
    (ws / 'lean-toolchain').write_text(toolchain)
    return str(ws)


def test_raw_runs_the_native_tool_when_there_is_one(monkeypatch, tmp_path):
    seen = []
    monkeypatch.setattr(LI, 'native_tool', lambda ws: '/bin/leaninfo')
    monkeypatch.setattr(LI.subprocess, 'run', lambda args, **k: seen.append(args) or _Done(out='{"x": 1}'))
    f = tmp_path / 'F.lean'
    f.write_text('')
    assert LI.raw(str(f), ws=_ws(tmp_path), idents=True) == {'x': 1}
    assert seen[0][:4] == ['lake', 'env', '/bin/leaninfo', str(f)] and '--run' not in seen[0]
    assert '--idents' in seen[0]


def test_raw_falls_back_to_lean_run(monkeypatch, tmp_path):
    seen = []
    monkeypatch.setattr(LI, 'native_tool', lambda ws: None)
    monkeypatch.setattr(LI.subprocess, 'run', lambda args, **k: seen.append(args) or _Done(out='{"x": 1}'))
    f = tmp_path / 'F.lean'
    f.write_text('')
    LI.raw(str(f), ws=_ws(tmp_path))
    assert seen[0][:5] == ['lake', 'env', 'lean', '--run', LI.TOOL]


def test_native_tool_builds_once_and_reuses(monkeypatch, tmp_path):
    monkeypatch.setattr(LI, 'BIN_CACHE', str(tmp_path / 'bin'))
    monkeypatch.delenv('P2M_LEANINFO_INTERPRETED', raising=False)
    builds = []

    def fake_build(args, cwd=None, **k):
        builds.append(cwd)
        exe = os.path.join(cwd, '.lake', 'build', 'bin', 'leaninfo')
        os.makedirs(os.path.dirname(exe))
        open(exe, 'w').close()
        os.chmod(exe, 0o755)
        return _Done()
    monkeypatch.setattr(LI.subprocess, 'run', fake_build)
    ws = _ws(tmp_path)
    exe = LI.native_tool(ws)
    assert exe and os.access(exe, os.X_OK) and len(builds) == 1
    assert open(os.path.join(builds[0], 'LeanInfo.lean'), 'rb').read() == open(LI.TOOL, 'rb').read()
    assert open(os.path.join(builds[0], 'lean-toolchain')).read() == 'leanprover/lean4:v4.33.1\n'
    assert LI.native_tool(ws) == exe and len(builds) == 1


def test_native_tool_depends_on_the_toolchain(monkeypatch, tmp_path):
    monkeypatch.setattr(LI, 'BIN_CACHE', str(tmp_path / 'bin'))
    a = LI.native_dir(_ws(tmp_path, 'leanprover/lean4:v4.33.1\n'))
    b = LI.native_dir(_ws(tmp_path, 'leanprover/lean4:v4.34.0\n'))
    assert a != b


def test_failed_native_build_is_remembered(monkeypatch, tmp_path):
    monkeypatch.setattr(LI, 'BIN_CACHE', str(tmp_path / 'bin'))
    monkeypatch.delenv('P2M_LEANINFO_INTERPRETED', raising=False)
    monkeypatch.setattr(LI.subprocess, 'run', lambda *a, **k: _Done(rc=1, out='error: boom'))
    ws = _ws(tmp_path)
    assert LI.native_tool(ws) is None

    def boom(*a, **k):
        raise AssertionError('a failed build is retried on every call')
    monkeypatch.setattr(LI.subprocess, 'run', boom)
    assert LI.native_tool(ws) is None
    assert 'boom' in open(os.path.join(LI.native_dir(ws), 'FAILED')).read()


def test_interpreted_switch(monkeypatch, tmp_path):
    monkeypatch.setenv('P2M_LEANINFO_INTERPRETED', '1')
    monkeypatch.setattr(LI.subprocess, 'run', lambda *a, **k: (_ for _ in ()).throw(AssertionError('built')))
    assert LI.native_tool(_ws(tmp_path)) is None
