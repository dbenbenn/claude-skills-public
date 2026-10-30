"""scripts/try_module.py: one ported module compiled as is and with the transparency option (oaiq-116),
the compiler stubbed (no Lean)."""
import os
import types

import try_module as T

SRC = ('import Mathlib\nimport Solutions.F.A\n\n/-! The module. -/\n\nset_option linter.unusedVariables false\n\n'
       'namespace OAI\n\ntheorem a : True := trivial\n\ntheorem b : True := by\n  simp\n\nend OAI\n')


def test_the_option_goes_at_module_scope_right_after_the_header():
    # a `set_option` inside `namespace OAI` ends with it (references/openai-ports.md)
    text, at = T.with_option(SRC)
    lines = text.split('\n')
    assert lines[at - 1] == T.OPT and at == 3
    assert lines.index(T.OPT) < lines.index('namespace OAI')
    assert text.replace(T.OPT + '\n', '', 1) == SRC
    assert T.with_option(text) == (text, None)                   # already there: nothing added
    assert T.with_option('theorem t : True := trivial\n')[0].startswith(T.OPT + '\n')


def test_errors_are_split_per_message_and_warnings_and_cap_lines_ignored():
    log = ('lean-cap: all 6 Lean slots busy; queued (priority 5)\n'
           '/w/F.lean:12:2: error: simp made no progress\n  ⊢ x = y\n'
           '/w/F.lean:13:0: warning: unused variable\n'
           '/w/F.lean:20:4: error(lean.unknownIdentifier): Unknown identifier `z`\n')
    errs = T.errors(log)
    assert [(e[0], e[1].split('\n')[0]) for e in errs] == [
        (12, '/w/F.lean:12:2: error: simp made no progress'),
        (20, '/w/F.lean:20:4: error(lean.unknownIdentifier): Unknown identifier `z`')]
    assert '⊢ x = y' in errs[0][1]


def test_both_versions_compile_with_the_pipeline_flags_through_the_cap(tmp_path, monkeypatch, capsys):
    ws = tmp_path / 'ws'
    ws.mkdir()
    cap = tmp_path / 'cap'
    cap.mkdir()
    f = tmp_path / 'F.lean'
    f.write_text(SRC)
    monkeypatch.setenv('P2M_LEAN_CAP', str(cap))
    calls = []

    def run(cmd, cwd=None, env=None, **k):
        calls.append((cmd, cwd, env['PATH'].split(os.pathsep)[0], open(cmd[-1]).read()))
        opt = T.OPT in open(cmd[-1]).read()
        # as is: two transparency errors; with the option (one line lower): one error at `b`
        out = ('%s:13:2: error: rewrite failed\n' % cmd[-1]) if opt else \
            ('%s:10:0: error: not type-correct\n%s:12:2: error: simp made no progress\n' % (cmd[-1], cmd[-1]))
        return types.SimpleNamespace(returncode=1, stdout=out, stderr='')
    res = T.try_module(str(f), ws=str(ws), run=run)
    assert [c[0][:5] for c in calls] == [['lake', 'env', 'lean', '-j1', '-DautoImplicit=false']] * 2
    assert all(c[1] == str(ws) and c[2] == str(cap) for c in calls)
    assert calls[0][3] == SRC and T.OPT in calls[1][3]
    assert [e[0] for e in res['as is']] == [10, 12]
    assert [e[0] for e in res['with option']] == [12]          # mapped back to FILE's own lines
    assert res['fewer'] == 'with option'
    assert f.read_text() == SRC                                # FILE itself untouched
    out = capsys.readouterr().out
    assert 'as is: 2 errors' in out and 'with the option: 1 error' in out


def test_show_prints_the_full_message_of_the_named_lines(tmp_path, monkeypatch, capsys):
    f = tmp_path / 'F.lean'
    f.write_text(SRC)
    monkeypatch.setenv('P2M_LEAN_CAP', '')

    def run(cmd, cwd=None, env=None, **k):
        return types.SimpleNamespace(returncode=1, stdout='%s:12:2: error: simp made no progress\n  ⊢ goal\n' % cmd[-1],
                                     stderr='')
    res = T.try_module(str(f), ws=str(tmp_path), run=run, show={12})
    out = capsys.readouterr().out
    assert '⊢ goal' in out and 'line 12 of FILE' in out
    assert res['fewer'] == 'tie' and 'the same number of errors' in out
