"""p2mlib.verdicts: what a prove2.me verdict or publish result means, and what to do next.

Golden messages are the platform's own texts, collected during the Erdős 3 split (2026-10-08..16),
where treating every ERROR as transient retried one piece 740 times."""
import pytest

from p2mlib import verdicts as V

CASES = [
    # (status, error_message, kind)
    ('ACCEPTED', None, 'accepted'),
    ('SKETCH_ACCEPTED', None, 'accepted'),
    ('ERROR', "Failed to materialize the target's dependencies: Module compilation timed out after 300s.", 'transient'),
    ('ERROR', "Failed to resolve platform imports: DB error looking up import 'Definitions.Def_OAIErdos3B010': "
              "<ConnectionTerminated error_code:0, last_stream_id:19999, additional_data:None>", 'transient'),
    ('ERROR', 'Verification timed out after 300s', 'own_timeout'),
    ('ERROR', 'Verification timed out after 300s. Try breaking the statement or proof into smaller lemmas or '
              'definitions and checking each piece separately before retrying.', 'own_timeout'),
    ('ERROR', 'Failed to compile solution module: Module compilation timed out after 300s', 'own_timeout'),
    ('CE', 'Compile error in your proof:\nline 3018: Unknown constant `OAI.Erdos3.X`', 'compile_error'),
    ('WA', 'Your proof does not match the target type:\nexpected token\nUnknown identifier `X`\nUnknown constant `_check`',
     'wrong'),
    # publish (definitions bundle / statement) results
    ('ERROR', 'Internal error while publishing: Module compilation timed out after 300s. Try breaking the statement '
              'or proof into smaller lemmas or definitions and checking each piece separately before retrying.', 'transient'),
    ('FAILED', 'Compilation timed out after 300s', 'own_timeout'),
    ('FAILED', 'definition does not compile: Import parser timed out after 5s', 'transient'),
    # oaiq-089: the platform's lexer timing out on small statements under load; a reset republished all nine
    ('FAILED', 'formal statement does not compile: could not lex the submitted code: Token scanner timed out after 10s',
     'transient'),
    # a lex failure that is not a timeout is the file's
    ('FAILED', 'formal statement does not compile: could not lex the submitted code: unterminated comment', 'compile_error'),
    ('FAILED', "definition does not compile: DB error looking up import 'Definitions.Def_OAIErdos3B133': "
               '<ConnectionTerminated error_code:0>', 'transient'),
    ('FAILED', 'definition does not compile: line 3001: (deterministic) timeout at `whnf`, maximum number of '
               'heartbeats (200000) has been reached', 'heartbeats'),
    ('FAILED', 'formal statement does not compile: line 199: failed to synthesize instance of type class', 'compile_error'),
    # Eilenberg–Ganea (2026-10-25): the worker's build of the imported bundles was OOM-killed (many
    # decide-heavy bundles built in parallel); unchanged retries failed the same way
    ('FAILED', 'definition does not compile: Failed to compile modules Definitions.Def_EilenbergGanea, '
               'Definitions.Def_OAIEG012: \u2714 [8717/8725] Built Definitions.Def_OAIEG006 (28s)\n'
               '\u2716 [8718/8725] Building Definitions.Def_OAIEG012 (44s)\nerror: Lean exited with code 137\n'
               'error: build failed', 'dependency_oom'),
    # q153 PlanarPacking (2026-11-06): the solution's build output, cut at about 4 KB inside the replay
    # warnings of imported statement stubs; the cause is not shown, and it is not a timeout
    ('ERROR', 'Failed to compile solution module: Failed to compile module Submissions.Job_9eeafbcf_Sol: '
              '\u26a0 [8709/8785] Replayed Theorems.Thm_OAI_SharpPlanar_Scoords_add_e\nwarning: '
              'Theorems/Thm_OAI_SharpPlanar_Scoords_add_e.lean:18:6: declaration uses `sorry`\n'
              '\u26a0 [8710/8785] Replayed Theorems.Thm_OAI_SharpPlanar_Scoords_mem_e\nwarning', 'hidden'),
    # the same output, with the error inside what is shown, is the file's
    ('ERROR', 'Failed to compile solution module: Failed to compile module Submissions.Job_X_Sol: '
              '\u26a0 [1/2] Replayed Theorems.Thm_A\nwarning: Theorems/Thm_A.lean:3:6: declaration uses `sorry`\n'
              'error: Sol.lean:12:4: unknown identifier `foo`\nerror: build failed', 'compile_error'),
    # q153 (2026-11-06): the solution's own build OOM-killed (a 586 MB import closure): retried, not a compile error
    ('ERROR', 'Failed to compile solution module: Failed to compile module Submissions.Job_d825_Sol: \u26a0 [8709/8844] '
              'Replayed Theorems.Thm_A\nwarning: Theorems/Thm_A.lean:15:6: declaration uses `sorry`\n'
              '\u2716 [8844/8844] Building Submissions.Job_d825_Sol (138s)\nerror: Lean exited with code 137\n'
              'Some required targets logged failures:\nerror: build failed', 'dependency_oom'),
    ('PUBLISHED', None, 'accepted'),
    (None, '<urlopen error [Errno -3] Temporary failure in name resolution>', 'transient'),
]


@pytest.mark.parametrize('status,msg,kind', CASES)
def test_classify(status, msg, kind):
    assert V.classify(status, msg) == kind


def test_decide_retries_transient_up_to_a_cap():
    assert V.decide('transient', {'transient': 3}) == 'retry'
    assert V.decide('transient', {'transient': V.TRANSIENT_CAP}) == 'give_up'


def test_decide_splits_after_two_own_timeouts():
    assert V.decide('own_timeout', {'own_timeout': 1}) == 'retry'
    assert V.decide('own_timeout', {'own_timeout': V.OWN_TIMEOUT_CAP}) == 'split'


def test_decide_never_retries_a_wrong_or_broken_proof():
    for k in ('compile_error', 'wrong', 'refused'):
        assert V.decide(k, {}) == 'stop'
    assert V.decide('accepted', {}) == 'done'
    assert V.decide('heartbeats', {}) == 'raise_heartbeats'


def test_decide_retries_a_hidden_cause_then_stops():
    assert V.decide('hidden', {}) == 'retry'
    assert V.decide('hidden', {'hidden': V.HIDDEN_CAP}) == 'stop'


def test_decide_retries_dependency_oom_a_few_times():
    # q152 (PlanarPacking, 2026-11-02): 30 bundles stopped on their first dependency_oom while siblings with
    # the same import closure (1,175 s, 1,246 s, 1,444 s of local compile) published: what the worker builds
    # in parallel decides it, so a few unchanged retries are worth it; then a person moves the heavy proofs
    assert V.decide('dependency_oom', {}) == 'retry'
    assert V.decide('dependency_oom', {'dependency_oom': V.DEPENDENCY_OOM_CAP - 1}) == 'retry'
    assert V.decide('dependency_oom', {'dependency_oom': V.DEPENDENCY_OOM_CAP}) == 'stop'
