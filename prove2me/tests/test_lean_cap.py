"""p2mlib.lean_cap_first: every script that imports p2mlib runs `lake`/`lean` through the box-wide
Lean cap, even from a shell whose PATH predates it (2026-10-09: such shells resolved `lake` to
elan's and bypassed the 3-slot queue)."""
import os

import p2mlib


def test_puts_the_cap_first(tmp_path):
    cap = tmp_path / 'lean-cap'
    cap.mkdir()
    env = {'PATH': '/home/u/.elan/bin:/usr/bin'}
    p2mlib.lean_cap_first(env, str(cap))
    assert env['PATH'].split(os.pathsep)[0] == str(cap)


def test_is_idempotent_and_leaves_a_missing_cap_alone(tmp_path):
    cap = tmp_path / 'lean-cap'
    cap.mkdir()
    env = {'PATH': str(cap) + os.pathsep + '/usr/bin'}
    p2mlib.lean_cap_first(env, str(cap))
    assert env['PATH'] == str(cap) + os.pathsep + '/usr/bin'
    env2 = {'PATH': '/usr/bin'}
    p2mlib.lean_cap_first(env2, str(tmp_path / 'absent'))
    assert env2['PATH'] == '/usr/bin'


def test_p2m_lean_cap_names_the_cap_and_empty_turns_it_off(tmp_path):
    # the same switch carvepipeline.env() reads; the pipeline tests set it empty to reach their stub lake
    cap = tmp_path / 'other-cap'
    cap.mkdir()
    env = {'PATH': '/usr/bin', 'P2M_LEAN_CAP': str(cap)}
    p2mlib.lean_cap_first(env)
    assert env['PATH'].split(os.pathsep)[0] == str(cap)
    env = {'PATH': '/stub/bin:/usr/bin', 'P2M_LEAN_CAP': ''}
    p2mlib.lean_cap_first(env)
    assert env['PATH'] == '/stub/bin:/usr/bin'
