"""Shared core for the prove2me scripts (scripts/README.md).

One implementation per concept: Lean structure comes from `leaninfo` (Lean itself), never from
regular expressions over Lean source."""

import os as _os

LEAN_CAP = _os.path.expanduser('~/claude/claude-private/tools/lean-cap')


def lean_cap_first(env=None, cap=LEAN_CAP):
    """Put the box-wide Lean cap's `lake`/`lean` wrappers first on `env`'s PATH (default: this
    process's), so every subprocess these scripts start queues for one of its 3 slots. A shell
    started before the cap existed resolves `lake` to elan's and bypasses it (2026-10-09)."""
    env = _os.environ if env is None else env
    path = env.get('PATH', '')
    if _os.path.isdir(cap) and path.split(_os.pathsep)[0] != cap:
        env['PATH'] = cap + _os.pathsep + path


lean_cap_first()
