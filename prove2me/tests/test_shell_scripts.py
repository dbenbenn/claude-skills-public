"""Every tracked *.sh in the skill is wrapped so bash parses the whole file before running any of it.
Bash reads a script incrementally, so an edit made while it runs executes garbage (2026-10-25:
plain_carve.sh edited under two live carves).  Required shape: the body in `main() { ...; }`, then
`main "$@"; exit`."""
import os
import re
import subprocess

import pytest

from conftest import SCRIPTS

SKILLS = os.path.dirname(os.path.dirname(os.path.dirname(SCRIPTS)))


def shell_scripts():
    out = subprocess.run(['git', '-C', SKILLS, 'ls-files', '*.sh'], capture_output=True, text=True).stdout.split()
    return [os.path.join(SKILLS, f) for f in out]


def problems(text):
    lines = [l for l in text.splitlines() if l.strip() and not l.lstrip().startswith('#')]
    if not lines or not re.match(r'^main\(\)\s*\{', lines[0]):
        return 'first command must open `main() {`'
    if lines[-1].strip() != 'main "$@"; exit' or lines[-2].strip() != '}':
        return 'last lines must be `}` then `main "$@"; exit`'
    return None


@pytest.mark.parametrize('path', shell_scripts() or [None])
def test_every_tracked_shell_script_is_wrapped(path):
    if path is None:
        pytest.skip('no tracked shell scripts')
    assert problems(open(path).read()) is None, path


def test_checker_accepts_wrapped_and_rejects_bare():
    good = '#!/usr/bin/env bash\n# usage\nmain() {\n  echo hi\n}\nmain "$@"; exit\n'
    assert problems(good) is None
    assert problems('#!/bin/bash\necho hi\n')
    assert problems('main() {\n echo\n}\nmain "$@"\n')            # no `; exit`: bash would read on
    assert problems('echo pre\nmain() {\n echo\n}\nmain "$@"; exit\n')
