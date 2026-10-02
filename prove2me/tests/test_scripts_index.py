"""Phase 6: every script documents itself, and SKILL.md's index is generated from those docs."""
import ast
import os
import subprocess
import sys

import pytest

from conftest import SCRIPTS

import gen_index


@pytest.mark.parametrize('name,first,runnable,doc', gen_index.scripts(), ids=lambda x: x if isinstance(x, str) and x.endswith('.py') else '')
def test_script_documents_itself(name, first, runnable, doc):
    assert first, '%s has no docstring' % name
    if runnable:
        assert 'usage:' in doc.lower(), '%s runs as a script but its docstring has no `usage:` line' % name


def test_skill_index_is_current():
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'gen_index.py'), '--check'],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
