"""sync_workspace.py's lessons-inbox line: untriaged lessons from the headless workers are counted
at every session start, so the main agent notices them without being asked."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
import sync_workspace  # noqa: E402


def test_inbox_missing_dir_says_nothing(tmp_path):
    assert sync_workspace.inbox_line(str(tmp_path / 'absent')) is None


def test_inbox_empty_says_nothing(tmp_path):
    (tmp_path / 'README.md').write_text('how the inbox works')
    assert sync_workspace.inbox_line(str(tmp_path)) is None


def test_inbox_counts_lessons_not_readme(tmp_path):
    (tmp_path / 'README.md').write_text('how the inbox works')
    (tmp_path / 'oaiq-010-tensor-drift.md').write_text('x')
    (tmp_path / 'oaiq-011-heartbeats.md').write_text('y')
    (tmp_path / 'notes.txt').write_text('not a lesson')
    line = sync_workspace.inbox_line(str(tmp_path))
    assert line.startswith('lessons inbox: 2 untriaged')
    assert str(tmp_path) in line
