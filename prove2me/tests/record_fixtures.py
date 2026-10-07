#!/usr/bin/env python3
"""Re-record lean_fixtures/<Name>.json and <Name>.parse.json from the current LeanInfo.

usage: python3 tests/record_fixtures.py [NAME ...]   (default: every fixture test_leaninfo replays)

Run after changing lean/LeanInfo.lean, then read `git diff tests/lean_fixtures`: the diff is the
change in what the tool reports, and test_tool_reproduces_recording pins it."""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import leaninfo  # noqa: E402

FIX = os.path.join(HERE, 'lean_fixtures')
REPLAYED = ['Structure', 'Broken', 'Notation', 'Rewire', 'Audit', 'Scope', 'Alias', 'Variable', 'ScopedVariable']


def record(name):
    for parse_only, suffix in ((False, ''), (True, '.parse')):
        path = os.path.join(FIX, name + '.lean')
        data = leaninfo.raw(path, parse_only=parse_only)
        data['file'] = name + '.lean'
        with open(os.path.join(FIX, name + suffix + '.json'), 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=1, sort_keys=True)
        print('recorded', name + suffix)


if __name__ == '__main__':
    for n in sys.argv[1:] or REPLAYED:
        record(n)
