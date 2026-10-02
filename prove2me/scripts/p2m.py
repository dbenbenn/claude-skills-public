#!/usr/bin/env python3
"""The prove2.me API client -- now p2mlib.api; this module re-exports it for the scripts.

usage: p2m.py METHOD PATH [JSON_BODY]     (prints the response)
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # p2mlib
from p2mlib.api import call, token, no_frozen_comments as _no_docstring  # noqa: E402,F401
from p2mlib.workspace import workspace as _workspace  # noqa: E402,F401

if __name__ == '__main__':
    m, p = sys.argv[1], sys.argv[2]
    b = json.loads(sys.argv[3]) if len(sys.argv) > 3 else None
    print(json.dumps(call(m, p, b), indent=1))
