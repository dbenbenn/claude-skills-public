#!/usr/bin/env python3
"""Folded into edge_audit.py (Phase 4.4): its SHARED section is this check, judged by Lean.

usage: edge_overlap.py SOLUTIONS_DIR   (= edge_audit.py --local SOLUTIONS_DIR)
"""
import os
import sys

if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    os.execv(sys.executable, [sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'edge_audit.py'),
                              '--local', sys.argv[1]])
