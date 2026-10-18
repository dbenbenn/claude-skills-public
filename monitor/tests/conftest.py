"""Shared test setup for the monitor skill: puts monitor.py and section.py on the path."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
