"""Load a mission's data (MISSION_DIR/mission.py) -- never through `import mission`.

`import mission` goes through Python's module cache, so a second mission in the same process is
silently the first one (submit_all waited forever on another mission's statement in the test
suite, 2026-10-02). This loads the file under a fresh module name each time."""
import importlib.util
import itertools
import os
import sys

_n = itertools.count()


def load(mdir):
    mdir = os.path.abspath(mdir)
    name = '_p2m_mission_%d' % next(_n)
    spec = importlib.util.spec_from_file_location(name, os.path.join(mdir, 'mission.py'))
    m = importlib.util.module_from_spec(spec)
    if mdir not in sys.path:            # mission.py may import its own helpers (prose.py, …)
        sys.path.insert(0, mdir)
    spec.loader.exec_module(m)
    return m
