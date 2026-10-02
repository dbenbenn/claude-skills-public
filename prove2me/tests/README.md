# Tests for the prove2me scripts

```
python3 -m pytest -q tests                  # unit + regression: seconds, no Lean, no network
P2M_LEAN=1 python3 -m pytest -q tests       # + golden pipeline rebuilds in the Lean workspace (~20 s)
P2M_LIVE=1 python3 -m pytest -q tests       # + live read-only API contract (also run by scripts/sync_workspace.py)
```

- **Every bug fix gets a test that fails on the pre-fix version.** Check it with `git show <fix>^:prove2me/scripts/<script>`.
- **Golden cases** live in `golden/<case>/`: `src/`, `expected.lean` (the ACCEPTED submission,
  fetched once) and `meta.json`.
  - A case marked `xfail` is one the pipeline cannot yet produce. The xfail is strict, so the test
    says when it starts passing.
- **No live write tests** (dbenbenn, 2026-10-02).
