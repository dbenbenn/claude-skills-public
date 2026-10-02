# Engineering pass on the prove2me scripts — plan (draft, 2026-10-02)

## Why

**Size and bug history.** There are 27 scripts and about 4,800 lines of Python. About 45 of the 111
commits touching `scripts/` are bug fixes, and the same bug classes recur:

| Bug class | Recent instances |
|---|---|
| Primed names | `\b` matched `isMarginal_EBad` inside `isMarginal_EBad'`, building `theorem solution'` (2026-10-02); rewire's prime stripping |
| Command boundaries | `open X in` copied as `open X in in`; a check block swallowing the next block's `open X in` |
| Namespace and `open` tracking | `end` matching, scoped opens, `solution` inside a namespace |
| Comments and docstrings | a docstring line beginning "open" became an `open` command; `/-! -/` attachment; `--` inside strings |
| Escaping | `\"` leaking into raw-string prose; LaTeX backslashes in Python literals; JSON |
| Platform API | pagination at 50 vs 100 (silently truncated lists); a poll timeout reported as a rejection; the false belief that the platform never serves submitted code |

**Root cause: duplicated reimplementation.**

| What | Separate copies |
|---|---|
| Lean declaration heads (regexes) | 8 scripts |
| Namespace/`end` stacks | 8 scripts |
| Comment stripping | 3 versions |
| `_workspace()` | 3 copies |
| `published()` | 2 copies |

A fix in one copy leaves the others broken. There are no tests, so a fix is only checked on the
case that triggered it.

**Undocumented scripts.** `watch_proposal.py` and `submit_all.py` were not mentioned in SKILL.md,
so they went unused.

## Principles

1. **Ask Lean, don't regex Lean.** A spike (below) shows that a small Lean program can elaborate a
   file and report everything the scripts currently guess:
   - every command, with its exact range;
   - every declaration's full name (primes, namespaces) and its range, including the doc comment;
   - each declaration's exact dependencies (constants used by its elaborated type and value).

   Text manipulation of Lean source is then limited to cutting at ranges Lean reported.
2. **One implementation per concept**, in a shared core package. Scripts become thin CLIs.
3. **Tests first.**
   - Every past bug becomes a regression test.
   - Refactors happen under characterization tests, so behaviour changes only on purpose.
4. **No prose in Python string literals.**
   - Store prose as Markdown files, read verbatim, with no escaping layer.
   - Build JSON only with `json.dumps`.
5. **One API layer.** It owns pagination, polling semantics (PENDING is not failure) and retries.
6. **Documentation is checked.**
   - Every script has a docstring with usage.
   - SKILL.md's scripts index is generated from those docstrings.
   - A test fails if a script is undocumented.

## The spike (done, 2026-10-02)

`lake env lean --run Decls.lean Target.lean`, an `unsafe def main` that calls
`enableInitializersExecution`, `processHeader` and `IO.processCommands`. On a test file it reports:

```
CMD Lean.Parser.Command.in 8-9          -- `open Nat in` + theorem: one command
DECL Foo.bar' lines 5-6 uses []         -- range includes the docstring
DECL solution lines 13-13 uses [Foo.bar']
```

It takes about 5 s including the Mathlib import. It has two limits:
- **It needs a compiling file.** A syntax-only mode is needed for files that do not elaborate yet:
  run `Lean.Parser` alone, which still gives command ranges and declaration names.
- **Macros and notation are syntax, not constants.** A declaration that only defines notation is
  kept when anything in the file uses that notation, conservatively.

## Architecture

```
prove2me/
  lean/LeanInfo.lean      # elaborate (or only parse) a file -> JSON: commands, decls, deps, opens
  p2mlib/
    api.py                # client, token refresh, paginate(), poll() with PENDING, retries
    workspace.py          # paths, Theorems/Definitions lookup, published() index
    leaninfo.py           # runs LeanInfo, caches by file hash, typed results
    names.py              # full/short/primed name handling, in one place
    leanedit.py           # cut/insert/replace by Lean-reported ranges; merge of modules
    prose.py              # Markdown prose loading; KaTeX/GitHub-math checks
    mission.py            # load mission data (old mission.py and new prose/ layout)
  scripts/*.py            # thin CLIs over p2mlib, one argparse convention, --go = act
  tests/                  # pytest; fixtures/ synthetic Lean files + recorded API responses
```

## Phases

Each phase ends with all tests passing and a commit. A real mission run (re-building Moore's 31
solutions, `edge_audit` on the F-amenability mission, `draft.py verify` on Lodha–Moore) must
reproduce today's results, apart from deliberate fixes.

**Phase 0: inventory (½ session).**
- One row per script: purpose, inputs and outputs, callers, SKILL.md mention, bug history, verdict
  (keep / merge / retire).
- Known candidates:
  - `build_solution.py` vs `build_solutions.py`;
  - `edge_overlap.py` vs an `edge_audit.py` built on dependencies;
  - `submit_verify.py` folded into the API layer.
- Deliverable: `scripts/README.md`.

**Phase 1: test harness and regression corpus (1 session).**
- pytest. Fixtures are **synthetic** Lean files and recorded API JSON. The repo is public, so
  nothing comes from private missions.
- One test per past bug class above, taken from the fix commits.
- Characterization tests for the current outputs of `prune`, `rewire`, `merge`,
  `build_solutions`, `assemble_blueprint`, `extract_payloads` and the checkers.
- A mock API serving paginated lists and PENDING-then-final verdicts.

**Phase 2: LeanInfo, the Lean side (1 session).**
- The spike made robust:
  - JSON output;
  - elaborate mode and parse-only mode;
  - the `open`/namespace context at each command;
  - each declaration's type, so copies of published theorems can be found by **type**, not by
    name (this also catches renamed copies, which `edge_overlap.py` only approximates);
  - caching.
- Tests: Lean fixtures with expected JSON.

**Phase 3: core library (1 session).**
- `api`, `workspace`, `names`, `leaninfo`, `leanedit`, each with unit tests.
- The duplicated helpers are deleted as their callers move over in Phase 4.

**Phase 4: migrate scripts (1–2 sessions).** In dependency order:
1. `prune_solution`: reachability over LeanInfo dependencies.
2. `rewire`: copies found by type equality against published statements.
3. `merge`, `build_solutions`, `assemble_blueprint`: ranges, not regexes.
4. `edge_audit`, `edge_overlap`: one tool.
5. `submit_*`, `publish_*`, `deprecate`, `watch_*`, `fetch_theorems`: all through `p2mlib.api`.
6. `draft`, `stage_auditor`, `source_audit`, `caveat_audit`, `decisions`: the large ones, last.

Each migration lands with its tests.

**Phase 5: prose and data format (½–1 session).**
- New missions keep prose as `prose/<item>.md` with front matter (title, page, result).
- `mission.py` keeps only data.
- The loader still reads the old layout, so finished missions are untouched (the archived-repos
  rule).

**Phase 6: documentation (½ session).**
- A generated scripts index in SKILL.md.
- A test that every script has usage and is listed.
- Retire `ENGINEERING_PLAN.md` into the README.

Estimate: 5–7 sessions, interleaved with mission work. Scripts are never left half-migrated,
because each phase leaves everything working.

## Decisions (dbenbenn, 2026-10-02)

1. **Lean-side extraction: yes** ("Lean parses Lean!").
2. **Prose as Markdown files** for mission drafting (Phase 5).
3. **Fixtures may reuse real cases**, with care.
   - Mission drafts like Moore become public soon, so excerpts from public or soon-public missions
     are fine.
   - Nothing from private missions (QFS's private repo).
4. **Tests first**: Phases 0–1 come before any refactor.
5. **Open:** a private sandbox on the platform for write-path tests (layer 5 below).

## Test layers

| Layer | What | Speed | When it runs |
|---|---|---|---|
| 1. Unit | pure functions: names, range edits, prose loading, JSON building | seconds | every change |
| 2. Lean integration | LeanInfo on fixture `.lean` files, checking the reported commands, declarations, dependencies and types | seconds each | every change |
| 3. Pipeline regression | rebuild a public mission's solutions and compare them with the accepted submissions, fetched by `GET /submissions/:id/solution`; `draft.py verify` on a recorded proposal | minutes | before merging a migration |
| 4. Live read-only contract | the platform behaves as `p2mlib.api` assumes: page size and `total`, the solution endpoint, graph node and edge shapes, proposal statuses, a known submission's final status; recorded responses for layer 1 come from here | about a minute | on demand and after a platform release |
| 5. Live write path | submit / poll / retry / deprecate / publish / definitions against a **private sandbox** (a private trivial statement; proofs built to be ACCEPTED, rejected, SKETCH_ACCEPTED) | minutes | rarely, on demand; needs dbenbenn's OK |

Layer 4 would have caught three real failures:
- the list endpoint paging at 50 when we asked for 100;
- the poll timeout misread as a rejection;
- "the platform never serves submitted code".
