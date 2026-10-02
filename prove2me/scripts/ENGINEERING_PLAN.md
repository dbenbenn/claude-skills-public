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
| Platform API | an unpaginated GET /submissions (100 of 981, 9e59d0c); a poll timeout reported as a rejection; the false belief that the platform never serves submitted code |

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
5. **No live write tests** (dbenbenn: "We're doing enough real writing that we'll notice such a
   problem").
6. **Pipeline regression runs locally on golden files.** Pick realistic tricky cases, fetch their
   accepted solutions **once**, and store inputs and outputs under `tests/golden/`. Tests never
   refetch.
7. **The live read-only checks need a trigger, not my memory.** They run with the session-start
   docs sync (fetch, read the diff, fast-forward `prove2me_workspace`), and always when that sync
   brings a new platform release.

## Test layers

| Layer | What | Speed | When it runs |
|---|---|---|---|
| 1. Unit | pure functions: names, range edits, prose loading, JSON building | seconds | every change |
| 2. Lean integration | LeanInfo on fixture `.lean` files, checking the reported commands, declarations, dependencies and types | seconds each | every change |
| 3. Pipeline regression | golden files fetched once into `tests/golden/`: the check module and its dependencies, plus the accepted solution of a few tricky targets. The rebuild must match the golden output. | minutes (Lean) | before merging a migration |
| 4. Live read-only contract | the platform behaves as `p2mlib.api` assumes: page size and `total`, the solution endpoint, graph node and edge shapes, a known submission's final status, `deprecated_at` on the detail endpoint | 5 s | at every session-start docs sync, and whenever it brings a platform release |

Layer 4 would have caught three real failures:
- an unpaginated list read (`GET /submissions` returned 100 of 981, 9e59d0c);
- the poll timeout misread as a rejection;
- "the platform never serves submitted code".

## Status

**Phase 0 (2026-10-02): done.** The inventory is in `scripts/README.md`.

**Phase 1 (2026-10-02): done.** `tests/`: 103 passed + 7 strict xfails, 49 s with every layer, in three groups:
- offline unit and regression tests, under a second;
- Lean tests (`P2M_LEAN=1`), about a minute;
- live read-only checks (`P2M_LIVE=1`), seconds.

Every regression test fails on the pre-fix version of its script (checked with `git show <fix>^`).

**Coverage, by script.**
- **Solution pipeline:** `build_solutions`, `merge`, `prune_solution`, `rewire`, `resolve_imports`,
  `assemble_blueprint`, `extract_payloads`.
- **Platform API:** `submit_all`, `submit_solution`, `deprecate`, `edge_audit`, `fetch_theorems`,
  `publish_standalone`, `publish_status`, `watch_proposal`, `p2m`'s comment guard.
- **Audits and checkers:** `draft` upload/verify plus its prose checks, `stage_auditor`,
  `source_audit`, `decisions`, `caveat_audit`, `check_description`, `check_pronouns`,
  `check_server_shape` (Lean).
- **Golden files:** Moore `isMarginal_EBad` (byte-identical to the accepted solution); Lemma 5.6
  assembly (pinned, compiles).
- **Not covered:** `build_solution.py`, slated to merge into `build_solutions`, and `watch_targets`.

**Strict xfails: known bugs, each to be fixed by a later phase.** The test flips when the bug is
fixed.

| # | Bug | Where | Fixed by |
|---|---|---|---|
| 1 | The pipeline cannot produce a hand-rewired solution: it misses copies under other names | Moore `bijOn` golden | Phase 4.2, type equality |
| 2 | Parts with a `section`/`variable` block spanning targets are mis-split | `assemble_blueprint`, FAmenChild | Phase 4.3, LeanInfo ranges |
| 3 | A comment line beginning `theorem` is taken as the declaration | `rewire.published` | Phase 3, one `published()` |
| 4 | A one-line `@[simp] theorem` is not found | `resolve_imports.extract` | Phase 4, LeanInfo ranges |
| 5 | An attribute line above the declaration is not carried | `resolve_imports.extract` | Phase 4, LeanInfo ranges |
| 6 | A primed statement name is truncated | `draft.extract_payloads` | Phase 4, LeanInfo names |
| 7 | Re-staging deletes a live auditor's directory | `caveat_audit.stage` | Phase 3, shared staging with `stage_auditor`'s guard |

**Duplication made visible by the tests.**
- The workspace lookup exists in 3 copies, so a fake workspace must be patched into `edge_audit`
  and `prune_solution` separately.
- `ROOT` is imported by value from `stage_auditor` into `source_audit` and `caveat_audit`.
- `caveat_audit` copies `source_audit`'s page rendering.
- `paged()` exists in 2 copies.

**A wrong claim corrected.** "/missions pages at 50" was false; my loop stopped at offset 400. The
live contract now pins full 100-item pages.

**Phase 2 (2026-10-02): done.** The tool is `lean/LeanInfo.lean`, with its wrapper
`p2mlib/leaninfo.py`.

**What it reports.**
- **Commands:** kind, `in`-wrapped kind, byte and line ranges, the namespace and opens in force,
  attributes, and declared names.
- **Declarations:** full and private names, kind, range (doc comment and attributes included),
  selection, pretty-printed type, `type_hash`, `uses_local` (auxiliaries folded through) and
  `uses_imported` (our modules only).
- **Messages:** all of them.

**What the wrapper adds.**
- Each declaration is mapped to its command, and constants Lean generates are flagged.
- `command_span` tiles the file exactly, so cutting by command never drops or duplicates text.
- `unknown_identifiers()` lists the identifiers Lean could not resolve.
- Results are cached by content, plus the imports' mtimes.

**Tests.** 18, on three fixtures (Structure, Broken, Notation):
- offline tests of the wrapper on recorded JSON;
- Lean tests requiring the tool to reproduce its recordings exactly, plus a test that the cache
  answers a second run.

**Real files.** The 2,251-line Lemma 5.6 proof takes 6 s to parse and 16 s to elaborate (355
commands, 284 declarations). FAmenChild PartB2 parses with no errors.

**Findings.**
- **Messages.** Elaboration resets the message log per command (`elabCommandTopLevel`), so the
  tool collects them command by command; the parse log starts fresh, so syntax errors survive.
- **Parse-only mode.** Pure parsing failed on `ℝ≥0∞`: scoped notation needs its `open scoped`
  elaborated. Parse-only mode therefore elaborates the commands that shape parsing, and never
  declarations.
- **`type_hash`.** It ignores binder names and binder brackets. A statement hidden behind a local
  definition hashes differently (the `bijOn` / `CommonCaret` case), so Phase 4.2 needs a
  Lean-side defeq comparison.

**Next: Phase 3.** The `p2mlib` core: `api` (pagination, polling, retries), `workspace`, `names`,
`leanedit` (cut and insert by LeanInfo ranges), and `mission` (loading without
`import mission`).
