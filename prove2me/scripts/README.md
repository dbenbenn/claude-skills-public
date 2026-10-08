# prove2me scripts

The tooling behind the `prove2me` skill: drafting and auditing missions, building and submitting
solutions, keeping the dependency graph honest. SKILL.md's **Scripts index** lists every script
(generated from the docstrings by `gen_index.py`); each runnable script prints its usage when run
with no arguments.

## Layout

| Path | What it is |
|---|---|
| `scripts/*.py` | the command-line tools |
| `p2mlib/` | the shared library: `api` (client, pagination, polling), `workspace` (the Lean workspace, published statements), `names` (one identifier grammar, primes included), `leantext` (comment stripper, header scanner), `leaninfo` (wrapper for the Lean tool), `leanedit` (edits by command ranges and scopes), `prune`, `copies`, `mission` (loader, prose files), `staging`, `carve` (splitting a large port: graph, plan, carver) |
| `lean/LeanInfo.lean` | the Lean tool: what a file contains, as Lean sees it (`--idents`: every identifier by role, for the carver) |
| `lean/DeclGraph.lean` | the declaration graph of a compiled development (`scripts/carve.py graph`) |
| `tests/` | the test suite and its fixtures |

## Principles

- **Lean parses Lean.** Declarations, names, ranges, scopes, dependencies and statement equality
  come from `lean/LeanInfo.lean`, never from regular expressions over Lean text. Regex survives
  only where Lean cannot run: `resolve_imports.extract` reads another project's tree, and
  `draft.extract_payloads` runs while a mission's bundles may not be built. Both use the shared
  grammar in `p2mlib.names`.
- **One copy of everything.** One API client, one workspace lookup, one comment stripper, one
  `published()`, one mission loader, one edge auditor.
- **Edits by ranges.** `p2mlib.leanedit` removes and replaces whole commands, keeps the comment
  block above a command with it, and re-creates a command's scope anywhere (`scope_wrap`).
- **A bug is a test first.** A known bug lands as a strict xfail, with a check that the regression
  test fails on the pre-fix code. A change to shared tooling is run against a real corpus before it
  ships: every accepted Moore solution, every mission's payloads, a live mission's audit.

## What LeanInfo reports

`lake env lean --run lean/LeanInfo.lean FILE [--parse-only] [--candidates M1,M2,…]` prints JSON:
- **Commands:** kind, ranges, declared names and their `declId` ranges, attributes, `decl_kind`
  (Mathlib's `lemma` counts as a theorem), where the value starts (`:=`), namespace, opens, and
  scope context (the opener commands and the open/variable/universe/include/omit/set_option
  commands in force).
- **Declarations:** full name, kind, ranges, type and its hash, and `uses_local` /
  `uses_imported`. Uses are the constants in the value, plus every name the elaborator resolved in
  the command's source: an `rfl` lemma used by `simp only` leaves no trace in the term.
- **Messages:** all of them.
- **With `--candidates`:** each theorem's `same_statement_as`, meaning equal after renaming
  universes, unfolding the file's own predicates and erasing proofs (deliberately not `isDefEq`).

Parse-only mode elaborates just the commands that shape parsing, so unbuilt modules can be read.
`tests/record_fixtures.py` re-records the fixtures after a change to the tool.

## Tests

```
python3 -m pytest tests/                        # unit + offline (seconds)
P2M_LEAN=1 python3 -m pytest tests/             # + Lean: LeanInfo, golden rebuilds, assembly
P2M_LEAN=1 P2M_LIVE=1 python3 -m pytest tests/  # + read-only checks against the live platform
```

| Layer | Content |
|---|---|
| unit | helpers, on recorded LeanInfo JSON and fake platforms |
| Lean | LeanInfo must reproduce its recordings; copies found by statement |
| golden | rebuild two accepted Moore solutions from their development and compare (`tests/golden/`); assemble two real Blueprint jobs and compile them (`tests/golden_assemble/`) |
| live | read-only platform contract (pagination, served sources); `sync_workspace.py` runs it each session |

Nothing writes to the live platform from a test.

## History

Built 2026-10-02 in six phases at dbenbenn's request. The same bug classes kept recurring (primed
names, escaping, namespace stacks), so the work was a test harness first, then the LeanInfo tool,
then a shared library and a migration of the scripts onto it. Each finding is in git history
(`ENGINEERING_PLAN.md`, retired here). The ones worth knowing:

- **Proof terms miss tactic dependencies.** `simp only [h]` with an `rfl` lemma rewrites by
  `dsimp` and leaves no constant behind; pruning by the term deleted Moore's `bits_001`.
  Dependencies now include what the source names (info trees).
- **`lemma` is not core syntax.** Mathlib's `lemma` is its own command kind, so a pruner keyed on
  core's `declaration` never deleted one (71 in one Moore file).
- **Comments belong to the previous token.** By Lean's ranges, the comment above a declaration is
  trailing trivia of the one before it.
- **Info state is per command.** Elaboration resets the message log and the info trees for each
  command (`elabCommandTopLevel`), so both are read command by command.
- **`open scoped` has no `OpenDecl`.** A command's scope is recorded as the commands themselves.
- **`Ω[` is a Mathlib token** (Kähler differentials), so `Ω[i]` does not parse: write `(Ω)[i]`.
- **Copies are found by statement, not by `isDefEq`.** Default-transparency defeq would equate
  `2 + 2 = 4` with `4 = 2 + 2` and invent an edge. A lemma that is *half* of a published `∃!`
  (Moore's `reduced_unique`) is no copy at all, and only a person sees it.
- **Golden files must allow improvement.** A rebuild may drop dead code the old tool kept, which
  the case pins with a reason (`dropped_since_accepted`), and import order is a set. Otherwise a
  better pruner reads as a regression.
- **Corpus checks catch what fixtures miss.** Re-pruning 31 accepted solutions found the `lemma`
  gap. Comparing 7 missions' payloads found that `'MooreFoelner.'` is a namespace prefix, before a
  stricter identifier match could drop a bundle import.
- **One auditor, checked against the old one.** On the live CFP §7 mission both report 0
  INCORRECT and 0 MISSING. The new one elaborated all 26 live proofs (none unchecked). Its SHARED
  section names the known §7 case, `subsimplex_of_farey` re-proving part of a published
  criterion, among 8 pairs that otherwise share basic lemmas. It takes 13 minutes instead of 1¼,
  and is cached for re-runs.
- **Elaborating with candidates is memory-heavy** (about 8.4 GB per proof), so `edge_audit` sizes
  its pool from `MemAvailable`.
