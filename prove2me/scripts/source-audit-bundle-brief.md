# Source-side audit brief: a definitions bundle

You are checking the DEFINITIONS of a formalization against its mathematical source, from the
source's side. You work in two phases, and in the first you do not see the formalization at all.

## Phase 1: what the source defines

Your directory holds `source.md` (the source and the pages where it sets up its objects) and the
rendered page images `page-*.png`. Read the pages **on the images**.

Write `claims.md`: an inventory of every object the source defines or names by notation on these
pages, numbered D1, D2, … For each:

- the object and its notation, and the verbatim defining words with their page;
- what the definition says, unpacked: the ambient set or space, every condition, every quantifier
  ("finitely many pieces", "all interval endpoints in P_A", "a.e. defined", "measurable");
- **implicit claims carried by the definition**, marked *(implicit)*: "the subgroup of G given by
  …" asserts the set is a subgroup and lies in G; "the group of all …" asserts closure under
  composition and inverses; "the relation induced by …" asserts it is an equivalence relation;
  "a measurable assignment" presupposes a measure. List each one;
- standing conventions the pages set silently (the measure class, the topology, an action's side,
  the orientation), as their own rows, marked *(convention)*.

Include objects the source defines by reference ("we recall that … is amenable if …") as well as
by notation. Do not include results (lemmas, propositions): only what is defined or named.

When the inventory is complete, end `claims.md` with the line `END OF CLAIMS` -- write it last,
and only then. Then stop and reply in at most five lines: the number of objects, conventions and
implicit claims. **Do not look for any formalization; there is none in your directory yet.**

## Phase 2: coverage (only when you are told to continue)

Two files are then added. `readback.md` is a blind, plain-mathematics rendering of the definitions
file, written by someone who never saw the source. `context.md` says what else the formalization
has: the other definition files it imports (with the names they declare), the fact that Mathlib's
own notions (groups, subgroups, commutators, free groups, orders, measures, …) count as available,
every statement of the formalization (title and plain-language statement), and what the
formalization deliberately leaves out. Compare with `claims.md` and write `coverage.md`, one entry
per row Dᵢ:

- **LITERAL**: the file defines the object as the source does. Quote the read-back.
- **EQUIVALENT**: the file defines it differently (a generated subgroup for a set that is already a
  group, SL₂ acting on ℝ ∪ {∞} for PSL₂ on P¹, a finitely additive measure for a mean), and the two
  agree in every case within the source's setting. Give the argument in one or two lines, and
  where it needs a theorem, the statement in `context.md` that carries it.
- **DIFFERENT**: the file defines it differently and the two do *not* agree somewhere within the
  source's setting. Give the near-miss: an object one admits and the other does not.
- **STAND-IN**: the source's object has no definition of its own and is represented by another
  object (an instance of a more general definition). Say what identifies them and whether a
  statement in `context.md` states that identification (then it is carried, not a finding).
- **AVAILABLE**: not in this file, but provided elsewhere: an imported definition file, Mathlib, or
  written out inline in a statement. Name where.
- **PROOF-INTERNAL**: only the source's proofs use it (support of an element, germs); no statement
  needs it. Say which result's proof.
- **OUT OF SCOPE**: only results that `context.md` lists as left out need it.
- **MISSING**: none of the above: a stated result needs the object and nothing provides it.
- For each *(implicit)* claim: **BY CONSTRUCTION** (the file's definition makes it true),
  **CARRIED BY** a statement in `context.md` (name it), **PROOF FACT** (only proofs need it), or
  **UNCARRIED** (a statement relies on it and nothing states or proves it).
- For each *(convention)*: whether the file adopts it, and whether any statement depends on it.
- Then **EXTRA**: definitions in the read-back with no counterpart in the source, one line each
  (an auxiliary notion is fine; say what it is for).

End with a verdict line: `VERDICT: literal` when there are no findings, else
`VERDICT: findings: D2, D5`. A finding is a real issue for the human to decide: every DIFFERENT
row, every MISSING row, every STAND-IN whose identification no statement carries, every UNCARRIED
implicit claim, and every convention a statement depends on that the file does not adopt.
EQUIVALENT rows are *not* findings: list them after the verdict under `EQUIVALENT: D2, D3, …`,
each already argued above, so the human can skim them without being asked to decide.

Reply in at most five lines: the verdict and one line per finding.

## Rules

Work only inside your directory; read nothing outside it. Do not edit `source.md`, the images or
`readback.md`. Quote the source exactly.
