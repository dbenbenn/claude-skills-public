# Source-side audit brief: a definitions bundle

You are checking the DEFINITIONS of a formalization against its mathematical source, from the
source's side. You work in two phases, and in the first you do not see the formalization at all.

## Phase 1: what the source defines

Your directory holds `source.md` (the source and the pages where it sets up its objects) and the
rendered page images `page-*.png`. Read the pages **on the images**.

Write `claims.md`: an inventory of every object the source defines or names by notation on these
pages, numbered D1, D2, … For each:

- the object and its notation, and the verbatim defining sentence **in full, from its subject to
  its end**, with its page ("We call a locally compact group G amenable if …", not "amenable if
  …");
- **the subject the definition predicates and what it presupposes about it**, as an *(implicit)*
  claim: "a locally compact group G is amenable if …" defines amenable only for locally compact
  groups, so "G is amenable" also asserts that G is locally compact. A definition stated for "the"
  object of a standing setting presupposes that setting;
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

Three files are then added. `readback.md` is a blind, plain-mathematics rendering of the
definitions file, written by someone who never saw the source. `note.md` is the bundle's own
note, the prose published beside it. `context.md` says what else the formalization has: the other definition files it imports (with the names they declare), the fact that Mathlib's
own notions (groups, subgroups, commutators, free groups, orders, measures, …) count as available,
every statement of the formalization (title and plain-language statement), and what the
formalization deliberately leaves out. Compare with `claims.md` and write `coverage.md`, one entry
per row Dᵢ:

- **LITERAL**: the file defines the object as the source does. Quote the read-back.
- **EQUIVALENT**: the file defines it differently (a generated subgroup for a set that is already a
  group, SL₂ acting on ℝ ∪ {∞} for PSL₂ on P¹, a finitely additive measure for a mean), and the two
  agree in every case within the source's setting. Give the argument in one or two lines, and
  where it needs a theorem, the statement in `context.md` that carries it.
  **Check every role before you write EQUIVALENT.** A statement in `context.md` either *assumes*
  the notion of an object (a hypothesis: "if G is amenable …") or *concludes* it of an object it
  builds ("… then the quotient G/N is amenable"). "Within the source's setting" covers the
  presuppositions of Phase 1: in a hypothesis role the statement usually supplies them (it also
  assumes G locally compact); in a conclusion role nothing does unless the file's definition
  carries them itself. So for each statement that concludes the notion, ask whether its hypotheses
  already give the object those presuppositions; if not, and the file's definition does not
  include them, the row is **DIFFERENT** in that role: name the statement and give the near-miss
  (an object the file's definition admits there that the source's, with its subject, does not).
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
- Then **QUOTES**: `note.md` is the bundle's own note, which quotes the source for its
  definitions. For each quoted defining sentence: is it verbatim (compare with Phase 1's words),
  and does it include the subject the definition predicates, with that subject's qualifiers ("a
  locally compact group G")? A quote that drops such a subject, or a qualifier
  that carries a presupposition, is **QUOTE-TRUNCATED**: give the full sentence. A definition the
  note does not quote at all although the source has a defining sentence is **UNQUOTED**.

End with a verdict line: `VERDICT: literal` when there are no findings, else
`VERDICT: findings: D2, D5`. A finding is a real issue for the human to decide: every DIFFERENT
row (in any role), every QUOTE-TRUNCATED or UNQUOTED quote, every MISSING row, every STAND-IN whose identification no statement carries, every UNCARRIED
implicit claim, and every convention a statement depends on that the file does not adopt.
EQUIVALENT rows are *not* findings: list them after the verdict under `EQUIVALENT: D2, D3, …`,
each already argued above, so the human can skim them without being asked to decide.

Reply in at most five lines: the verdict and one line per finding.

## Rules

Work only inside your directory; read nothing outside it. Do not edit `source.md`, the images or
`readback.md`. Quote the source exactly.
