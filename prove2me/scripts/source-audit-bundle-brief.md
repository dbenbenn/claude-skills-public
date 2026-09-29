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

A file `readback.md` will then be added: a blind, plain-mathematics rendering of the definitions
file, written by someone who never saw the source. Compare it with `claims.md` and write
`coverage.md`, one entry per row Dᵢ:

- **LITERAL**: the file defines the object as the source does. Quote the read-back.
- **ENCODED**: the file defines it differently (a generated subgroup for a set that is already a
  group, an operator for a family of means, a local condition for "finitely many pieces"). Say
  exactly how, whether the two agree, and by what argument. If they do not agree in every case,
  give a near-miss: an object one admits and the other does not.
- **STAND-IN**: the source's object has no definition of its own and is represented by another
  object (an instance of a more general definition, "G" as "G(R)"). Say what identifies them.
- **MISSING**: no definition. Say whether the file could state results about it at all.
- For each *(implicit)* claim: the file cannot assert it (definitions do not prove things); say
  whether the read-back's definition makes it true by construction, or whether it is a claim some
  theorem must carry, and state that theorem.
- For each *(convention)*: whether the file adopts it.
- Then **EXTRA**: definitions in the read-back with no counterpart in the source, one line each
  (an auxiliary notion is fine; say what it is for).

End with a verdict line: `VERDICT: literal` when every object is LITERAL and every convention is
adopted, else `VERDICT: findings: D2, D5` (every row that is ENCODED, STAND-IN or MISSING, and
every implicit claim no construction makes true). An ENCODED row with a sound argument is still a
finding: the human decides whether the encoding stays.

Reply in at most five lines: the verdict and one line per finding.

## Rules

Work only inside your directory; read nothing outside it. Do not edit `source.md`, the images or
`readback.md`. Quote the source exactly.
