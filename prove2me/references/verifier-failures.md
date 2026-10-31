# When the verifier says no

Failures of `/verify` and of publish jobs that a local build does not reproduce, each with the
case that taught it. SKILL.md's *Verifier failures* table is the index; this file has the detail.

## A solution must not redeclare the target's name with a different signature

A `/verify` submission is compiled **without** the target in scope; the platform then checks
`solution` against the published statement. So the solution file may not mention the target's
name at all: `theorem solution : type_of% @Target := @Target_dev` gets `CE` "Unknown constant
`Target`" (Erdős 3, 2026-10-16), while `theorem solution : type_of% @Target_dev := @Target_dev`
is accepted. And if your solution file declares that **same full name** with a signature that is
not identical, the verdict is `WA` with

    expected token
    Unknown identifier `<your target's full name>`
    Unknown constant `_check`

— a parse-style error, **with no location**, that looks nothing like a name collision and
survives every local check: the merged file builds clean and the server-shape recheck (re-elaborate
the published `formal_statement`, discharge it with `solution`) passes, because locally nothing
else declares that name.

This bites when a development proves the target under its own name and the solution is assembled
by concatenating modules. An *identical* signature is harmless — one mission had a solution
redeclaring its target's exact name and signature and it was ACCEPTED — so the trap only springs
when the signatures differ, e.g. the module says `{G : Type u}` (a file with `universe u`) while
the published statement says `{G : Type*}`.

**Fix:** give the development's theorem a different name and let `solution` be the only
declaration matching the target. Do not "fix" it by editing the signature to match — the name is
the hazard, and a later edit can reintroduce the mismatch.

**Diagnosing a locationless `WA` generally.** Do not guess at syntax. Bisect with submissions
against targets where a `WA` costs nothing — an already-`Proved` theorem, or one that already has
an accepted sketch — changing exactly one thing at a time:

- same file, *different tail* proving some other theorem → isolates content from target;
- a known-good small solution *plus the suspect import* → isolates the import.

Two such submissions localised the above in minutes after two blind fixes had failed. Rule out
size first from the record: a 102KB solution had been accepted, so a 70KB one is not too big.


## Timeouts, heartbeats and size

**Two publish timeouts, two remedies.** "FAILED: Compilation timed out after 300s" means the item itself is too slow: split it, with pieces of about 60–70 s or less single-threaded locally (a 102 s Erdős 3 bundle failed three times, and its 69 s and 33 s halves passed). "ERROR: Internal error while publishing: Module compilation timed out" means the server is building imported bundles on a cold worker. It grows more frequent the deeper the item sits in a bundle chain, but every one so far has eventually passed on an unchanged retry (Erdős 3, 2026-10-08), so retry it and never split it.

**A heartbeat timeout the local build never shows: replace the `rfl`, do not raise the limit.** Erdős 3 v2 bundle B122 (2026-10-17) failed on the verifier with "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)" and again at `set_option maxHeartbeats 400000`, on a one-line `rfl` proof that locally passes under 5,000 heartbeats, with every imported bundle on the platform byte-identical to the local files. Reproving it without the deep unfolding (extensionality on the structure, then the definitions' own `@[simp]` coordinate lemmas, then a small `rfl`) published at once. So for a verifier-only heartbeat timeout, rewrite the proof to avoid the reduction; raising `maxHeartbeats` is not a reliable remedy there.

**Reproduce it first, with synchronous elaboration.** The verifier elaborates synchronously. q128 (2026-10-30, Finitistic bundle F039, a `LinearEquiv` literal with `rfl` fields): "(deterministic) timeout at `«abstract nested proofs»`" on the server at 200000 and again at 1000000, while plain local `lean` passed; `lean -j1 -DautoImplicit=false -DElab.async=false` failed exactly as the server did. There `set_option maxHeartbeats 0 in` before the declaration (before its docstring) compiled in about 50 s under the same flag and published, and the flag caught a second such bundle (F028) before sending. So: reproduce under `-DElab.async=false`; a raise that passes there is reliable, one that only passes plain `lean` is a guess.

**A WA "does not match the target type" that no local check reproduces: look for a raw `Classical.choose (Classical.choose_spec …)` in a hypothesis.** Erdős 3 v2 (2026-10-18): two statements got WA ("failed to synthesize CoeT … timeout at `typeclass` (20000)") for every proof, although locally the solution's type and the target's were `Expr`-equal, every published file was byte-identical and every emulation of the check passed. Private probes (`"private": true` statements keeping the hypotheses, conclusion `True`, proof `trivial`) bisected it in four rounds of about 15 minutes each: the trigger was two hypotheses whose binder types repeated `Classical.choose (Classical.choose_spec (exists_… m dim))`. Restating them after the colon, with the term named once by `let A := …` (the form the accepted statements used), passed at once. The proofs needed only an `intro` and positional arguments. So: never put a raw choose-of-an-existence-theorem into a binder type; name it with a `let` after the colon. To bisect a verifier-only WA, use private trivial probes rather than guesses. The verifier elaborates the check separately from the solution file, so options set in the solution never reach its message, and the soundness guard refuses metaprogramming.

**Proof submissions time out the same way.** A solution's verify can return `ERROR` with "Verification
timed out after 300s". Measure the solution file single-threaded (`lake env lean -j1 FILE`; the default
parallel wall time hides the cost): Artin's (10.10) solution took 81 s single-threaded (17 s wall) and
timed out twice, while 18 s and 40 s ones passed. Over about 60 s single-threaded, split it into
published cuts before the second retry.

**Retry or split according to how easy the split is** (dbenbenn, 2026-10-08). When the carver can cut an item cleanly into parts that are each much faster, split early, after an own-compile timeout or a slow local check, because a split costs little. Dependency timeouts ("Module compilation timed out") do not depend on the item's own size, so they never justify a split: a 14 s Erdős 3 bundle got four in a row while its 42 s sibling passed first try. When one heavy declaration dominates, or the best cut barely changes the time, keep retrying much longer instead. Never loop re-splitting for a marginal gain: a 76 s bundle that the scheduler kept "splitting" to stay under a 75 s cutoff went through unsplit on a retry.

**Carried-over `local notation` lines cost about 1 s each to elaborate.** A carved bundle that keeps every module section's notations can be dominated by them. Erdős 3 B132 had 166 notations for 36 declarations: 161 s at -j1 and 25 own-compile timeouts, though no declaration took more than 5 s. Dropping the unused notations brought it to 73 s, and it published. Prune unused notations when carving.

**A third failure kind is deterministic:** "FAILED: definition does not compile: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)" can appear on the server for a declaration that compiles locally (Erdős 3 B025, 2026-10-08). Retrying cannot fix it. Put `set_option maxHeartbeats 1000000 in` before that declaration and resubmit.

**The hard size limit is 1 MiB.** The soundness guard refuses a solution over 1,048,576 bytes before compiling it: "Source too large for token scanner" (FAILED, 2026-10-07, a 1.65 MB port of OpenAI's Kaplansky counterexample). Stripping comments saved only 6%. A larger proof has to be split into published intermediate statements, each proved by its own submission. A disproof cannot be split, since it cannot import theorems, so it has to be golfed instead. The Kaplansky disproof went from 1.65 MB to 995 KB by pruning, stripping comments, renaming identifiers to short names, adding `notation` aliases for long Mathlib names, and one global `open scoped Classical`. Tactic `macro`/`syntax` shortcuts are refused by the soundness guard, but `notation` lines pass. 299 KB and 332 KB solutions were accepted.
