# Proving machine-code statements with plain tactics

DeepMind's ProofLib (about 200k lines, hundreds of macros and elaborators) cannot be used in a
prove2.me solution: the verifier rejects metaprogramming. Proofs are written against the published
`Def_Arm64_*` bundles with plain tactics. Worked examples, each with a NOTES.md: `crc32-pilot`
(66 instructions), `poly1305-pilot` (117), `zlib-crc32-aarch64/proofs/` (508, split into pieces),
`x25519-dalek-aarch64/proofs/` (call composition), `poly1305-libsodium-aarch64/proofs/` (hooks,
stack guard, GOT). Reuse a framework before writing one (SKILL.md, "Framework first").

## The framework

- **State abstraction**: `mkS s0 pc sp mem ps r` with `r : Nat → BitVec 64` for the general
  registers and generic `rd_gpr`/`wr_gpr` lemmas, so one step lemma per instruction *shape* serves
  every register (`poly1305-pilot`).
- **Step lemmas** state results as `BitVec.ofNat 64 (Nat expression)`, so the arithmetic later is
  about natural numbers.
- **Name every computed value** (`reach_gen` or `generalize`). Composing steps without naming makes
  each value mention the whole previous register function: the term roughly doubles per
  instruction, and some passes are not sharing-aware (40 instructions 4 s, 48 instructions 16 s).
- **Code stays loaded across a call**: import `Theorems.Thm_X25519Dalek_steps_keepsFrozen`
  (published, Proved) instead of porting DeepMind's `Invariant.lean`. If a port is unavoidable, drop
  the `symtab` lemmas (77 s of its 134 s; pick what to drop by profile, not by guess).
- **Address computations hand back separation-logic facts**, not reads. A lemma for a GOT load
  (`adrp; ldr`, possibly relaxed) whose continuation gets `m.read64 x = g` is useless once the code
  writes the stack; give it `m ⊨ guardAt pl g x ∗ F` instead, so the fact survives later writes
  (libsodium `GuardPair.lean`).
- Generate long straight-line chains from the decoder output with a script (`tools/gen_chain.py`)
  rather than by hand.

## Fetching instructions from a large block

- Prove closed facts about the code bytes (`decode (wordAt off) = some i`, `relocAt? off = none`,
  `relaxableAt`, `wordAt`) by `decide +kernel`, never `rfl` or `decide`: `rfl` makes the
  elaborator unfold and keep the whole code literal (+1 GB per module in zlib).
- For a large block, decode once in chunks: prove `wordsOf code n = codeChunks.flatten` by
  `decide +kernel` over literal chunks of 32 words, the generic `wordAt` ↔ chunk lemma, then each
  `decode (chunk.getD r 0) = some I` on a short list. zlib's 502 fetch lemmas: 19 s, against
  2–3 min per-address and 17 GB for one big `decide` (`zlib-crc32-aarch64/.../tools/gen_code5.py`).

## Arithmetic

- **`clear * -` before `omega`/`bv_omega`.** In a long chain the context holds dozens of `% 2^64`
  equations, and omega takes all of them: one side goal went from over 5 min to under a second.
  Write each fact as `have … := by clear * - h₁ h₂; omega`, and clear per-step hypotheses once used.
- `omega` treats products as atoms: supply bounds as facts about the product terms, and prove
  modular identities with `ring` (or `linear_combination`; `grind` costs memory).
- Small exactness lemmas for 128-bit add/mul/extract (`mul128`, `add128`, `extr128`) keep the
  carries readable.

## Disproofs by kernel evaluation

A disproof cannot import theorems, so it cannot be split: it must fit the verifier on its own.
- Reuse the placement and hooks of the published non-vacuity statement (copy them in).
- Run the concrete program in the kernel (`decide +kernel`, never `native_decide`).
- Never index a long list literal in the kernel: each `getD` re-walks the chain (~30 ms per lookup;
  `CodeBlock.patched` cost 25 s / 6.9 GB). Encode byte strings as one little-endian `Nat` read with
  shifts, convert the bundle's list once by `decide +kernel` on `bundleList = bytesOfNat n N`, and
  `generalize` huge values as variables. One disproof went from 86 s / 6.8 GB to 26 s / 2.4 GB.
- Bisect a slow `type checking took` with `#exit` and `set_option profiler true`.

## Memory and CPU budget

- Measure peak memory as soon as the skeleton compiles (`prune_solution.py --check`), not only CPU.
  Most of a piece's peak is often `import Mathlib`; narrow it before splitting.
- Above about 6.8 GB, move a self-contained lemma block into its own published statement
  (pre-approved) and import it.
- Never name a development declaration after a core type (`Fin`, `List`): after merging, a
  sub-namespace resolved `Fin D` to it and the error surfaced only after 7 minutes.
- After `build_solution.py`, check the imports by hand: it has added unused or unpublished
  `Definitions.*` imports (q458, q461), and `prune_solution.py` has dropped a bundle that was the
  only route to the `Def_Arm64_*` modules (q445).
