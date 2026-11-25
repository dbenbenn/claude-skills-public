---
name: prove2me-program
description: Companion to the prove2me skill for machine-code (program) missions on prove2.me — verifying compiled AArch64 object code against a specification on the republished DeepMind semantics. Covers choosing and provenancing the binary, exporting it to a bundle (rust-obj2lean), writing contracts (placements, hooks, LinkOk, stack frames, registers, data, stack guard), executing every contract on the semantics before stating it, what the source audit is for when the object is a binary, milestone granularity, non-vacuity, and proving. Load it together with prove2me whenever a mission, milestone or standalone statement is about a binary, object file, library function or machine code.
---

# Machine-code missions on prove2.me

This skill adds to `prove2me`; it does not replace it. Load both. `prove2me` owns everything the
platform does (rulebook sync, the algorithm, read-backs, source audits, the gap review, Draft,
Submit, the queue, after-launch care), and every rule there applies here unchanged. This file holds
only what is different when the formalized object is compiled code. Where the two seem to disagree,
the difference is written here on purpose. If it is not, `prove2me` wins; fix this file.

Missions so far, each with its repo (RESUME.md, ITEMS.md, DECISIONS.md, `checks/`):

| Mission | Object | Repo |
|---|---|---|
| zlib `crc32_z` | our zig build of zlib 1.3.1, one block | `~/claude/zlib-crc32-aarch64` |
| x25519-dalek | DeepMind's libsignal object, 19 blocks | `~/claude/x25519-dalek-aarch64` |
| BoringSSL Poly1305 | our build; parked | `~/claude/poly1305-boringssl-aarch64` |
| libsodium Poly1305 | Debian's released `libsodium.a` objects | `~/claude/poly1305-libsodium-aarch64` |

Shared packages: the AArch64 semantics (`~/claude/arm64-semantics-p2m`, 56 `Def_Arm64_*` bundles,
namespace `Arm64`, public) and libc contracts plus link sanity (`~/claude/p2m-standalone/arm64-libc`:
`Def_Musl_StringContracts`, `Def_Musl_ExternHooks`, `Def_Libc_ExplicitBzero`, `Def_Link_LinkOk`).
Upstream is google-deepmind/code-verification (Apache 2.0): keep its headers, mark our changes,
credit it. No further permission is needed.

## The shape of a line of work

- **Two missions per target.** Mission A is the mathematics or the specification (a paper, or an
  RFC when there is no paper: Bernstein 2006 for X25519, Bernstein 2005 for Poly1305,
  Kadatch–Jenkins for CRC). Mission B is the code, with a bridge milestone into A (the RFC function
  equals A's object). Important code may be formalized **without a paper**; the RFC or the source is
  then the specification.
- **Existing verification does not rule a target out.** DeepMind already verified x25519-dalek; it
  still went on prove2.me, carved into milestones. Credit prior work in the description.
- **Pilot first.** One routine, plain tactics, proved locally, before any item list: it tests opcode
  coverage, the export, and whether the proof method scales (`crc32-pilot`, `poly1305-pilot`).

## Choosing the binary

- **Prefer a released binary over our own build.** dbenbenn's rule (2026-11-25): compiled code is
  left untouched. A distribution's object (Debian's `libsodium-dev` → `libsodium.a` → `ar x`) is
  what users run, and verifying it also checks that the release is not tampered with. Do not strip,
  relink or edit functions to make the export or the proof easier: removing libsodium's keygen
  functions with `llvm-objcopy` was rejected.
- **Our own build** (when no release fits): zig cc with the flags `rust-obj2lean print-cflags`
  gives, pinned in `Implementation/build.sh`. Watch for libcalls the compiler invents: a zeroing
  loop becomes a `memset` call unless built with `-fno-builtin-memset`. Record the decision.
- **Read the disassembly before designing anything** (`source/*disasm*.txt`): which functions the
  compiler inlined or kept (GCC kept libsodium's `poly1305_update`, so it became a milestone), the
  externs, the data objects, stack frames, the stack protector, PAC/BTI hints.

## Provenance and the bytes

The bundle must hold the shipped code, and that is checked mechanically:

1. **Provenance chain** for a released binary, written up in `Implementation/<dist>/PROVENANCE.md`:
   archive key fingerprints from the distribution's key page → `gpgv` on `InRelease` → the
   `Packages` index sha256 → the `.deb` sha256 → `ar x` of the named objects, with their sha256s.
   `fetch.sh` redoes and checks every step. Model: `poly1305-libsodium-aarch64/Implementation/debian/`.
2. **Same code as the shipped shared library**: every function of the objects occurs byte for byte
   in the `.so`, except at relocated words (`tools/debian_so_match.py`).
3. **Bundle code equals the objects' `.text`**, and every word decodes (`checks/DecodeAll.lean`:
   count instructions and padding words; an undecodable word is a missing opcode).

## Exporting the object to a bundle

- **rust-obj2lean** (upstream, pinned commit) turns objects into an `Obj.PlacedLib` module from a
  `translation.toml` (objects, `namespace_prefix`, `[placed] placed_only`, `exports`). It needs a
  Rust toolchain and zig on `PATH`; see the mission RESUMEs for the store paths that worked.
  `--placed-witness` synthesizes a concrete placement (useful for the non-vacuity proof).
- **GCC branch-protection objects** carry `.note.gnu.property`; upstream rejects it. Build the
  patched exporter with `arm64-semantics-p2m/tools/rust-obj2lean/build.sh` (skips `SHT_NOTE`;
  offered upstream as issue #6 — PRs there are limited to collaborators).
- **Prefer a single-block `PlacedLib`**: link the objects into one text block. A `MultiPlacedLib`
  gives hooks per block, and a hooked extern called from another block then has no usable hook;
  the libsodium multi-block export was unusable for that reason. DeepMind's x25519 object is
  multi-block and its contracts use no hooks.
- **Make it publishable**: `tools/inline_bytes.py` (copy from the libsodium repo) replaces each
  `include_bytes%` by a byte literal, maps `import Arm64.Trusted.X` to `Definitions.Def_Arm64_X`,
  drops the `IncludeBytes` elaborator, and adds a modification notice. Nothing else changes.
- **Upstream DSLs are banned** (the platform rejects `macro`/`syntax`/`elab`): a contract written
  in `rust_spec` or `c_type_spec` is published as the term it elaborates to, checked equal to the
  upstream constant (`x25519-dalek-aarch64/elab/`, `arm64-libc/tools/make_contracts.py`).
- **Local lake quirk**: in a project requiring `arm64-semantics-p2m`, a module named
  `Definitions.*` is looked up inside that package; name local object modules
  `<Mission>.PlacedObj` and rename at publication.
- Upstream builds on a newer Lean than the platform: compile everything on the platform's toolchain.

## Writing the contracts

The Spec bundle defines one judgment per kind of function and states each milestone with it.
Model: `poly1305-libsodium-aarch64/lib/Def_Poly1305Debian_Spec.lean`.

- **The judgment.** `internalOk fnName spec`: `fnName` is a symbol of the block, and for every
  placement `pl` with `lib.Placeable pl`, the guard and link hypotheses, and every hook table
  `externs` meeting the hook conditions, `subroutine_ok (lib.program pl externs) (lib.fnAddr pl
  fnName) (spec pl)`. `publicOk` adds `fnName ∈ lib.exports` and lends the data objects (below).
- **Link sanity: always assume `Link.PlacedLib.LinkOk lib pl externs`** (bundle `Def_Link_LinkOk`).
  Upstream `Placeable` checks only that relocations fit. In the semantics a branch to an extern's
  address runs the hook of the *first* extern listed there, while a contract assumes hooks by name:
  with `crypto_verify_16` and `sodium_memzero` at one address, two published libsodium statements
  were false (disproofs 0deb3f8b, 13e72391). `LinkOk` gives what a real link gives: externs at one
  address share a hook, no extern inside code or data, data objects disjoint from each other and
  from code.
- **Hooks for libc calls use the shared contracts**: `HookSat externs "memset"
  VerifiedLibraries.Musl.cryptoMemsetSpec`, `HookSat externs "sodium_memzero"
  Libc.explicitBzeroSpec`. Never invent a mission-local condition when a shared one exists; add a
  missing one to `arm64-libc` (with its own non-vacuity proof) and import it. These `cExtern`
  contracts let the hook use **4096 bytes below the stack pointer it is entered with**.
- **Stack frames are read off the disassembly** and owned in the precondition (`stackFrame s0 n`).
  A function that calls a hook owns its own frame plus 4096 below the call's `sp`; for a tail call
  the hook enters at the function's own entry `sp`, so 4096 dominates. Write the arithmetic down
  in RESUME.md per function (libsodium: finish 4128, final 4144, one-shot 4320).
- **Registers.** `subroutine_ok` already gives the AAPCS64 callee-saved set. Add a register clause
  only where a caller needs more: GCC's interprocedural register allocation lets a caller rely on
  registers a `static` callee happens not to touch (Debian's `poly1305_blocks` keeps `x0` and `x18`
  for its callers). Read the callers' code to find them.
- **Data objects** come from `lib.dataInit pl`; `withData pl spec` lends them to an exported call
  and asks for them back unchanged. A writable C object (non-`const` table) is owned, not read-only.
- **Stack protector through the GOT**: `guardSites` (the `adrGotPage` relocations to
  `__stack_chk_guard`), `GuardUniform pl` (all relaxed or none), `guardRes pl g` (the guard
  readable where the code reads it, relaxed or through a GOT slot). Copy from the Debian Spec.
- **PAC/BTI hints** (`bti c`, `paciasp`, `autiasp`) execute as no-ops in the model. Say so in the
  description's Formalization scope (decided 2026-11-25).
- **State representations.** For streaming APIs (init/update/final), the goal quantifies a
  representation predicate existentially, `∃ Rep, initOk Rep ∧ updateOk Rep ∧ finalOk Rep`, with the
  one-shot stated directly (agreed 2026-11-25). Accumulators are specified by value modulo the
  prime, as the source's comments do, not limb by limb; limb *bounds* are stated, and must be the
  real ones (next section).
- **Name every clause used twice** (prove2me's rule): `MemsetOk`, `GuardUniform`, `StateOk`.
- **Reuse published bundles** for the layout, invariants and tags when a second binary of the same
  source arrives (the Debian Spec imports the clang-era `Poly1305Libsodium_Spec`).

## Execute every contract before stating it

A false contract is disproved within hours by a prover running the semantics; every disproof so
far was something an evaluation would have caught. Before a statement enters a Draft, run it on the
semantics (`#eval`/`decide` on the placed program with a concrete placement) and keep the files in
the repo's `checks/`, listed in RESUME.md. Rerun all of them before the Draft goes out (not yet
automated; do it by hand and say so in the hand-over).

- **End to end**: the exported functions against the specification on many lengths, splits and
  keys (`checks/DebianE2EEval.lean`: one-shot 10 lengths, streaming 8 splits × 2 keys).
- **Every precondition at its edges, including values no caller uses.** A compiler that sees all
  callers of a `static` function may exploit them: Debian's GCC loop in `poly1305_blocks` ends when
  the pointer *equals* `m + bytes`, valid only for multiples of 16. The contract allowed any
  `bytes ≥ 16`, was checked only at 16, 32, 48, 80, and was disproved within the hour (88a8159d).
  Run the boundary, non-multiples (17, 31, 33), and the smallest and largest admitted values. A
  loop whose exit test is `!=` on a pointer or counter signals an unstated divisibility condition;
  a `do … while` signals an unstated nonzero condition.
- **Bounds against the code's truncations.** Craft extreme but legal states and check every stated
  bound: a limb bound of `2^44` was false (a crafted state gives `2^44 + 16`; `checks/craft_h1.py`),
  and an earlier `h0` bound was false because only some carries are truncated to 32 bits.
- **Contract chains: run each consumer on what its producer's contract admits**, not only on
  states the producer really produces. If `finish` is wrong on a state `blocks`'s postcondition
  allows, either the invariant is too weak or the code is wrong; search for an input that reaches
  the state before deciding which. (One mission goal was false this way, exposing an upstream bug.)
- **Hooks and placement**: evaluate with two externs at one address and with adversarial hooks
  that still meet the hook contracts, to confirm the statement depends on `LinkOk` and nothing
  weaker.

A disproof found while the proposal is In review stops the review; `prove2me` says what to do.

## What the source audit is for

(dbenbenn, 2026-11-25, after the Debian libsodium mission.) When the formalized object is a binary,
the paper-era notion of fidelity does not carry over. The object code is in the Lean byte for byte,
so the Lean cannot silently drift from it; the C source and the documentation are untrusted
accounts of the binary. Three things can still go wrong, and the audit spends its effort
accordingly:

- **The bytes.** The provenance chain and the byte comparisons above. Mechanical, no judgement.
- **A statement too strong** is false and gets disproved. That costs a resubmission, nothing worse.
  Prevent it by execution (previous section).
- **A statement too weak** is what nothing catches automatically: a precondition no caller can
  meet, a postcondition that says too little, a degenerate representation predicate. This is where
  the source audit earns its cost. Its claims still come from the C and the documentation. Each
  WEAKER or MISSING finding is first classified:
  - *the binary differs from the C* (shown by executing the binary): the statement follows the
    binary and the milestone's note documents the difference. This is decided by standing rule
    ("document the difference between what the C code does and what the object code does",
    dbenbenn 2026-11-25), so the row goes in the summary list for skimming, not to the human one at
    a time;
  - *the statement is weaker than the binary's documented or used behaviour*: a genuine row for the
    human.
- **Code quotes are commentary.** A milestone quotes the code's comments or lines to orient the
  reader; they are not a sentence the statement must match, and a bundle note need not quote every
  function it names. UNQUOTED findings on code are dismissed by this rule.
- Recurring dispositions, already decided: DIRECTNESS "about the compiled code, not the C
  function" is inherent (dismiss); constant-time claims are out of scope (the model has values, not
  time; say so in Formalization scope); exact limbs vs value mod p, keep the value.

## Milestone granularity

Milestones are the public API layers and the hard core (the arithmetic, the final reduction, the
block step), each a function a reader would name. Compiler-shaped helper contracts (IPA-RA
register clauses, length quirks of an internal loop, segment lemmas of a long function) are not
milestones: provers publish them as auxiliary statements when a proof needs them. (dbenbenn liked
this as a first take, 2026-11-25; refine it with the next mission.)

## Non-vacuity

Every hypothesis of the judgments must be satisfiable together, proved as a published statement and
cited in the description (dbenbenn: a general requirement; `mission_captain.md` §5). Shape:
`∃ pl externs, lib.Placeable pl ∧ GuardUniform pl ∧ MemzeroOk externs ∧ MemsetOk externs ∧
Link.PlacedLib.LinkOk lib pl externs` (`Poly1305Debian.exists_placement_hooks`, in
`p2m-standalone/poly1305-debian-readings`). A shared hook contract gets its own
(`Libc.exists_hookOk_explicitBzeroSpec`). Publish it as a standalone companion after Submit, as libsodium did, prove it, and link it from
the live description after approval.

## After Submit: proving

- **Framework first, then fan out.** DeepMind's ProofLib tactics and DSL macros are banned in
  solutions, so proofs use plain tactics on a framework of stepping lemmas. Four x25519 batches each
  built their own in parallel (≈$370, much of it duplicated). Queue one framework batch first
  (fetch, step lemmas per instruction shape, relocation, separation-logic loads/stores, frames, a
  loop combinator), publish its cross-block facts (`X25519Dalek.steps_keepsFrozen` exists: import
  it), then fan out with each batch told to import the framework.
- **Siblings watch each other.** A batch whose target imports a sibling milestone rechecks the
  sibling's status and RESUME at each stage of its own work; a Disproved sibling means "look for the
  same counterexample in my target first".
- **Narrow imports**: no `import Mathlib` in statements or machine pieces (prove2me's rule); the
  zlib pieces fell from 7.1 GB to 2.6 GB.
- Proof method — fetch lemmas, naming computed values, `clear * -` before `omega`, kernel-evaluated
  disproofs, guard lemmas, memory: `references/proving.md`.
- **An upstream bug found by a proof or disproof** is reported upstream only by dbenbenn
  (outward-facing; possibly a security report). Draft the report in the repo's `bug/`, keep the
  details out of anything public until the fix ships, and park the mission.

## Repo layout

`Implementation/` (build or fetch scripts, `translation.toml`, PROVENANCE.md), `gen/` (raw export),
`lib/` (bundles and statements), `source/` (C, disassembly, documentation, page renders),
`checks/` (evaluations), `statements/`, `prose/`, `readbacks/`, `proofs/`, `solutions/`,
`explanations/`, `tools/`, ITEMS.md, DECISIONS.md, RESUME.md, `published_ids.json`. Start from the
libsodium repo.
