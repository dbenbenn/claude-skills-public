# The upload pipeline, and what silently breaks it

`upload_full_project.md` describes the intended flow. This file records the traps.

## Shape of the tree

A published project becomes, in the prove2.me Lean workspace (the `prove2me_workspace`
checkout):

- `Definitions/Def_<Bundle>.lean` — one bundle per source module, carrying that
  module's `def`s and `structure`s
- `Theorems/Thm_<Name>.lean` — one file per theorem: imports, then the statement with
  `:= by sorry`
- `Solutions/Sol_<Name>.lean` — the same statement named `solution`, with the real
  proof, importing the `Thm_` files of the published theorems it uses

Generation is by **skeleton subtraction**: take the source module, delete every
declaration except the target (and, for a solution, its same-module helpers), rewrite
the import block to the bundles. Generators live in `~/qfs-platform/upload/gen/`.

## Publishing a batch

Use `~/qfs-platform/upload/gen/upload_batch.py <meta.json>` rather than a hand-rolled
loop. It exists because two mistakes recurred:

**Never hand-write the publish order.** Dependents get published before their
dependencies whenever the order is written from how the results *read* rather than how
they *depend*. In one paper the wide-cone regime is derived as the case `γ = π/2` of the
axis-spread one, so `*_wide` imports `*_spread` — and it was published first twice,
because "wide cones" reads like the simpler, earlier case. The ground truth is already
on disk: the `import Theorems.Thm_*` lines of each `Sol_` file. Topologically sort those.
`--dry-run` prints the derived order.

**Refresh the access token.** A batch of twenty-plus theorems outlives one token, and the
failure lands as a bare `HTTP 401` on whichever item happened to be last. Route every
request through a refreshing accessor.

**Not everything cited is publishable as a theorem.** `submit-problem` takes theorems;
a `def` — including one that produces a structure, like a `WhitneyBallData` witness — has
to go in a definition bundle instead, and a theorem *embedded* in a bundle cannot be
published at all (see above). When a description cites such a name, reword the citation
rather than build a bundle for it: the invariant worth keeping is that every name a
reader sees resolves, not that every name gets its own page.

## Traps

**A definition item reads back under `theorem_name`.** You POST a proposal definition item
with `definition_name`, but `GET /mission-proposals/:id` returns it with that value in
`theorem_name` and `definition_name` absent. Filtering the item list on `definition_name`
finds nothing and looks exactly like "the upload silently failed". Match on
`kind == "definition"` instead.

**The api_key is not a bearer token.** `credentials.json` holds a `p2m_…` key that
must be exchanged at `POST /agent/refresh` (`{"api_key": …}`) for a short-lived
`access_token`; that token is what goes in `Authorization: Bearer`. Sending the key
itself gets a flat `401` on every endpoint, which reads exactly like an expired key —
decoding the JWT's `exp` and finding it weeks away is the tell that the flow, not the
key, is wrong.

**Byte offsets, not character indices.** Lean's `String.Pos` are UTF-8 byte offsets.
Slice source as `bytes` in Python. Hit twice; corrupts silently and the corruption
looks like a plausible file.

**Stale offsets against an edited source.** The extractor records offsets from one
commit; the generator reads the file from disk *now*. Edit the repo — even a docstring
— and every splice silently corrupts. Guard: check that each recorded declaration
still begins with a declaration keyword, and refuse to run otherwise. Generate against
a pristine tree (`git archive <sha> | tar -x -C tmpdir`), selected by an env var.

**Theorems embedded in a definition bundle cannot be published standalone.** A theorem
reachable from a `def`'s body — typically because the definition is built by `.choose`
from an existence lemma — lives *inside* that bundle. Publishing it under its own name
fails with "has already been declared". Publish a restatement under a new name instead
(`ref_cones_paper`), proved from the bundled one in a line.

**Structure accessors share the structure's span.** A `Prop`-valued field of a
structure is a theorem whose declaration span *is* the structure's. Inlining one
re-declares the whole structure. Any planner must treat accessors of a bundled
structure as bundle-provided, never as inlinable helpers.

**A new definition bundle takes minutes to reach the verifier.** Solutions importing
it fail with `no such file or directory: Definitions/Def_X.lean` even though the
definition published fine. Not a real error — retry.

**Response shapes differ.** `POST /submit-definition` returns `job_id` at the top
level; `POST /submit-problem` returns `jobs[0].job_id`. Handle both, and never write a
"diagnostic" retry that POSTs placeholder metadata — it may succeed.

**A solution may carry helper declarations.** If a proof needs an unpublished lemma
from another module, paste it into the `Sol_` file rather than building a new bundle.

## The gate to run before publishing anything

For each pair, in the workspace:

```lean
import Theorems.Thm_QFS_foo
import Solutions.Sol_QFS_foo
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let e ← getEnv
  logInfo m!"foo :: {← isDefEq (e.find? `QFS.foo).get!.type (e.find? `solution).get!.type}"
```

`true` means the solution proves the statement that was published, not a neighbour of
it. Separately, normalise whitespace and compare the published `formal_statement`
against the repo's — the two are written at different times and drift.

A `sorryAx` in `#print axioms solution` is expected: solutions import `Thm_` stubs,
which are `sorry`. What matters is that the `Sol_` file itself contains no `sorry`.

## State

Keep the upload state file outside any per-session scratchpad — scratchpads are
per-session, not per-project, and collide across projects. Record every action before
and after its API call so an interrupted run resumes without duplicates. Never edit
the state file while an uploader holds it.
