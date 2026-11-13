# Porting and carving openai/math results

How a ported openai/math proof reaches prove2.me: the single-file route, and when that is too
big or too slow, the carver that splits it into published bundles, statements and pieces. Loaded
from SKILL.md's *Porting an openai/math result* pointer. The sections follow a port's course:
search, the single-file route, the module port and Mathlib drift, the carver, the
`carve_pipeline.py` driver, measuring, slow failures, publishing, after publishing, retrying.

**Timing rule for this whole file:** verifier-failures.md, "Proof submissions time out". The
verifier's limit is about 100–110 s of local CPU under synchronous elaboration. `PIECE_CAP` is
100 s: a solution over 100 s is split before its first submission, one under it is submitted as
is. Memory is a separate limit, about 7 GiB peak (`PIECE_RSS_LIMIT`).

OpenAI's Mathlib is d13f23b; ours is 0df444a. The published OAI goals were generated from
openai/math at `adc7f12`.

## Search first

- **Search prove2.me before publishing anything**, for the goal and for each named result
  (`/theorems?theorem_name=`, `/definitions?q=`, by title). Someone else's existing statement is
  imported or proved, never published a second time. If the goal overlaps published work or is
  already proved, see "After publishing" (**Overlap with someone else's published work**, **A goal
  someone else has already proved**). Also ask whether a *stronger* Proved result of the same family
  implies the goal in a few lines (read the family's `docs/NNN.md` and its other challenges): q230
  proved two goals from the family's Proved 7/8 zero-free half-plane, with no port.

## The single-file route

- **Use the skill's scripts for every port; never copy them into a job directory.** Private copies
  drifted apart from the shared fixes (twenty carves, 2026-10-18). The shared text transformations
  are in `p2mlib.oaiport`; `tests/test_oaiport.py` pins the bugs they fixed.
- **The single-file route comes first.** Fetch the import closure with `oai_fetch.py`. `oai_port.py`
  merges it, drops every declaration of the statement's published bundles by full name, renames
  OpenAI's copy of the target `<name>_oai`, and checks the verifier's form locally with `-j1`.
  `oai_batch.py --dir JOB` does this for many goals; `oai_submit.py --dir JOB` is the submit queue
  (restart-safe: each goal's state is rebuilt from its log). Every route renames the target `_oai`
  because the verifier compiles a solution without its target in scope (verifier-failures.md, "A
  solution must not redeclare the target's name"); without it submissions came back WA.
- **Submit it as it is; don't optimize first.** Under 100 s of local CPU, submit unchanged. Over it the
  timing rule says carve first, but `oai_submit.py` still sends such a file once: a file at or over
  `RETRY_UNDER` (90 s) gets one attempt, a faster one an unchanged retry. A port that times out
  twice is carved.

## The module port

`carve_pipeline.py` runs the module route (see "Running a carve"). This section is what it does
and how to repair it.

- **The steps.** `oai_port_modules.py` writes the modules into `Solutions/FOLDER`, the compatibility
  lemmas in namespace `OAI`; `oai_build_modules.py --elab-log` builds them; `carve_prep.py config`
  takes `--def` for each published bundle the goal imports and `--forced` for each theorem the paper
  names (each becomes its own published statement, reusable by others); then `carve.py graph`,
  `carve_prep.py ext-defs`, `carve.py plan/gen/order`, `carve_measure.py`, `carve.py split`. The
  module port inlines tactic macros across modules, as `oai_port.py` does, `syntax` + `macro_rules`
  tactics included: a recursive one becomes `repeat' (first | …)` in source order, without backtracking
  (9cb038c; q222 still needed a reorder by patch), and a call it cannot flatten is left with a warning
  (expand those uses by hand). `oai_build_modules.py`
  rebuilds a module when anything it imports changed: no `--force` after a fix.
- **A bundle that needs a statement imports it.** With `bundles_import_statements` (the default), a
  bundle imports a forced theorem that definitions need. That import is allowed only once the theorem
  is Proved, so `publish_order` puts the bundle after the statement's piece.
- **One live run per carve.** `oai_build_modules.py`, `carve.py` and `carve_measure.py` each allow one
  live run per carve (`p2mlib/runlock.py`); a second copy exits 3 and names the running pid. Wait for
  that run or stop it; never start another. Stop a run with a plain `kill PID` (SIGTERM), never `kill
  -9`: SIGTERM makes the lock holder stop its `lake` and `lean` too, while after `kill -9` they keep
  compiling and race the next run over the same `.olean` files (oaiq-003, oaiq-012).

### Port patches

- **filter-patches counts against the ported text.** Single-file patches go through `carve_prep.py
  filter-patches` (the pipeline's `filter_patches` step), with the same compat options as
  `oai_port_modules.py`. It counts each patch against the module port's text, not OpenAI's source:
  the port's rewrites can add a match (`OAI.tensorInductionOn`) or remove one (a compat alias). Quote
  the ported text (an `inferInstance` at a `Measure.map` site is a long `first | infer_instance | …`
  line there) and count with `rg -c` in `Solutions/FOLDER`. A patch whose count differs fails the step,
  listing its occurrences per module (`"allow_drop": true` lets one go). So does an `old` that starts
  or ends inside a longer identifier (oaiq-040: `hpos` matched `hpositive`): end `old` at a delimiter.
  It drops single-file-only patches (`"route": "single"`, or reordering a universe list for merge.py's
  `universe` line).
- **A patch dropped for too few occurrences prints `why:`**: the rule that now rewrites its site and
  what the port writes there, or "not in the port's input". Check the new text and drop the patch
  rather than marking it `allow_drop` blindly (oaiq-090). If the dropped patch carried another repair
  in the same hunk, re-add that as its own entry (q136).
- **Make patches from a diff against a pristine port**, so each `count` is taken over the unpatched
  port, never the patched workspace (oaiq-063, -071). Keep the whole port run with patches `[]`, on the
  current snapshot, as PRISTINE (q234: a pristine from before a tool fix makes patches the new rules
  already cover; mkpatches refuses an `old` that also occurs in a port module PRISTINE lacks, q220,
  `--port-dir` when it cannot find the port), repair by hand, then `scripts/mkpatches.py PRISTINE
  REPAIRED OUT.json`: it grows each hunk's
  context until `old` is unique and not cut mid-identifier, merges into an existing OUT.json, and checks
  the result reproduces the repair byte for byte (oaiq-043, -080). A line patch whose `old` is also the
  tail of a more-indented line double-counts: anchor it with a leading `\n` (oaiq-086). q141's
  `tools/rebase_edits.py` (save repairs, re-port pristine on a new snapshot, 3-way merge, mkpatches,
  verify) makes mid-repair rule changes cheap.
- **`core_rewrites` is not idempotent** (the argument-dropping rules drop again): never re-run it on
  ported text.
- **When a port rule matches a tactic spelling**, `rg` the port for unspaced and variant spellings
  (q133: `; first|…` escaped the `; first | …` rule).
- **Iterating on drift fixes.** Edit the ported file in `prove2me_workspace/Solutions/FOLDER` and
  compile it alone (`lake env lean FILE`, seconds), with the pipeline's flags (`lean -j1
  -DautoImplicit=false`; a `-j1` build can hit heartbeats an in-place `lake build` does not).
  - After the first failure of a kind, `rg` the whole port for the pattern and patch every site before
    rebuilding (oaiq-089). Within a module read the first error: a failed `def` header drops its `variable` binders, so dozens of
    `Unknown identifier ι` after it are a cascade (q261).
  - Batch compat changes before the first full build: a compat change rebuilds everything (oaiq-091).
  - Let the pipeline's `build` build the modules. An in-place build writes neither module times nor
    the LeanInfo cache, so `graph` elaborates every module itself (oaiq-092: about 6 h) and the plan is
    blind. `config` fills missing times from the LeanInfo cache and stops when under half the port is
    timed: then delete `.lake/build/{lib/lean,ir}/Solutions/FOLDER` and `--redo build` (a03f3b3). An
    in-place `lake build` of the root can invalidate the pipeline's oleans (q128: a 70-minute rebuild):
    build single modules in place instead.
- **After a build failure, skipped importers hide the next errors.** The build reports every failure
  of a round, but after each fix stop the driver (`systemctl --user stop carve-<hash>`) and resume
  rather than waiting for the build to end (oaiq-107).
- **A heartbeat failure in the pipeline's build is not evidence** until plain `lean
  -DautoImplicit=false` reproduces it: LeanInfo elaborates synchronously and spends more (3230451
  retries such modules with plain `lean -o`). Bundles and pieces are the opposite case: the verifier
  elaborates synchronously too (verifier-failures.md, "Reproduce it first, with synchronous
  elaboration").
- **Heartbeat failures clustered in one module family**, each compiling in seconds with a raise: add
  `set_option maxHeartbeats 1000000 in` per declaration across the whole family at once. Not
  module-wide (carved pieces would not carry it), not one module per round (q145: 450 `Cartan*`
  modules).
- **A `whnf` or kernel deterministic timeout that a raise does not cure in seconds is not a budget
  problem**: raising the limit only traded it for 10–22 GiB (q246, q261). Profile (`trace.profiler`) and
  read the deepest `isDefEq`: usually two instance paths d13f23b unified cheaply (q246:
  `NonUnitalCStarAlgebra` of `M.toStarSubalgebra`; q261: `Algebra ℚ (FractionRing (MvPolynomial ι ℚ))`
  by `DivisionRing.toRatAlgebra` against Ore localization, cured by a high-priority instance pinning
  OpenAI's path), or a `change`/`show` across them (rewrite that step). `#synth` the instance in a
  scratch file to see which path fires. Remedies, best first: when a compat instance opens the second
  path, pipeline.json `hide_instances` for the whole port (q360: `OAI.vonNeumannToStarSubalgebraIsClosed`;
  `attribute [-instance]` per module makes a new diamond at every boundary, and a pin that is a new
  constant still left `rfl` between applied maps timing out); a priority pin, in every module of the chain
  or none (in one module alone it made it slower); per site, `erw` for the `rw`, `rw … at h; exact h`
  for `simpa`, a `show` restating the goal, or a local instance stated at the use (q258, q359). A compat
  instance that a published `Def_*` bundle also declares anonymously meets it in carved pieces the same
  way (q258: `MeasurableSpace (Matrix …)`).

### The compatibility block and shims

- **The compatibility block lives in namespace `OAI`** (`--root-compat` restores the old root form,
  where two bundles declaring `ite_eq_left` clash). Aliases are rewritten into the sources instead,
  since a namespaced `alias Finset.prod_le_prod₀` would create `OAI.Finset`, shadowing `Finset` under
  `open Finset`. Two published bundles still export root names: UniversalFInfinity's `OAIQWUFI004`
  (`ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right`) and ESB's `OAIQWESB000` (`alias
  Finset.prod_le_prod₀`). A port that imports either must not declare those names again.
- **`--compat-imports narrow`.** `import Mathlib` in Compat leaks instances: Mathlib's `CStarMatrix` (a
  type copy of `Matrix`) breaks `simp only [Matrix.mul_apply]`. `oai_port_modules.py --compat-imports
  narrow` gives Compat only the Mathlib files its lemmas need (`oaiport.COMPAT_NARROW_IMPORTS`); set
  the carve's `collapse_mathlib` to false so carved files keep OpenAI's narrow imports too. A module
  that then misses a name gets its import by a patch.
- **`TensorProduct.inductionOn` becomes the compat eliminator `OAI.tensorInductionOn`**, declared in
  `lean/compat_4_34.lean` with d13f23b's signature (zero case from `tmul 0 0`; ours, `induction_on`,
  wants a `zero` case); `oaiport.core_rewrites` points every use at it, so no zero case is guessed. It
  is not `OAI.TensorProduct.inductionOn`: that namespace makes `open TensorProduct` inside `namespace
  OAI` open only it, losing Mathlib's `⊗ₜ` lemmas. Old `| zero => …` patches count 0: drop them.
- **`Convexity.StdSimplex` is handled by a shim, never by hand.** `lean/StdSimplexCompat.lean` supplies
  d13f23b's `Convexity.StdSimplex` API under its names (Part 1) plus `OAI.SStd`, the subtype
  `stdSimplex` with the same names (Part 2). Both port routes apply it when a source mentions
  `StdSimplex` (`--stdsimplex auto`, `p2mlib.oaiport.stdsimplex_*`): they drop the d13f23b-only
  `Mathlib.Geometry.Convex.ConvexSpace.*` imports, and the module route adds the module
  `StdSimplexCompat`. Pass the same `--stdsimplex` to `oai_port_modules.py` and `carve_prep.py
  filter-patches`.
  - Code that uses `SimplexCategory.toTop.obj` as a `StdSimplex` (Problem340) needs `--stdsimplex
    subtype` (renames `Convexity.StdSimplex` to `OAI.SStd`; needs finite index types, has no
    `ConvexSpace`). Code mixing both uses needs hand work.
  - `SimplexCategory.toTopHomeo` and `TopCat.toSSetObjEquiv` take the simplex to the structure in
    d13f23b and to the subtype here. Structure mode renames them, with `toTopHomeo_naturality_apply` and
    `toSSetObjEquiv_{symm_naturality,naturality_apply,δ_apply,σ_apply}`, to `…D` versions with d13f23b's
    types from `lean/StdSimplexTopCompat.lean` (module `StdSimplexTopCompat`, imported where used; the
    single-file route inlines it after the shim). OpenAI's own `toSSetObjEquiv_…` lemmas keep their names.
    Three ports hand-wrote this bridge before it existed (oaiq-043, oaiq-066, q225; 2026-11-11). What
    stays manual: a d13f23b `rfl` proof that unfolded through the simplex (oaiq-066's `simplex_face :=
    rfl`) needs `rw [TopCat.toSSetObjEquivD_δ_apply]` or the like, since the homeomorphism is not
    definitional. The `D` lemmas fire under `simp` exactly where Mathlib's originals do, and like them not
    on `TopCat.of X` with a `.symm` inside. `subtype` mode is no way out for code that also uses the
    structure's fields.
  - The shim is published as `Definitions.Def_OAIStdSimplexCompat` (c7014b9a,
    p2m-standalone/oai-stdsimplex-compat). With that bundle built in the workspace
    (`Definitions/Def_OAIStdSimplexCompat.lean`, byte-identical to `lean/StdSimplexCompat.lean`),
    `oai_port.py` imports it instead of inlining, and `carve_prep.py config` adds it as a `--def`.
    `StdSimplexTopCompat` is published likewise as `Definitions.Def_OAIStdSimplexTopCompat` (42fe481c, same
    folder; its text is `oaiport.stdsimplex_top_shim()`, importing the first bundle) and used the same
    way once in the workspace.
- **A Mathlib definition that changed shape wants a shadowing shim**, not per-site patches (q141:
  `UnifIntegrable`, `UniformIntegrable`, `UnifTight` at about 260 sites). Write a module under `OAI`
  with d13f23b's shape and its API proved from ours: inside `namespace OAI`, `OAI.X` wins over `open
  MeasureTheory`'s `X`, so bare names need no rewriting. Models: `StdSimplexCompat`, and
  `UnifIntegrableCompat` (00f2d9c, 64c9ae2; opt-in per carve, pipeline.json `"unif_integrable": "on"`;
  each construction site needs one measurability line, and a lemma concluding `UniformIntegrable` from
  `eLpNorm` estimates alone gains a measurability hypothesis). It stays opt-in until the carves that
  hand-patched uniform integrability are published.
- **Read d13f23b itself before writing a shim.** A shallow fetch (about a minute, 150 MB) is kept at
  `~/.cache/p2m/mathlib-d13f23b` for every worker (`git init; git fetch --depth 1 origin
  d13f23b723b8a846827a245b89c10fc7d3f11612; git checkout FETCH_HEAD`); it settled every "Unknown
  constant" root of q145.
- **Where a shim or a missing name goes.** In this carve, place it in the lowest module under most of
  its users, not in `compat_4_34.lean` (which rebuilds the whole port), and add an `import` to the few
  users not under it; lemmas with one to three users go into each user (`private theorem` when
  several). A single missing Mathlib name is declared by a port patch in a common ancestor of its users
  (oaiq-107). q145's `anc.py` (records folder) computes the common ancestors and the users not under the
  best host. For later carves, add it to `compat_4_34.lean` with its test; copy a carve's shims there
  (with tests) once that carve no longer needs a plain `--upgrade`.
- **Shims declare their attributes on the declaration** (`@[aesop 50% apply …] theorem …`), never as a
  standalone `attribute […] X` command: the carver repeats a section's standalone command in every file
  keeping a declaration of that section, and aesop refuses a rule registered twice (q141). Shim text
  passes the soundness guard (no `unsafe` token; a test checks every shim, adc4387).
- **Compat instances are global** (oaiq-122: one made `whnf` time out in three modules). A compat
  instance carrying data is a `@[reducible] def` made local by a port rule keyed on what the module
  names (2165390). A carve whose port built before a compat instance was added can hide it with
  pipeline.json `hide_instances` (0eea563). A module that built before and times out at `whnf` after an
  upgrade: bisect the compat instances first (`attribute [-instance]` in a copy, about 20 s each).
- **`import all`.** OpenAI reaches Mathlib's *private* declarations with `import all`
  (`…IsGaussianProcess` for `Finset.orderEmbOfFinWithBot`), which a non-`module` file cannot use. Copy
  the private declarations into the module (root names; the private ones are mangled, so nothing
  clashes).

### Foreign packages

OpenAI's lakefile requires about twenty packages (PrimeNumberTheoremAnd, StrongPNT,
RellichKondrachov, TauCeti, ClassFieldTheory, …) that the repo does not contain (oaiq-083).
`oai_fetch.py` exits 1 naming any root the closure imports that is neither OpenAI's nor in our
toolchain.

- **Getting the sources.** Put them beside `OAI/` in `src/lean` (the commit pinned in
  `lean/lake-manifest.json`) and resume; the port takes them as OpenAI's. With a local checkout at the
  pinned commit, `oai_fetch.py DEST ROOT --foreign <checkout>` (repeatable) copies the package's import
  closure, strips LeanArchitect annotations (a8b47ea), and names any module the checkout lacks
  (oaiq-093: a stray import to patch away). Turn `/--` doc comments inside tactic blocks into `/-` by
  hand. Packages written in the module system
  (`module`, `public import`, `public section`, `@[expose]`, `public def`) need no strip script: the
  port's `demodule` makes them plain (0edecdf, fb51151). The `Erdos970` forks are in
  `prove2me_workspace/Solutions/OAIChowla`.
- **Size.** Very large closures with foreign packages (oaiq-093: 2,679 modules) are a day's work, not
  a batch. Look for statements already published from them (the Chowla split) to use as
  `external_theorems`. A root module that bundles several comparator theorems, only some Open, is
  scoped first: edit the fetched `src` root to import only the Open goals' branches (a port patch
  cannot drop imports) and record the edit (q235: 504 modules with a foreign package became 178).
- **Before the first build, check each package:**
  1. *Its Mathlib* (`lean-toolchain`). The port rewrites every module as if it targeted d13f23b; for a
     package on an older Mathlib (Gromov), where its Mathlib and ours agree the rewrite breaks working
     code (q145: `(hf := …)` inserted into `grw [eLpNorm_sub_le]`). Revert those rewrites by patch;
     its `Finset.prod_le_prod'`-style names are its Mathlib's, our unprimed ones.
  2. *Its `autoImplicit`*. A package that sets only `relaxedAutoImplicit = false` (Schoenflies) relies
     on auto-bound implicits, and the port builds with them off: patch `set_option autoImplicit true`
     after the imports of each of its modules (q146).
  3. *Its commands*: `rg` it for `#print`, `#eval`, `elab`, `macro`, `syntax`, `run_cmd`. The carver
     keeps every non-declaration command of a module it draws from, except the info kinds it lists. An
     `elab` must go even when no kept proof uses it, with its whole meta section: helper defs typed in
     `TermElabM`, `TacticM`, `MetaM` are refused by the platform (q151).
  4. *Its `sorry`s*: list every `sorry` in the closure with the import that brings it in, which often
     is unused (q142: `PerronFormula` imported `Wiener` for nothing).
- **Vendored sources copied from an earlier port** are already on our Mathlib, and the port's
  d13f23b rules rewrite them again (q142: `Finset.prod_le_prod` became `prod_le_prod'` in the Chowla
  copy of `PrimeNumberTheoremAnd.Erdos970`). Prefer the fork's original text; otherwise expect undo
  patches.
- **A package on an older Mathlib repairs in layers** (q244, q359: ClassFieldTheory on 5ed2965, 12
  build rounds of ~1.5 h each): a failed module skips its importers, so fix each recurring pattern across
  the whole package before rebuilding, never one module per round. Its instance diamonds (`Algebra ℚ` on
  `SeparableClosure ℚ`: `DivisionRing.toRatAlgebra` against the package's own instance) take the local
  repairs of "two instance paths" above. `--compat-imports narrow` fails once Compat holds lemmas needing
  broader imports.
- **`Finset.one_le_prod` / `one_le_prod'` swap meaning** between d13f23b and ours (ordered monoid vs
  GroupWithZero, `one_le_prod₀` there): the rule maps the monoid lemma, so a source that meant the
  GroupWithZero one (q145's Gromov `PosDef`) needs a per-port patch.

## Mathlib drift (d13f23b against ours)

Fix each drift at its cause; none needs a macro.

### Rewritten by the port

`oaiport.core_rewrites` and the compat lemmas in `lean/compat_4_34.lean` handle these;
`tests/test_oaiport.py` has each rule's cases. A hand patch at such a site counts 0 and filter-patches
drops it with a `why:` naming the rule: delete it from the patches file.

- **`Measure.map` sites** (8bac231, f6bb691, d0c5d2c, f76350b): `IsProbabilityMeasure` instances
  (`inferInstance`, `infer_instance`, `inferInstanceAs`, `by unfold foo; infer_instance`),
  `ProbabilityMeasure.map ν f`, `μ.map F` with `μ` a `ProbabilityMeasure`, the `Measure.map_smul` and
  `fst_map_prodMk` arguments. The fallback tries the function's named measurability facts (a
  hypothesis, or a `foo_measurable` / `measurable_foo` lemma anywhere in the port), then a bounded
  `infer_instance`, then `AEM_TAC` (`fun_prop | assumption | … | measurability`).
- **The `eLpNorm` family** (0cd4396; `Lp` norm sites 0888a41, af5cc81, 7a21c26): removed measurability
  arguments are dropped by position, added ones are inserted by name and proved by `AESM_TAC`, and
  renames such as `eLpNorm_indicator_const₀`, `eventuallyEq_univ` and `mgf_gaussianReal heq`.
- **Renames and compat lemmas** (f6bb691, d0c5d2c, f76350b, ae6d21c, 2c13ec2, cf1ff0e), among them
  `MemLp.mul` and `MemLp.smul` by argument name (also through an untyped `have`), `Pi.lift_comp_π`,
  the `List` `length` → `card` lemmas, `not_imp` under `open Classical`, `Ordinal.lt_wf.induction` (now `WellFoundedLT.induction`, case `ind`), `simp [ite_true]` gaining
  `if_true`, and `Finset.antidiagonal` outside Hahn-series files.
- **`convert h using 1` + `· rfl` / `· ext x …` on `HasDerivAt` / `HasFDerivAt`** becomes
  `h.congr_deriv (Eq.symm ?_)` (8fdf735): hand patches adding a `symm` count 0.
- **`norm_num` on `Fin` literals** (1a89f36; this Mathlib's `norm_num` runs no simprocs): a terminal
  `norm_num [L]` after `fin_cases`, or one naming a `Fin.` lemma, becomes a `first | (simp L; …) | …`
  chain. Drop hand patches `norm_num [L]` → `simp [L] <;> norm_num`.
- **`List.TFAE.out N M`** → `.out (N-1) (M-1)` (e359e08; d13f23b counts from 1).
- **`; ring` after a simp-family step that now closes the goal** becomes `<;> …`
  (`_simp_semicolon_closer`, a910463). Where the simp step closed one goal of an unbulleted block and
  the closer was meant for the next, that is a build error, not a silent change.
- **Refused tokens**: `prelude` becomes `prelude_` (the soundness guard refuses it even as an
  identifier); a bare `variables` becomes `«variables»` and an index `c[j]` becomes `(c)[j]` (oaiq-082);
  the refused `elab` `additive_combination` becomes `linear_combination (norm := ((try simp only
  [smul_add, smul_sub]); abel)) …` (ae6d21c).

### Repaired by hand

Before repairing a drift error, `rg -g '*patches*.json' NAME ~/claude/p2m-standalone/openai-ports
~/.claude/jobs` (a carve's `pipeline.json` names its patches file): the repairs of every earlier carve are there (q260's 57 for operator theory, q244's and q359's for
ClassFieldTheory), with the private re-proofs of lemmas missing here. Only patterns that recur go in the
list below.

- **Pi-form vs lambda-form (`to_fun`).** Our `HasDerivAt.mul/neg/sum/pow`, `DifferentiableAt.sum`
  conclude `c * d`, `-f`, `∑ i, f i` as functions, OpenAI's the lambda, so a `convert … using 1` leaves
  extra goals (a function equality, an instance diamond). Use the `fun_` variant (`fun_mul`, `fun_neg`,
  `fun_sum`, `fun_pow`) and close what is left with `all_goals first | rfl | …`. `ContDiffAt.mul` has
  no `fun_` form: `convert … using 1 <;> first | rfl | (funext z; simp …)`.
- **`Measure.map` sites the port leaves.** `μ.map T` of an untyped `ProbabilityMeasure`; an instance
  used implicitly by a lemma statement (add `haveI … := Measure.isProbabilityMeasure_map …`); a map
  whose measurability is a named lemma (`measurable_liftPair d`): name it directly, since the tactic
  chain can time out at `isDefEq` (oaiq-041). A `measurability` fallback can hit maxRecDepth when no
  named fact exists. The port's `first | infer_instance | exact Measure.isProbabilityMeasure_map …`
  line times out at `whnf` when the measure is a `let`: name `Measure.isProbabilityMeasure_map
  hφ.aemeasurable` (oaiq-074). `ProbabilityMeasure.map` with a bare function, after a `)` or across a
  line break is left too: `rg` them all before the first build (q242: ~20 modules found one build
  round at a time).
- **`eLpNorm` sites the port leaves.** An `apply` followed by one bullet per goal (delete the dropped
  goal's bullet); a `rw [foo a b]` that left the removed argument as a side goal; an `AESM_TAC` site
  where nothing fixes the function yet (`simpa … using eLpNorm_sum_le (…)` with no `(f := …)`).
- **Total `eLpNorm`, `Measure.map` and `MemLp`: measurability cascades.** In d13f23b, `eLpNorm f p μ =
  ⊤` off a.e.-strongly-measurable `f`, `Measure.map` of a non-measurable map is a Dirac mass (so
  `IsProbabilityMeasure (μ.map f)` always holds and `ProbabilityMeasure.map ν f` takes no proof), and
  `MemLp f p μ` is just `eLpNorm f p μ < ∞`. Ours: `eLpNorm` is a lower integral; `μ.map f` is 0 for a
  non-AEMeasurable `f` (a measurable *equivalence* has an instance in the compat block);
  `ProbabilityMeasure.map` wants `AEMeasurable f ν`; `MemLp g p μ` is a pair (a bare `lt_top` proof
  needs `⟨hg.aestronglyMeasurable, _⟩`); `MemLp.mul` swapped its factors.
  - *Lemmas false as ported* (oaiq-080): `eLpNorm_add_le`, `tendstoInMeasure_of_tendsto_eLpNorm`,
    `eLpNorm_mono` and lemmas built on them fail here without measurability. No shim fixes this: each
    site needs a measurability fact, and a lemma over arbitrary functions gains a hypothesis that every
    caller passes, up to where the function is concrete (about one cascade per 15 modules, up to three
    levels). Budget build rounds, not single fixes; budget an analysis development at about 12% of
    modules needing a hand repair, a third of them measurability.
  - *An inserted `(hf := by AESM_TAC)` fails:* check whether the declaration has any measurability fact
    for that function. If not, repair the statement, in one of three shapes (q145): add the hypothesis
    its sibling lemma already has and pass it at the call site; apply the lemma to `‖f‖ₑ`, which is
    ENNReal-valued, so `AEMeasurable` suffices (`enorm_enorm`, `eLpNorm_enorm`); or make a widely used
    `def` built by `ProbabilityMeasure.map` of an arbitrary function total as d13f23b is (`if hp :
    AEMeasurable … then … else ⟨Measure.dirac …, _⟩`) with a `…_coe (hp)` lemma.
  - *`MemLp` symptoms* (q146): `And.ne_top` not found (`hf.ne_top` was `LT.lt.ne_top`); `eLpNorm_add_le`,
    `tendstoInMeasure_of_tendsto_eLpNorm`, `eLpNorm_eq_zero_iff`, `summable_norm_of_tsum_eLpNorm_ne_top`
    asking for measurability the generic tactic cannot find ("no goals" or timeouts, worst inside
    `def`s): where its first alternative is a named fact (`exact hf.aemeasurable`), pass that fact
    directly. A lemma *concluding* `MemLp D` for an arbitrary `D` gets a hypothesis its callers supply;
    a `def` built on `μ.map f` for an `f` measurable only in some cases becomes a definition by cases.
  - *The real-valued `Lp` norm* (q136). `lpNorm f p μ` is `if AEStronglyMeasurable f μ then (eLpNorm f
    p μ).toReal else 0`: `toReal_eLpNorm` takes `hf` (a bare `rw [← toReal_eLpNorm]` leaves a side goal
    or makes no progress), `lpNorm_congr_ae` cases on measurability, `eLpNorm_indicator_const` takes
    `MeasurableSet` (the null-measurable form is `…_const₀`), a `MemLp` built from the norm bound alone
    needs `⟨hg, …⟩`. Some lemmas *dropped* the argument instead (`eLpNorm_eq_lintegral_rpow_enorm_toReal`,
    `Lp.eLpNorm_le_of_ae_tendsto`, `Lp.eLpNorm_lim_le_liminf_eLpNorm`). When a port fails on one of these
    names, `rg` the whole port and repair every site at once.
  - *Traps* (q141): an explicit measurability argument placed before the hypothesis that fixes an
    implicit function fixes it first, un-beta-reduced (write it `(by exact …)`). A rule that drops
    d13f23b's leading measurability argument also drops what pinned the implicit `f`: prefer a shadowing
    lemma in `namespace OAI` with d13f23b's signature (`hf` taken and ignored). `whnf` timeouts unifying
    `F - G` with `(fun z => (f-g) z.1) ∘ e` want the equation stated by `funext; rfl`, or the function
    given by name (`(f := fun n x => …)`).
- **Uniform integrability.** `unifIntegrable_iff.mp`/`.1`: ours has no iff (our `UnifIntegrable` is the
  ε-δ, measurable-set, indicator form); a safe special case is `unifIntegrable_iff.mp hf.1` →
  `hf.unifIntegrable`. `UniformIntegrable` has three components here, two in d13f23b (`.1`/`.2` shift).
  The opt-in `UnifIntegrableCompat` shim restores d13f23b's shape.
- **Other drift that needs types or a compat lemma.** `HasGaussianLaw` has one field, `isGaussian_map`
  (drop a constructor's `aemeasurable` component; `HasGaussianLaw.aemeasurable` is a lemma).
  `LinearPMap.ker` and its lemmas are gone (`inverse_graph` and friends take `f.toFun.ker = ⊥`).
  `dite_true` takes only the standard instance. `norm_num` no longer closes a constructor disequality
  of a local `inductive` (`IV.box a b ≠ IV.unk`, not even with `reduceCtorEq`): `nofun` / `⟨nofun, …⟩`
  does (q133).
- **Smaller drift, patched per site:**
  - `A ≤ᵐ[μ] B ∪ ⋃ …` with sets of sets fails to synthesize `Union (Set E → Prop)`: ascribe `(B ∪ … :
    Set (Set E))`.
  - After `filter_upwards` on `=ᵐ` of sets the goal is applied sets (`E x = F x`), not `x ∈ E`: `change
    (x ∈ E ∩ U) = (x ∈ G ∩ U)` / `show x ∈ …` first, `refine hx.trans ?_` for `rw [hx]`, `exact
    iff_of_true … (mem_univ x)` (oaiq-078).
  - A root name Mathlib added collides with OpenAI's under an `open` (`harmonic` with `open Harmonic`,
    `rotation` with `open TraceHessian`): qualify it.
  - A `local instance` whose explicit arguments synthesis cannot infer is now an error: make it a
    `theorem` (it never fired; oaiq-091).
  - `simpa [..] using X` reporting `(f ∘ g) / (f * g)` against a lambda: `exact X` (defeq).
  - Left by the `Fin` rule: a bare `(by norm_num)` on a Fin literal fact (`(190 : Fin 768) ∉ list`):
    `first | decide | norm_num` (oaiq-081); a non-terminal `norm_num` after `fin_cases`.
  - `Finset.sum_le_sum_of_injOn` is gone (`sum_image` + `sum_le_sum_of_subset_of_nonneg`).
  - `decide (G.Reachable …)` under `omit [Fintype V] in` needs `@decide _ (Classical.propDecidable _)`
    (oaiq-089).
  - `liminf_le_liminf (hu := …) (hv := …)` has the two names swapped; `toReal_eLpNorm` and `summable_norm_of_tsum_eLpNorm_ne_top` gained a measurability argument.
  - `List.Pairwise.rel_getElem_of_lt h …` is `List.pairwise_iff_getElem.1 h _ _ hi hj hij`;
    `Nodup.eq_of_getElem_eq` is `(Nodup.getElem_inj_iff …).1`.
  - `exists_contDiff_support_eq_eq_one_iff` is `exists_contMDiff_support_eq_eq_one_iff (I :=
    modelWithCornersSelf ℝ E)` with `contMDiff_iff_contDiff`.
  - `mem_closedBall_zero_iff` on a submodule subtype needs `(E := ↥S)` (oaiq-092).
  - Missing here, declared by patch in the lowest user module: `ModelWithCorners.MfldCat` (oaiq-091,
    a local structure for its one model), `Group.IsVirtuallyCyclic` (q236).
  - `norm_num [table defs]` leaves `vecCons` lookups or `Int.toNat 205` unevaluated where `simp [same]`
    evaluates them.
  - `rw [AddMonoidAlgebra.coeff_zero]` on an `MvPolynomial.coeff` goal is `MvPolynomial.coeff_zero`
    (and `coeff_add`).
  - `tauto` no longer unfolds an applied set-builder membership.
  - `simpa only [ite_true]` does not fire on an `if True` with a non-standard `Decidable` instance: use
    `↓reduceIte` (oaiq-056).
  - `convert … using 1` then per-goal steps: a multi-line `; first | rfl | ring` closes only the first
    goal (use `<;>`, oaiq-045), and bullets can meet an instance goal or a new order (q233, 12 sites;
    q244, q260, q351 in every older-Mathlib source since): `all_goals try with_reducible_and_instances
    rfl` first, `refine Eq.trans_le ?_ (h.trans_eq ?_)`, or state the function and value equalities and
    `rw … at h`.
  - `omit [BorelSpace E]` on a lemma that uses stdGaussian (oaiq-048). `omit [CompleteSpace H] in`
    where our order on `H →L[ℂ] H` needs it: remove only the `omit`s Lean rejects, never all
    (`~/claude/p2m-standalone/openai-ports/oaiq-039/fix_omits_from_errors.py` writes those patches from a
    module's errors).
  - An instance body `by unfold; infer_instance` on a type synonym breaks `simp`/`rw` instance
    matching: `inferInstanceAs` (oaiq-075).
- **"not type-correct under the `implicit` transparency level"** in `rw`/`simp`/`dsimp` (category
  theory, homological algebra; oaiq-032, oaiq-116). Errors full of `simp made no progress` / `rewrite
  failed` on `comp_f`, `ShiftedHom`, `Cocycle`, `single…` lemmas are this check, not API drift. Fix per
  failing module, never as a port default (a header default of `backward.isDefEq.respectTransparency
  false` broke modules that had built).
  - The pipeline's build tries the option itself (f252eeb): a module failing with the transparency note
    is recompiled with it at module scope, and if that builds, its `.olean` stands in so its importers
    build in the same round. The module is still reported failed ("builds only with the transparency
    option … needs a patch", listed in the last line), and the build step stops until each has its port
    patch (`openai-ports/q128-finitistic-retry/add_option_patch.py` writes them).
  - `scripts/try_module.py FILE [--show LINE,...]` compiles a module as is and with the option at module
    scope (pipeline flags, through the lean-cap wrapper) and names the version with fewer errors.
  - Repairs in order: the option as a port patch anchored inside the module before `namespace OAI` (a
    `set_option` inside a namespace ends with it); where it breaks later steps, `set_option … false in`
    per declaration; else `erw` at the failing step; when the option makes `simp` close a goal,
    `all_goals` or `simp only` for the next tactic.
  - `set_option synthInstance.maxHeartbeats 200000` fixed "failed to synthesize … deterministic
    timeout" in 12 modules with one patch. A `Spec` structure-sheaf `Algebra B Γ(Spec B, U)` that fails
    to synthesize wants `backward.isDefEq.respectTransparency.types false` on the theorem (q223).
- **CStarMatrix takes over `*` on Matrix products** (oaiq-092). For a product whose dimensions are still
  metavariables, CStarMatrix's `@[default_instance 100]` HMul wins over Matrix's: `rw [Matrix.sum_mul]`
  fails with `CStarMatrix.inst…` in the error, while `#synth` shows Matrix's instance. `--compat-imports
  narrow` and `attribute [-instance]` do not cure it. Patch the failing module with `attribute
  [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid` after its imports (global; `local`
  is refused). `oaiport.module_texts` can add it to every module naming `Matrix`
  (`matrix_default_instance=True`), off by default: one failure in about 11,000 such modules, and the
  attribute rides along in every bundle carved from them.
- **An `elab` that builds tactic syntax** (oaiq-119, 54 sites): expand it at its call sites by running a
  logging variant in place (build the replacement text, parse and run it, log it), then `mkpatches.py`.
  Traps: restore the message log before logging a failure, count error messages around `evalTactic`,
  `try a; b` is `try (a; b)`, no `pp.oneline`, keep explicit atoms. Budget an hour or two: not a
  blocker.
- **"maximum recursion depth" at a line that looks fine**: the position can belong to a later
  declaration; bisect with `#exit` cuts (oaiq-080).

## Splitting a large ported proof

A port over the 1 MiB cap, or with pieces the 300 s verifier cannot finish, is split by
`scripts/carve.py` (`graph`, `plan`, `gen`, `order`; its docstring has the config). It publishes every
reachable definition in Definitions bundles and promotes theorems to published statements until each
piece fits its budget. It carves by Lean's own command ranges, and each piece renames OpenAI's copy of
its target `<name>_oai`.

### Rules for every carve

- **Never write a per-mission carver.** Five did, and each relearned the same bugs, now tests in
  `tests/test_carve.py`.
- **Fix a carver bug in `p2mlib/carve.py` with a CarveDev test; don't patch it per carve.** A post-carve
  patch is only for a proof fix. Prefer a carver fix to a post-carve patch naming a collision suffix
  (`_r<hex>_<n>`), which breaks silently across snapshots (oaiq-123).
- **Budget**: the timing rule at the top. Bundles and statements freeze at publish and keep a stricter
  limit (see "Measuring and calibrating").
- **Splitting only helps when it removes shared recomputation.** A definition every piece re-elaborates
  costs every piece. Splitting pays when expensive shared material moves into a bundle or a published
  statement that later pieces import; cutting a proof whose pieces all redo the same heavy work only
  multiplies it. When two pieces redo the same generic modules, move those modules whole into
  definitions bundles.
- **Publish concurrently along the DAG.** `carve.py order` prints waves; everything in a wave can be
  published at once when the earlier waves are done (bundles, then statements after their bundles, then
  pieces after the statements they import).
- **Rebuild the port before `carve.py graph`.** DeclGraph reads `.olean`s; a proof repaired in the
  source but not rebuilt reads as `sorry` with no dependencies.
- **Never edit the port's source after the graph is built.** The carver cuts each module by the command
  positions recorded at compile time, so a source edit corrupts every later carve of that module (Erdős
  3). Apply such fixes as post-carve text replacements (config `patches`) to the generated files.
- **No `macro` or `syntax` commands.** The soundness guard refuses them, and the carver refuses to keep
  one. `notation` is fine.
- **The soundness guard's rules are in `p2mlib.leantext.guard_problems`**; `carve.py gen`, `split_run.py`
  and `submit_solution.py` refuse any file the guard would refuse. Add a newly found rule there. Found so
  far beyond `macro`/`syntax`/`prelude`: `TermElabM` (refused, q151; `TacticM`, `MetaM` assumed; 18ce84c),
  `run_tac` (334a816; q227 lost a publish round to it: `beta_reduce` + the same `exact` replaced it),
  and `run_cmd`, `run_elab`, `run_meta`, `modifyEnv` (7bba886: the carver and prune drop OpenAI's
  trailing `run_cmd Lean.modifyEnv … nameDenyListExt.addEntry …` like `#print` diagnostics).
- **`carve.py plan` refuses** a plan in which a bundle misses a definition one of its members needs, or
  in which a bundle or piece rests on `sorry`, or a forced `instance` command (its stub would hold no
  theorem: patch it to `@[instance] theorem` in the port; f480e83, q241). A published bundle is frozen (`frozen` in the config), so a
  later re-plan keeps it as it is.
- **Measure before publishing.** Build every bundle locally (`-j1`), re-pack any over budget, and only
  then publish; never re-carve published bundles while publishing (the first Erdős 3 split did, and two
  published chains re-declared 169 names; archive `p2m-standalone/openai-erdos3-split-v1`).
- **Retries are `p2mlib.verdicts`**: transient failures retry (≤ 30), own timeouts split after 2, CE and
  WA stop for a person. **Local checks are `p2mlib.localcheck`**: it keys each result by content and
  compiles the emulated verifier check (solution, published statement, `theorem _check : type_of% @T :=
  @solution`), which reproduces the locationless WA.
- **Carved pieces** re-activate local instances (`attribute [local instance] x` when the bundle exports
  `x`), avoid tokens full Mathlib adds (`Δ_[1]^[n]` → `Δ_[1] ^[n]`), and drop a theorem a published
  bundle already declares. Config `external_defs`, `statement_suffix` and `patches` support a fresh
  split beside an abandoned one.

### Bundle shape

- **Definitions with proof fields pull the development into bundles** (q257: a structure-valued `def`
  whose fields are proofs made 184 bundles, no statements; 123 published before the shape froze). `plan`
  prints bundled theorem cost against definition cost and warns at 4× and 300 s, listing the entry
  theorems with their chain costs: force the heavy ones before the first publish. On a re-carve, config
  `measured` (an earlier plan plus its times.json) calibrates costs per declaration.
- **Heavy computations do not belong in bundles; publish them as statements.** Eilenberg–Ganea: about
  850 `decide +kernel` lemmas under a *definition* went into 17 bundles of about 58 s; each published
  alone, but every bundle importing several failed with `dependency_oom` ("Failed to compile modules …:
  Lean exited with code 137"), since a cold worker builds the imported bundles in parallel, and
  unchanged retries failed the same way. The fix: `forced` the facts the definition needs (statements
  whose names are ASCII; `pinned` the definitions their statements mention, or the plan has a cycle), so
  bundles import cheap `sorry` stubs and the computation moves into pieces. When such a fact is proved
  from hundreds of per-index lemmas, the planner promotes each to its own statement; add block lemmas
  first, by a port patch that proves the aggregate from blocks (`interval_cases` over a range, then the
  per-index lemmas; `omega` picks the block), and it promotes blocks. Size blocks by the measured cost
  per lemma (30 lemmas at 2.8 s made an 84 s block). Generator:
  `p2m-standalone/openai-ports/eilenberg-ganea-carve/gen_block_patches.py`; fold it into `carve_prep.py`
  the next time a carve needs it.
- **Bundles hold only what definitions need.** The carver keeps a theorem out of bundles unless a
  definition uses it, and drops scopes left without a kept declaration. With
  `bundles_import_statements` (on by default) a forced theorem that definitions need is published as a
  statement its bundles import (prove.md's Platform Imports); otherwise the bundle proves it. **Do not
  use `kernel_lemmas_in_bundles`** (b7749bb, 9047b16), which makes computational leaves bundle material
  (dbenbenn 2026-11-02: lemmas leave definitions bundles freely).
- **Shallow bundles: `"chunker": "schedule"`.** Bands over modules follow the module DAG (163 levels on
  Erdős 3); declaration-level list scheduling gives about 16 for the same material. Depth is what a cold
  verifier pays: a 92-level bundle chain left the first Erdős 3 split's deepest bundles unpublishable
  ("Module compilation timed out").
- **Mixed bundles: `"chunker": "closure"`.** `schedule` puts declarations with unrelated dependencies side
  by side, so an importer pays for chains it never uses (q149: bundle D228 brought 1.64 GB of .olean for
  members needing 0.05 GB). `closure` groups declarations by what they depend on (`closure_slack`, default
  budget/10): on q149 the longest chain fell from 3,433 s to 601 s for 58% more bundles. It does not help
  when the chains are real need (q153: 525 bundles instead of 133 for no gain): keep `schedule` there.
  `plan` prints the heaviest chains and what their members need, and says when the gap is mixing.
- **`gen` stops "OVER 1 MiB"**: emitted bundles ran to 1.7× the planned `bundle_size` (q146). Lower
  `config_set.bundle_size` (450,000 worked). A statement or piece over the cap (a fold into a live
  piece) has its comments stripped by `gen` (4d96885).
- **Universes only under `max`** (oaiq-124): `plan` never makes such a theorem a statement on its own;
  a target or forced statement with one gets a WARNING: fold it, or restate it with every universe bare.

### How the carver reads the port

- **The carver reads what Lean elaborated, not the source text.** `carve.py graph` runs
  `lean/LeanInfo.lean --idents` on each module (`--module M --no-decls`; cached by content under
  `~/.cache/p2m/leaninfo`), at about the module's own compile time. `oai_build_modules.py` compiles each
  module through it (`leaninfo.build_module`), so after a pipeline build `graph` reads the cache and
  takes seconds; a module built some other way (by hand with `lean -o`) is elaborated again by `graph`.
  It records what each identifier token resolved to (`resolved`), the non-library instances used
  (`insts`/`sig_insts`), what instance search solved (`inst_keys`) and notations
  (`declares_kinds`/`kinds_used`); the carver takes dependency edges, renames and `_root_.` pins from
  these. Tokens with no record (a few per carve, inside some `simp`/`simpa` argument lists) fall back to
  a text reading; `graph` and `gen` list them.
- **The same theorem name in two modules** is handled (2ae7988): the copy most modules see keeps the
  name, the others become `<name>_dup<i>`, and `graph`/`plan` list each case (`DUPLICATE …`). No port
  patch is needed.
- **What a carved file brings back.** The carver restores the context its declarations used, on purpose
  over-approximating, so do not hand-patch these: local instances a kept command used (reactivated, or
  re-emitted under a file-unique name) with their siblings in source order; `attribute [-instance]` and
  `attribute [-simp]` (section-local) for global instances and this carve's `@[simp]` lemmas the module
  never saw; the earlier `rfl` simp lemmas a default simp call depends on; coercion instances that
  elaborate away and instances only a `variable` binder needs (no `pinned` groups or
  `synthInstance.maxHeartbeats` patches needed); restricted attributes (`RESTRICTED_ATTRIBUTES`) and
  constant-declaring ones (`reassoc`, `simps`, `to_additive`, …) only in the file holding their target;
  `@[local X]` attributes as `attribute [local X] _root_.N`; pins for short names a dotted declaration
  could misread; `export` blocks that still export something; local instances whose use left no record
  (one of a Prop class such as `Fact (finrank …)` for every kept proof in its scope, and one whose
  class's namespace the source names; 54fdd6c, q221, q237). What it cannot hide (an instance declared
  later in the same module, reached through a bundle) `plan`/`gen` warn about. Not handled: a re-emitted
  anonymous instance's name (`instFactEq…_5`) can collide with the name Lean gave one in an imported
  bundle ("has already been declared"): rename it by post-carve patch (q237).
- **Diagnosing a carved file the carver got wrong.** For "unsolved goals" after `simp` in a bundle, run
  `simp?` at that line in the original module and look for each lemma it names in the bundles. For
  "Invalid pattern" or a type mismatch on a short name, `#check` it at that point of a truncated copy of
  the bundle.

### Failures only in the carved bundle or piece

These never show in the module build of the port (oaiq-085, -086, -087).

- **A `have` that states a hand-written `match`** (`have h : … (match vs with …) …; simp_rw [h]`) breaks
  when the function with the same `match` comes from a bundle: Lean shares a matcher only within one
  module (oaiq-018). Patch the generated piece (config `patches`) with a defeq congruence instead of the
  rewrite. Same for `simp only [hb]` with `hb` mentioning a `match` lambda (oaiq-087): close with
  `change`/`exact`/`refine Eq.trans (congrArg …) ?_`.
- **Two global instances on one carrier** that no OpenAI module saw together ("synthesized type class
  instance is not definitionally equal"): give the one the original module order preferred `priority :=
  high` by patch (oaiq-086; making the other local broke its users).
- **Instance mismatches between contexts.** `Finset.filter` goals differing in `DecidablePred`:
  `congr!`. A `Subsingleton.elim` rewrite of a `Fintype` instance whose direction flips: `first | exact hh
  | (convert hh; all_goals first | rfl | exact Subsingleton.elim _ _)`. `Function.update` with
  `FunLike.toDecidableEq` vs `Classical.propDecidable`: `convert` where `exact` fails.
- **Dot notation on a `def`-typed value** (`ψ.map_zero`, `ψ : Nakayama …`) resolves to a
  `Nakayama.map_zero` the carved file now declares first: write `LinearMap.map_zero ψ` (oaiq-116).
- **A `local notation` written with another local notation** is dropped when the statement is carved,
  while the piece copying the whole module keeps it: scope an insertion patch by its preceding context
  (oaiq-081).
- **A `local instance : Coe …` or `@[local gcongr]` leaves no constant in the term**: a post-carve patch
  inserting `private local instance …` (private, or every bundle holding it declares it again) and
  `exact` in place of the `gcongr` (oaiq-096).
- **A tactic defined by `syntax` + `elab_rules`** (oaiq-076): the port builds, but the carver and guard
  refuse the commands ("unknown tactic"). Replace it at its uses with `iterate N (all_goals first |
  with_reducible exact l₁ _ | with_reducible apply l₂ | … | with_reducible fun_prop | fun_prop)` and
  delete the block by patch. `with_reducible` on each `apply` matters (an unrestricted `apply` times out
  in `whnf`). Test in the carved bundle's context (a scratch file importing `<carve>/olean`), since its
  `attribute [-instance]` lines change what `fun_prop` finds.
- **"failed to synthesize" an instance in a bundle at `measure`**: read `work/repairs.json` first. A
  REPAIR that deleted an `omit`/`include`/`variable` line changes the signatures of everything after it in
  that section, so the error shows in a later file (q139).
- **Test a patch on the stage file** before another re-port and re-measure, and keep the port's module
  compiling too: `LEAN_PATH=<carve>/olean:$(lake env printenv LEAN_PATH) lean -j1 -DautoImplicit=false
  -DElab.async=false <stage file>` (measure's `VERIFIER_FLAGS`; without the last flag a heartbeat
  timeout at `abstract nested proofs` passes, q359) from the workspace, with `~/claude/claude-private/tools/lean-cap` first on PATH (`which
  lean` shows the wrapper; `lake env env … lean` runs the toolchain's lean outside the cap, oaiq-114).
- **Post-carve patches naming `<x>_oai`**: after a re-plan, re-read each; it is right only while `x` is
  still a piece target (oaiq-122). A full `carve.py gen` fails naming a post-carve patch that matches no
  generated file (20365e5).

### The import-edge check

- **`carve_measure.py` checks every import edge, and fails the carve on a false one.** After each file
  compiles, `lean/EdgeUses.lean` lists the constants each import supplies; an import it finds unused is
  confirmed by one compile without it. Checked: every `import Theorems.*`, and a bundle's imports of this
  carve's other bundles. The report `work/false_edges.json` lists each false edge (with the bundle to
  import instead when the statement only brought one in), imports used only by dead code, and
  **orphaned statements** (imported by nothing, neither target nor forced: drop them from the plan).
  Cached in `work/edges.json`. `--drop-false-edges` cuts the false import lines and records the cuts in
  `work/repairs.json`, so they survive `carve.py gen`; `--allow-false-edges` reports without failing;
  `--no-edge-check` skips the check.
- **Unused imports of a definitions bundle are kept** (oaiq-075, 733702b): a later bundle's `attribute
  [-instance]` line can name an instance it sees only through that import. carve_measure reports them,
  and fails or cuts only false edges between statements.

## Running a carve: `scripts/carve_pipeline.py`

**Run carves with `scripts/carve_pipeline.py`, from a snapshot; never write a job-dir driver** (dbenbenn
2026-10-25: a hand-written driver was edited while two carves ran it, and a skill fix pushed mid-carve
mixed old and new `carve.py` inside one carve).

- **The command.** `carve_pipeline.py DIR --folder F --root-module M --target T --bundle-prefix P [--def
  …] [--forced …] [--patches …] [--compat-imports narrow] [--budget N] [--config-set JSON] [--fetch]` is
  the whole module route: fetch, inputs (the targets' published statements and `Def_` bundles, fetched
  into the workspace when missing), filter-patches, port, build, workspace build, config, graph, ext-defs,
  plan, gen, names, order, measure (edge check on), calibrate, publish-prep, prose-template, check-text,
  and a `split_run` dry run (`--publish` adds `split_run --go`).
- **`--fetch`** copies the root's import closure from the local openai/math clone (`~/claude/openai-math`;
  raw GitHub only for what it lacks, with backoff on 429). Never pass a whole openai/math tree as
  `--lean-src`: port and filter-patches refuse more than 50 modules outside the closure.
- **Write `DIR/oai_meta.json` before starting** (title, date, family, full commit, paper URL, `prefixes`;
  `p2mlib/prosetemplate.py` has the format). `prefixes` are `OAI.<top directory>` of the root module
  (what `oai_port_modules` strips, e.g. `OAI.Algebra`), never the result's folder: step `config` refuses
  another value (oaiq-031).
- **Parameters live in `DIR/pipeline.json`**: a different CLI value is refused, so edit the file. A
  changed `config_set` there reaches config.json on the next resume without re-running `config` (which
  would reset calibrate's `time_scale`): `patches` re-runs from `gen`, any other key from `plan`. Editing
  the patches file and resuming re-ports (stale-step detection). `--def` takes `Definitions.Def_X` (a
  bare `Def_X` is read so); `--measure-flag` takes the `=` form (`--measure-flag=--drop-false-edges`).
- **Each step is idempotent**, logged in `DIR/logs/STEP.log` and recorded in `DIR/pipeline_state.json`;
  the first failure stops the run with the log's tail, and the same command resumes. `measure` keeps
  going past a failing file and lists them all.
- **It runs from a snapshot.** It re-execs itself from `scripts/skill_snapshot.py`'s read-only copy of the
  skill at HEAD (`~/.cache/p2m/skill/<sha>/`; `--allow-dirty` snapshots an uncommitted tree) and calls
  every tool from there. A resume stays on its snapshot; `--upgrade` moves to HEAD. Editing or pushing
  the live skill cannot reach a running carve.
- **To change a tool:** change the skill (tests first), commit, push; new runs pick it up, running ones do
  not. A running carve that needs the fix: `--upgrade --redo STEP` (from any snapshot, 1dbb8c1). A one-off
  tool outside the pipeline runs from `python3 "$(scripts/skill_snapshot.py)"/prove2me/scripts/X.py`.
  Shell scripts in the skill keep their body in `main() { …; }; main "$@"; exit`
  (`tests/test_shell_scripts.py`): bash reads a script as it runs, so never edit a running one.

### Detaching, waiting and handing off

- **Run it detached and wait on it.** `carve_pipeline.py DIR … --detach` starts the run as a systemd user
  unit (log `DIR/logs/driver.log`); `carve_pipeline.py DIR --wait 100` returns its status, or exits 4 still
  running: re-arm that. Set the Bash tool's `timeout` above the wait (e.g. 7000000 ms for `--wait 100`):
  without it the harness stops a background command after 10 minutes (q137), and a Bash background
  command dies at 2 h. `--wait` reports only its own run. `--detach` refuses with exit 3, naming the pid
  and command line of a driver that holds the carve: stop that one or wait for it (oaiq-084).
- **Do not wait on a publisher for days.** Each wake of a `--wait` re-reads the agent's whole context,
  since prompt caching does not outlive a 100-minute wait (q172: ~$2.80 a wake for two days). Once only
  waiting is left (step `publish` waiting for its publisher, or hours of statements and pieces), commit
  the records, write a self-contained wrap-up brief, hand the wait to the machine's hand-off service if it
  has one (the brief names it), and exit; a fresh agent does the wrap-up. Keep `--wait` for build and
  measuring, where a failure needs you soon.
- **The carve's own section on the monitoring page.** The driver publishes `carve-<hash>`
  (p2mlib.carvemonitor: step, steps done, modules built, items measured and live, processes), refreshed
  every minute, and marks it done or failed with the reason; `split_run --go` keeps the counts current
  while a background publisher outlives its driver. A worker's own section need not repeat any of that.
  A carve on an older snapshot shows no section until it is resumed with `--upgrade`.
- **`gen` is silent for hours** on a few thousand nodes (q154: 3.5 h, out/lib count still, 95–100% CPU):
  not a hang. A watcher on a carve's logs must not match `rror`, since calibrate's "no systematic error"
  line contains it: use `Traceback|FAIL|Killed`.

### What re-runs after `--upgrade`

- **Port rules.** `port` and `filter_patches` record the rules and options they ran with, so a skill fix
  to a port rewrite re-ports without `--redo port`; a re-port that changes no module's text rebuilds
  nothing. filter_patches' rule input is carve_prep.py's filter-patches code only.
- **`--keep-port`.** A carve that has planned and measured takes new tools with `--upgrade --keep-port`:
  the port stays as it is across rule changes, on that run and every later one, until `--redo port` or
  `--redo filter_patches` (`pipeline_state.json` `keep_port`). Every plain `--upgrade` of a built carve
  re-ports (oaiq-098: two 11-hour rebuilds, the second only to pick up a planner fix).
- **Compat changes rebuild everything.** An unchanged port replays (the build depends on nothing of the
  snapshot), but a changed `lean/compat_4_34.lean` rewrites `Compat.lean`, which every module imports
  (oaiq-088). The driver warns when a re-port would do that; on a built carve use `--upgrade
  --keep-port` unless the new shims are needed (df97e19).
- **Once publishing has started** (`pipeline_state.json` `publishing_started`, set the first time
  publish or publish_early runs or `publish/run_state.json` or config `frozen` is seen, and kept), a rule
  change keeps the port: `--redo port` only deliberately. A changed input from outside (an edited patches
  file, a port folder rewritten under the carve) stops the run until you `--redo` that step. The guard
  hashes bytes: a patches file re-serialised by a JSON library counts as edited (q241; restore it with
  `git show`).
- **LeanInfo and graph.** A change to `LeanInfo.lean` re-runs `graph` (with a warning giving the module
  count) while a step that loads the graph is still to run, and re-elaborates the whole graph. A graph
  recorded before a DeclGraph change is re-run after `--upgrade` while planning is ahead; a published carve
  keeps its graph. A `config.json` that `--redo config` changed re-runs from `extdefs`.
- **A private snapshot for one tool fix.** A large published carve that needs one tool fix takes it on a
  private snapshot, `--snapshot <commit>`, rather than a HEAD that also changed LeanInfo or the compat
  sources. q145's recipe: `git commit-tree` of HEAD's tree with `prove2me/lean/` taken from the carve's old
  snapshot (built in a temporary `GIT_INDEX_FILE`), kept under a private ref such as `refs/q145/snap` and
  never pushed. `--snapshot REV` wins over `--upgrade` (43a23e2).
- **Carver changes.** `gen` records the carver code (`p2mlib/carve.py`, `scripts/carve.py`,
  `p2mlib/leantext.py`): until publishing starts, a carver fix re-runs `gen` on `--upgrade`; after that,
  `--redo gen` deliberately. Editing the post-carve patches file re-runs `gen` (dad2e72), and a `gen`
  whose output changed makes `measure` / `measure_pieces` and every later step stale, also after
  publishing (a3c96b5).
- **Module times.** A rebuild keeps the replayed modules' times in `build_elab.log`. A carve built before
  2026-10-29 can lack most of them (each then costs a default 2 s): `--redo build` once before planning it
  again.
- **Measure cache.** A kinds-limited `measure` judges only its kinds' edge records, and a cached ok is
  reused only while its `.olean` exists and is whole, so a repair cut needs no `times.json` edit
  (17b6d76); after a crash, `carve_resume.py` deletes the broken `.olean`/`.ilean` under `olean/`
  (1b2b1bc; q172's power cut left 33 empty files the resumed driver trusted).

### The port folder has an owner

- The port writes `WORKSPACE/Solutions/FOLDER`, outside the carve dir (a copy of a carve on the shared
  workspace once rewrote 228 files of the live carve's folder). `Solutions/FOLDER/.carve_owner.json` names
  the owning carve directory, and the driver refuses before any step when the folder belongs to another
  carve, config `out`/`work` lie in another carve, or config `src` is not the run's workspace.
- A folder without an owner file is adopted by the carve whose recorded port hash it holds, when its
  `logs/port.log` names no other carve; otherwise use `--claim-folder` (also to take a folder over on
  purpose, e.g. an extension carve on its parent's port). A moved carve keeps its folder.
- **To rehearse:** copy the carve, point every absolute path in the copy's `pipeline.json` and
  `config.json` (`out`, `work`, `meta`, `patches`; `src` at the new workspace) at the copy, and run it with
  `P2M_WORKSPACE` set to a workspace of its own holding the folder (and its `.lake` build) as copies;
  never on `~/claude/prove2me_workspace`.

## Measuring and calibrating

- **The cost model is calibrated by the measurement, automatically.** `calibrate` (after `measure`) takes
  any unfrozen item measured over 1.6 × budget, sets `time_scale` to scale × (measured seconds / planned
  cost), re-plans, re-generates and re-measures (unchanged files cached), at most twice, and stops with
  the offenders listed (then `carve.py split` or a manual `time_scale`). Never publish before it passes.
  It only raises the scale: the per-item error is 0.3–1.4× even at a fitted scale (over 27 carves,
  per-carve medians of measured/estimate ran from 0.56 to 1.34), so trust the measurement, never the
  estimate. Outside the pipeline the manual rule is the same: measure everything (`carve_measure.py`),
  and if any bundle or statement is over 80 s (`BUNDLE_OWN_LIMIT`), multiply `time_scale` by the worst measured/planned ratio
  and plan again, or `carve.py split` from the times.
- **Pieces are judged by `PIECE_CAP`.** A piece measured under 100 s never counts as slow: it is a
  resubmittable proof, so submit it as is. Bundles and statements freeze at publish and keep the strict
  limit. When only pieces are over, re-planning does not help (it re-splits bundles but has never shrunk
  a piece): force the heavy lemmas the piece keeps into statements (`forced` in pipeline.json; a private
  one by its graph node name, `_private.<module>.0.<name>`, published without the prefix) and resume
  `--from config`, or let overlap mode split it alone.
- **Unpublished bundles are over at 80 s local** even when the budget allows more (`BUNDLE_OWN_LIMIT`,
  17a5cac): q172's data bundles at 83–88.6 s hit the server's own 300 s timeout.
- **Memory, separately from time** (q153). The verifier's workers kill a file whose Lean peaks over
  about 7 GiB; `import Mathlib` alone peaks at 6.5 GiB. carve_measure records each run's peak
  (`rss_mib`). A piece over `PIECE_RSS_LIMIT` (7,150 MiB; pipeline.json `piece_rss_limit`) is split alone,
  into enough parts for the proof's share (its peak minus its statement's) to fit, with two exceptions
  that are sent once as they are: a piece listed in `try_over_memory`, found unsplittable, or at most 5%
  over once splitting stops shrinking it (`near_memory`, pipeline.json `try_near_memory`; q334), and a fast
  piece a little over (at most `TRY_UNSPLIT_RSS` 8,600 MiB and `TRY_UNSPLIT_SECS` 20 s) that imports at
  most `TRY_UNSPLIT_IMPORTS` (120) statements; q153 had all 331 pieces over 7,150 MiB accepted, each
  importing at most 119. A memory kill (verdicts `hidden`/`dependency_oom`) puts a piece in state `split`.
- **Many imports are their own memory cost** (q154 `GramData.Block3.gram`, 2026-11-10): the verifier
  replays every imported module, which the local peak under-counts. `gram` imported 709 entry statements
  and was killed four times at ~7,450 MiB, and each split only made it import more. A piece like that
  needs its imports grouped under a layer of intermediate statements (rows of a matrix, say), not a split;
  calibrate_pieces says so when it stops for a person. The same flat shape cannot be cut by forcing
  mid-chain lemmas either. Before publishing, add the row lemmas by port patch and force them with
  `config_set.template_forced`; after (an edited patches file is refused), publish the rows by hand with
  `publish_standalone.py`, each proved from its entries and the aggregator from the rows, submitted with
  `submit_solution.py --carve DIR` for imports only the carve holds (q172: 27 rows
  in about an hour, all accepted first time).
- **Kernel computation is invisible to the cost model** (`decide +kernel`, `native_decide`) and is the
  usual cause of a slow item: see **Kernel time** under "Slow or odd failures".
- **`accept_over`** in pipeline.json excuses an item (`bundle:NAME`, `piece:NAME`) under a 200 s cap. For
  a bundle a few seconds over that few items import it is the cheap exit; a split round costs a full
  `gen` plus a re-measure (q154: about 8 h). Calibrate warns when an excused bundle gates 5 or more items.
- **A slow bundle in `calibrate`:** if at least three bundles and a quarter of the measured ones are over
  (a systematic cost-model error) and nothing is published (no publishing started, no config `frozen`),
  calibrate re-plans globally at a larger `time_scale`. Otherwise each slow bundle is split alone
  (`carve.py split CONFIG TIMES --limit BUDGET --only NAMES`, up to three rounds): every other bundle keeps
  its declarations, name and imports, so only the split one's importers change and are re-measured.
- **Calibrate stops on a bundle splitting cannot shrink** (df97e19): one declaration, or unchanged by a
  split round. It profiles each such bundle once (`carve_measure.py CONFIG --profile bundle:NAME`;
  `work/profiles.json`, `work/profile_<name>.log`) and stops naming the declaration: serialization-bound
  (name the type's large sides with `abbrev`s by post-carve patch, oaiq-124), kernel-bound (rewrite it, or
  `cost_factors` + `accept_over`, oaiq-092) or elaboration-bound.
- **A slow piece in a classic carve**: when three or more pieces are over the plan by a similar factor
  (median ≥ 2.5, spread ≤ 2×), calibrate re-plans at that ratio by itself (oaiq-073). A lone slow piece,
  or a scatter, stops it with a profiling hint: follow "Slow or odd failures".
- **Slow pieces made of private lemmas are not a cost-model error** (q143): read as a uniform overrun,
  they re-planned oaiq-091 twice (time_scale 1.2 → 5.6) while the same pieces stayed over. Restore the
  first `time_scale`, add their private `keep` entries to `promote_private` (`config_set`) and re-plan
  once. On a retry, check whether a carve re-planned more than once was over on the same pieces every
  round. The automatic split of a slow piece promotes private lemmas itself (config `promote_private`,
  graph node names).
- **One wild reading is the machine, not the piece** (q138: 1,595 s for a piece that compiles alone in
  2.2 s, measured while Lean held all its swap). `calibrate_pieces` measures an over-limit piece once
  more before splitting it (f5d1875); by hand, re-time a lone outlier with `lean -j1` and the carve's
  `olean/` ahead of LEAN_PATH (the toolchain's `lean` directly: `lake env` resets LEAN_PATH).

### Overlap mode: bundles and statements publish while the pieces are measured

On for every carve created since 2026-10-29 (`pipeline.json` `"overlap": true`, written at the first run;
`--no-overlap` to opt out). A `pipeline.json` without the key is a classic carve and stays one,
`--upgrade` included. The steps: `measure` (`--kinds bundle,statement`), `calibrate` (those only),
`publish_prep`, `prose`, `check_text` (`--kinds bundle,statement`: written prose for forced *statements*
is needed now, explanations later), `dryrun` (`publish/run_early.json`), `publish_early`,
`measure_pieces`, `calibrate_pieces`, `pieces_prep` (publish-prep `--sync`, prose-template, check-text of
the explanations, the full dry run), `publish`.

- **`publish_early`** (only with `--publish`) freezes what it publishes: `DIR/published/` keeps the plan
  and lib files, and config `frozen` (that plan, its bundles, `published/lib`), `forced` (its statements)
  and `template_forced` (those not named in `forced` by you) are set, recorded in `pipeline_state.json`
  `auto_config` and re-applied whenever config.json is rewritten. It then starts the background
  publisher, `split_run.py publish/run_early.json --go`, as systemd user unit `carve-pub-<hash>` (output
  `logs/publish_early.log`, progress `publish/PROGRESS.log`). Pieces are held by the gate
  (`publish/release.json`, see p2mlib.splitrun) until released for exactly this plan. `split_run --go`
  holds a lock per `publish/`, so a second publisher exits 3 while the background one runs.
- **A failure after `publish_early`** (a piece that does not compile, a missing explanation, a slow
  piece) stops the driver and the publisher goes on; `--wait` and the failure message say so. Fix and
  resume as usual. Steps that write `publish/` sync it (atomic file replacement), never rebuild it, and
  stop if a published bundle or statement file would change (`gen` checks the same right away).
  `publish` writes the release, waits for the background publisher to end, then runs the final
  `split_run publish/run.json --go`, which resumes.
- **A slow piece** in `calibrate_pieces` (dbenbenn 2026-11-06): a uniform overrun of several pieces while
  nothing is published re-plans at the ratio. Otherwise each piece over the limit is measured once more,
  then split alone: `carve.py split-piece CONFIG NODE=PARTS` (PARTS = measured s / budget, at least 2)
  promotes lemmas the piece keeps into new statements until each part's planned cost is 1/PARTS of the
  piece's, regenerates only that piece and the new statements and pieces, and the run goes on from
  `names` (no `plan`, no full `gen`, every other measurement cached). The new statements join auto_config
  `forced` and `template_forced`. A piece the publisher stopped after own verifier timeouts (state
  `split`) is halved the same way, up to `MAX_PIECE_SPLITS` times, only while its file is still the text
  that stopped. By hand: `carve_pipeline.py DIR --split-piece NODE[=PARTS] --publish --detach`. It stops
  for a person when a piece is still over after its split, or its statement alone takes half its time
  (the type is the cost: `abbrev`s cannot be added to a live statement; `theorem _root_.solution` halves
  the serialization). Remedies then: `accept_over` (`piece:NAME`, under 200 s), `--split-piece` with more
  parts, or forced lemmas. This replaced a frozen global re-plan (config `cost_factors`), which for q153's
  four slow pieces changed the text of ~2,000 others and cost a day.
- **Streaming** (with `--publish`). `measure_pieces` measures `STREAM_BATCH` (64) pieces per
  `carve_measure --only` run and releases each batch's pieces within the limit at once
  (`publish/release.json` with `open`: the publisher keeps waiting for more while it is open and under 2 h
  old), so verifier feedback arrives within the hour. The pieces bundles wait for (a bundle importing a
  statement publishes only once it is Proved) and those of held (new) statements go first; held
  statements are published as soon as their pieces pass. `measure` streams bundles and statements the
  same way: batches in publish order; after the first `STREAM_SAMPLE` (20) bundles, `publish_prep`,
  `prose` and `check_text` run once, and each batch's items within calibration's limits (and the 160 MB
  import limit unless `accept_heavy_imports`) whose own bundles and statements went first are frozen as
  they go (`published/plan.json`, `pipeline_state.json` `streamed_stubs`) and listed in `release.json`
  `items` for the streaming publisher (`publish/run_stream.json`, `gate_items`). A systematic overrun while
  nothing is published releases nothing (calibrate re-plans); a slow or heavy item stays back with its
  importers for calibrate to split alone. `--no-stream-bundles` (pipeline.json `stream_bundles: false`)
  keeps the old order.
- **Switching a classic carve** that has not published (oaiq-081): wait for its driver to end
  (`--wait`), add `"overlap": true` to `pipeline.json`, then `carve_pipeline.py DIR --upgrade --keep-port
  --publish --detach`. A finished `measure` stands, the plan is kept, and the run goes on from the
  phase-1 `calibrate`. If the classic driver got past `publish_prep` with no `publish/run_early.json`, add
  `--redo publish_prep`; `publish_early` refuses without that file.

## Slow or odd failures: what to try first

Profile before forcing or splitting anything.

- **1. Serialization.** `lean -o x.olean -Dprofiler=true FILE` (with
  `LEAN_PATH=<carve>/olean:$(lake env printenv LEAN_PATH)`). Profile the `chk/` file whose name matches
  the current plan: earlier plans' files stay there (oaiq-078). If `.olean serialization` dominates while
  elaboration is fast (oaiq-075: 316 s of 328, `sorry` just as slow), the statement's *type* is huge:
  print `Expr.sizeWithoutSharing` per binder (`forallTelescope` in a `#eval show MetaM Unit`) and of the
  body. Only declaration *types* cost; the same term in a proof or a definition's value is cheap.
  - Remedy: `abbrev`s naming the large sides or subterms, in a bundle (in the same `attribute
    [-instance]` context as the stubs), and the statement restated with them; its piece starts with
    `unfold` of them, and importers still work (even `with_reducible exact`). When the large part is the
    conclusion under binders, name the *whole conclusion* as a `Prop`-valued `abbrev` taking the binders
    (q140: serialization 316 s to 0.4 s; an `abbrev` of the subterm alone only halved it). Give the
    `abbrev` a type ascription and copy every instance binder the statement has (`[IsClosed (B : Set
    _)]`), else importers stop matching.
  - Where the type cannot shrink (a frozen statement), declare OpenAI's theorem directly as `theorem
    _root_.solution` instead of `<name>_oai` plus a `solution` copy: it halves the serialization.
  - The same holds for bundles (oaiq-124: 92 s to 55 s with an `abbrev` in the same bundle).
  - A *statement* over the limit stops calibrate: it publishes, but every verify that imports it times
    out compiling it. Never `forced`: the item is already one small proof.
- **2. A slow tactic.** `lean -Dtrace.profiler=true -Dtrace.profiler.threshold=20000 FILE` names the slow
  tactic with its position; plain `-Dprofiler` gives only the cumulative "type checking" (oaiq-074: a
  53 s `fun_prop` goal, fixed by `Real.continuous_exp.aestronglyMeasurable` as a term). Cheap gains
  (q159): explicit-function `comp_left` terms, explicit terms for `nlinarith`/`positivity`.
- **3. Many small lemmas, no heavy declaration.** Force two or three mid-chain theorems (`forced`, chosen
  by transitive-closure size at about 1/3, 1/2, 5/6 of the total; oaiq-074). For chains of `decide
  +kernel` theorems, force every kernel theorem the piece keeps, or an evenly spaced fraction
  (`~/claude/p2m-standalone/openai-ports/oaiq-047/resplit_prep.py`; oaiq-047, -084: 97–186 s pieces
  became 85–97 s and all passed), and in a kernel-heavy carve do it at the first plan rather than after
  the verifier's timeouts. Big carves take time: a 1,300-module carve took about 20 driver restarts and
  two days (oaiq-050).
- **Kernel time.** `lean -Dtrace.profiler=true -Dtrace.profiler.threshold=4000 FILE` prints `[Kernel]
  typechecking declarations [X]` lines (oaiq-092: single declarations at 23–474 s, which no bundle split
  can fix). Rewrite the heavy declaration by patch (state the function up front instead of leaving the
  kernel to unify it), else `cost_factors` + `accept_over`. Kernel pieces are load-sensitive: profile any
  kernel piece over ~30 s. In a kernel-heavy development, force the source's own block or merge lemmas at
  the first plan (oaiq-114).
  - A `decide` on `Finset.card` or Finset equality over a long `List.toFinset` is quadratic in the
    kernel. For a sorted list, prove `Nodup` from a strict chain (`List.IsChain (toLex · < toLex ·)` by
    `decide +kernel`, `List.isChain_iff_pairwise`) and use `List.toFinset_card_of_nodup` (85 s to 0.3 s).
  - A flat certificate chain (one aggregator over many `fin_cases` leaves): **Many imports are their own
    memory cost** under "Measuring and calibrating".
- **A slow, memory-heavy piece with a short tactic proof** (oaiq-123: 281 s, ~22 GiB): compile it with
  `set_option debug.skipKernelTC true in` on the theorem. If that makes it fast, the kernel is
  re-evaluating a certificate term a cheap `simp` left behind: rewrite the cached-value lemmas in before
  any arithmetic `simp`. On a loaded machine bisect with `sorry` truncations under `timeout 300`, not the
  profiler.
- **Kernel-bound in one or two terms**: a piece under the limit locally that times out on the verifier,
  elaboration a few seconds and the rest "type checking" (q131). Bisect with `sorry` truncations, two
  variants at a time; splitting cannot help. Try these in a scratch file with `trace.profiler` before
  `cost_factors` + `accept_over` (replacing `rfl` by `simp only` does not help: the kernel checks the same
  defeq):
  - A generic lemma about `compiled c` applied to a constant (`highLoop`) defined as `.seq A B`, with
    hypotheses proved for `compiled (.seq A B)` (q131): move the step into a local `have generic : ∀ {c
    first second …}, c = .seq first second → … := by intro …; subst hceq; exact …` and apply it as
    `generic (c := highLoop) rfl …` (134 s to 0.07 s; no declaration added, plan unchanged).
  - `Procedure.comp` typed `… (g ∘ f)` with a *named* `g` makes lazy delta unfold `g` first (q144): a
    local `compBeta q p : Procedure ea ec (fun a => g (f a)) := q.comp p`, used as `let p := compBeta …;
    exact p` (376 s to under 1 s).
  - An `rfl` between projections of a tuple and of a variable (`delta (T).1 (T).2.1 … = delta (6*x.1) W
    x.2.2.1`): a generic `rfl` lemma over variables, instantiated at the tuple's components
    (`deltaFn_apply (r W G N) : (fun x => delta x.1 x.2.1 x.2.2.1) (r, W, G, N) = delta r W G := rfl`,
    then `….congrFun (fun x => deltaFn_apply …)`).
- **`(kernel) deterministic timeout` where the elaborator accepted every step** (oaiq-068): typically a
  goal equating `f a i₁` with `f a i₂` for two proofs of a Prop-valued instance argument. State the
  irrelevance as a lemma, `@f … i₁ = @f … i₂ := by cases Subsingleton.elim i₁ i₂; rfl`, and chain with
  `.trans`. Bisect by `sorry`-ing the tail of the proof (about 40 s a trial; three variants in parallel).
- **Certificate ports: `decide +kernel` lemmas** (oaiq-098, q152). `carve.kernel_weights` adds the size
  of what a `decide`/`native_decide` declaration names to its cost (9cc6f1c), and a re-plan (`--from
  plan`) splits such bundles itself: don't force each lemma. `promote_shared` (90a79b7) promotes a theorem
  whose extra copies, cost × (pieces keeping it − 1), reach one piece budget: use it when pieces sum to
  several times the build time. Never `kernel_lemmas_in_bundles` ("Bundle shape").
- **Closure chains and closure bytes.** A cold verifier worker builds an item's whole import closure. On
  q152, closures grew along the publish order to ~10,000 s of local compile, the bundle rate fell from
  159 an hour to about 10, and D297 ended `dependency_oom`, though every bundle measured under 90 s. When
  bundle publishes slow down or time out, re-plan the unpublished part with its lemmas as statements (the
  live bundles `frozen`) instead of pushing it through. `plan` and `check` give each heavy chain a verdict
  against the 300 s cold build, and calibrate warns on measured chain sums over 150 s (17a5cac). It also
  sums each item's local seconds over its whole closure, warns over 1,000 s, and before the first publish
  stops on such an item that also imports over 160 MB (pipeline.json `closure_stop`, `closure_limit`):
  q257's `tr` failed there at 1,294 s, while light-import items elsewhere went live up to ~2,200 s. Closure
  *bytes* look like a second ceiling (q149, oaiq-106: every published bundle's closure was ≤ 0.74 GB of
  .olean; above 0.87 GB, "Module compilation timed out after 300s" every time). That is one carve's
  correlation, not a platform-stated limit; `carve_measure.py` warns over 0.7 GB. A goal piece that must
  import the whole development (several GB) is blocked by the platform, not by drift: say so in RESUME
  rather than retrying.
- **The CoeT WA: "failed to synthesize CoeT … timeout at `typeclass` (20000)"** (opus-kadison, oaiq-039,
  q129). For some polymorphic statements the verifier's plain type comparison fails and its `CoeT`
  fallback times out on a heavy type. The local check runs that fallback (19c7a63), so carve_measure
  reports such a piece. The cost is the type's unshared size (q129: 18.9M nodes failed, 8.5M passed);
  COE_CHECK prints `sizeWithoutSharing` (facecb3). Remedies, in order:
  1. **Shortcut instances** for the carrier's algebraic classes, in a bundle the statement imports (a
     post-carve patch): `instance (priority := high) q129Monoid : Monoid (TracialQuotient τ l) :=
     inferInstance`, plus `StarMul`, `Ring`, `Algebra ℂ`, …, in a `noncomputable section`. q129's
     statement fell to 2,613 nodes. Try them in slow pieces of the family first (pieces are not frozen):
     they cut three pieces' kernel time from 306 s to 170 s.
  2. **State it monomorphically** if every importer is. Config `monomorphic` (18ce84c) writes the listed
     statements and their whole pieces at universe 0 (`carve.monomorphize`) and `solution` without
     universe parameters, so the fallback never runs; when the goals are stated over `Type`, prefer it to
     folding (q151). Keep the set consistent: a live polymorphic statement's piece needs its imports
     polymorphic (fold the CoeT ones among them); every other CoeT statement and its unpublished
     importers up to the goals go in `monomorphic`, with the pieces of live `Type`-only importers. Compute
     it on the folded plan and iterate (folding changes imports); q151's script is in its RESUME.md. Set
     it before the first publish: `gen` stops if it would change a frozen stub (b8be844, q240).
  3. **Fold, last** (folding makes the importers' pieces slow). `carve.py fold CONFIG NODE…` (config
     `folded`) folds the statement into every importer's piece, whose live statements stay; only those
     pieces are resubmitted, through split_run with a `comparisons/` note on each, since the old sketches
     are live. Fold the whole CoeT set at once (q240: one fold at a time promoted new polymorphic
     statements in the importers each round), and deprecate the folded statements that went live
     before the fold once the carve is done; they stay Open orphans otherwise. Regenerate pieces of a published carve with the carve's own snapshot (pipeline_state.json
     `snapshot`): a newer carver emits more `attribute [-instance]` lines than the frozen stubs have. A
     re-plan with a snapshot older than 19c7a63 drops the fold.

  CoeT failures come in families: after `measure_pieces` fails, list every FAIL of the run (`awk
  '$1=="piece" && $4=="FAIL"'` from the run's `====` line) and treat them together (oaiq-122).
  **Pre-screen split points on a CoeT-prone family** (C*-algebra or Hilbert-space towers; q160): before
  the first `--publish`, read every candidate's `Expr.sizeWithoutSharing` with `#eval` from one Lean file
  importing the built port (it equals COE_CHECK's number). Every failure was ≥ 2.6e7 nodes and every pass
  ≤ 3.2e6 (q129: 1.9e7 failed, 8.5e6 passed): put every theorem over 1e7 in `config_set.no_promote`. A
  re-plan's new statements wait for `measure_pieces` (its CoeT check) before the publisher posts them
  (2f6bb06).
- **Platform lexer timeouts** ("Token scanner timed out after 10s", "Import parser timed out after 5s")
  are platform load and retried automatically (2675af1). An item an older snapshot stopped:
  `split_run.py publish/run.json --go --reset statement:NAME` once (oaiq-089).
- **Heartbeat timeouts on the server.** A bundle or piece that compiled in `measure` can still hit the
  verifier's `maxHeartbeats 200000` (oaiq-055: `rfl` lemmas, instance-heavy statements). split_run adds
  `set_option maxHeartbeats 1000000` after the imports and resends once (updating the frozen
  `published/lib` copy, 4b230e3); a second failure waits for a person. See verifier-failures.md, "A
  heartbeat timeout the local build never shows".

## Publishing

- **Before publishing:** `carve_prep.py publish-prep`, then `carve_prep.py prose-template DIR`, then
  write by hand only what it lists as "needs written prose", then `carve_prep.py check-text` (the
  pipeline runs these). check-text checks the explanation rules, that every backticked name exists, and
  that no stub contains a comment. So write bundle names in full: a backticked prefix such as
  `` `OAIQ030L…` `` is NOT FOUND; write "OAIQ030L000 to OAIQ030L035" without backticks (q137). Credit
  OpenAI and the result family in every description and explanation.
- **Template prose for intermediate items; written prose only for the goal and the forced named
  results** (dbenbenn 2026-10-24). `prose-template` makes no model call. From the plan, `publish/out/`,
  `work/decl_graph.jsonl` and `DIR/oai_meta.json` it writes each statement's prose (the OpenAI credit,
  the GitHub link to the declaration at the commit, the published Lean, the declarations Lean records it
  using, which items import it), each bundle's prose (declarations by kind, modules, imports both ways),
  and each piece's explanation in prove.md's form, with no mathematical claim the Lean does not show. It
  skips the goal and every `forced` node and lists them as needing written prose. Generated files carry
  `template:` in their front matter and a sha1 in `.template.json`; a rerun regenerates only unchanged
  templates and keeps written prose unless `--force`. `bundle-prose` (a hand template) remains for a
  carve that wants written bundle prose. Fenced code blocks are code to `check-text` and
  `check_pronouns.py` (a binder `he` is not a pronoun).
- **Missing prose stops `check_text`**: the "needs written prose" lines name the files to write, and
  check-text and the dry run fail (MISSING / CANNOT BE SENT) until they exist, in any wave (eafc6da). In
  overlap mode write the forced statements' prose before starting, and the goal's and forced pieces'
  explanations while the pieces measure.
- **A patch `why` lands in the piece's explanation**: write Lean names in it in backticks (oaiq-064: a
  hypothesis `he` failed the pronoun check), except a lemma our Mathlib lacks (a d13f23b-only
  `Measure.prod_apply₀`), which check-text looks up and stops on (`mkpatches.py` refuses such a `--why`
  up front, 07a30df; q243 met it after hours of measuring). Once publishing has started an edited
  patches file is refused, so fix the text by hand in the generated `publish/explanations/*.md`, which
  the template keeps (q146).
- **The `names` step**, right after `gen`, looks every planned bundle and statement up (read-only, a few
  minutes) and stops on one live with other text, before the hours of measuring (oaiq-068): then a
  `statement_suffix` and `--from plan`, or extend the earlier carve ("After publishing").

## After publishing: re-splitting, extending, overlapping carves

- **Overlap-mode carves freeze themselves.** Once `publish_early` ran, config `frozen` and `forced`
  hold the published plan, bundles and statements (`pipeline_state.json` `auto_config`), and a slow piece
  is split alone automatically ("Overlap mode"). Only what is published or being published is locked
  against change (`carvepipeline.locked_files`, 955adf7). The recipes below are what that automates; they
  remain the way for classic carves, for a piece the automation hands back, and for real verifier
  timeouts. Statements the early-publish plan wrote into `published/lib` but never sent are locked too, so
  `gen` keeps their old text: with no publisher running, move the unposted ones out of `published/lib`
  (keep a backup) before the `gen` that should change them (q151).
- **Splitting one stopped bundle by hand after publish_early** (q172, 17a5cac):
  1. Let the publisher end, or (on a HOLD from a worker) stop it and the driver: a running publisher
     locks every unsent item of its plan.
  2. `carve.py split config.json work/times.json --limit 55 --only X`. When the parts form a chain, the
     top part keeps the name X and no importer changes; otherwise the tool writes the changed importers
     into `pipeline.json` `thaw`. The old plan is kept as `work/plan.pre_split[.N].json`.
  3. Copy `out/lib` aside, then run `carve_pipeline.py DIR --upgrade --keep-port --publish --detach` (add
     `--redo gen` for a carve last generated before 301958e).
  4. Diff out/lib against the copy: only X, the new parts and any thawed importers may change. A posted
     importer cannot change, so that case needs a re-plan.
  5. split_run sends X again by itself, since its text changed after it stopped.
- **Re-split one item after real verifier timeouts** (two or more on a bundle or piece). Keep everything
  live as it is: in `pipeline.json` `config_set`, set `frozen` = {`plan`: a copy of the published
  plan.json, `bundles`: every live bundle, `lib`: `publish/out/lib`} and `forced` = the live intermediate
  statements plus the new ones you want (without the live ones the planner re-chooses intermediates by
  cost, dropping live statements: oaiq-071). Then `--publish --detach`: `--publish` always re-enters
  split_run, and an item stopped for a person whose file changed since is sent again by itself. `gen`
  needs each frozen bundle in `Definitions/`: `fetch_theorems.py --names Definitions.Def_X` (or the bare
  `X`). `prose-template` skips `forced` nodes; for a mechanical split, generate the prose on a scratch
  copy with `forced` emptied and copy the files back.
- **A re-plan only reshapes what is not live** (q160, 2f6bb06). The automatic re-plan writes config
  `no_promote` = the keeps of live pieces less the slow pieces' (plus `config_set.no_promote`, ed0d656).
  Once publishing has begun, `plan` refuses a plan whose new statement is imported only by live pieces,
  since split_run never resends a live piece without a comparison note and the statement would stay an
  Open orphan (remedy: `no_promote`, or a `comparisons/` note to resend that piece). A hand re-plan after
  publishing: diff the new pieces against `publish/plan.json` first.
- **Post-carve patches on frozen files.** A frozen item the run state shows stopped (not live) takes
  post-carve patches (3dc33a3): the driver lists such files in config `frozen.thawed`, gen generates them
  with the patches, and their `published/lib` copy follows. On older snapshots edit `out/lib`,
  `publish/out/lib` and `published/lib` identically. A patch whose only match is a live frozen file fails
  a full gen ("PATCH ON A FROZEN FILE ONLY"). On a snapshot before a3c96b5, patched pieces never reach
  `publish/out`: resume with `--from measure_pieces --publish --detach` and `rg` the new text in
  `publish/out` (q131).
- **Frozen bundles keep their old plan's imports** (20365e5), and `check_plan` no longer reports their
  inferred needs or cycles unless the frozen carve used another external bundle
  (`frozen_external_conflicts`). A plan from before 20365e5 recomputes frozen bundles' imports: after
  `--upgrade`, `--redo plan` (plain `--upgrade` keeps the old plan).
- **After renaming published items, dry-run split_run first** (q151). Config `statement_suffixes`
  (f42edbc) renames live statements; an item is sent again when the name it was sent under changed
  (e4d2383). Still run `split_run.py RUN.json` without `--go` after any rename, check the renamed items
  appear under "would send now", and stop a publisher running an older snapshot. Platform 5xx answers
  (Gateway Timeout, "Verification service error") are transient (69c9fd3); pieces stopped that way on an
  older snapshot need `--go --reset piece:X`.

### Extending a carve

- **Extending a published carve** (a new statement after the first bundles are live) is the normal path:
  a second carve with the live bundles under `frozen` (`plan`: the first carve's plan; `bundles`: their
  names) and the live statements under `external_theorems`, then plan, gen, measure and `split_run.py` as
  usual, with a fresh run state.
  - **gen** writes each frozen bundle byte for byte from its published copy (`frozen.lib`, else the
    workspace's `Definitions/` via `fetch_theorems.py --names`) and refuses when there is no copy. It
    re-applies `work/repairs.json` to every file. With `frozen.repairs` (the first carve's repairs.json)
    it prints `FROZEN … differs` on drift.
  - **split_run** starts every run (and the read-only dry run) by looking up every item of the plan on
    the platform and adopts each one live under its name with our text, without needing its prose. A live
    name with other text stops the whole run before anything is posted.
- **A later target of an already-carved family** (oaiq-057): extend it with the earlier carve's plan,
  bundles and lib as `frozen`; the planner takes the frozen plan's `external_defs` as its own (56fd083).
  Not handled: a frozen bundle that imports one of the old carve's statements (then use a fresh
  `statement_suffix`).
  - **Clashing `Def_` bundles.** Each comparator file of a family carries its own copy of the shared
    declarations, so two goals importing different `Def_` bundles usually cannot share a frozen bundle
    (q228, q236, q240, q245: hours lost each). `config` and `plan` now stop on such a clash (6e16e00;
    the queue's overlap row names both bundles). Then carve fresh under a `statement_suffix`; or, when
    the new goal's solution uses only a few results of the old development (read its calls), publish a
    bridge statement mentioning neither bundle (definitions unfolded into Mathlib terms), prove it in
    the old bundle's world, and the goal from it (q245: minutes, not a 513-module re-carve).
  - `defs` must hold every `import Definitions.*` of the targets' stubs (checked at `inputs` and
    `config`, q238); the `Def_` bundles those import come along by themselves, and a `defs` edit re-runs
    `config` (6cd9e93, q227).
- **Extending another carve's frozen plan** (oaiq-088): a private node name embeds the old port folder
  (`_private.Solutions.OAIQ038_FA…`): rewrite the frozen plan's folder name to the new one, or a spurious
  import cycle appears. Every `external_theorems` entry must exist in the new graph (drop those outside
  the new closure, else `unknown external definition`).
- **Extending a split whose bundle another carver made** (the zero-divisor K(G,1) clause): `carve.py`
  with a `frozen` bundle from an old per-mission carver produced pieces that imported none of the new
  bundles. Instead: merge the whole port (`build_solution.py`), drop by exact full name every declaration
  the published bundles define (list them with a Lean `#eval` over `env.constants` filtered by module) and
  every published statement, import those, rename OpenAI's copy of the target, then `prune_solution.py`.
  Traps: a bundle name can capture a bare name the port meant at the root (`GraphPresentation.Group`
  captured `[Group G]`; write `[_root_.Group G]`); `prune_solution.py` drops `include` lines after kept
  `variable` lines and keeps `variable` binders that mention pruned variables (repair script:
  `p2m-standalone/openai-tfzd-kg1/fixup.py`; fold it into prune_solution next time it bites).
- **Overlap with someone else's published work** (oaiq-067): `pipeline.json` `defs` replaces the list
  derived from the targets (keep the goal's own `Def_` in it); earlier published statements go in
  `config_set.external_theorems` (`{lean name: "Theorems.Thm_<name with _>"}`) after `fetch_theorems.py
  --names`; a clashing bundle is as above. Another user's *stalled* carve of the same goal (oaiq-082:
  a SKETCH_ACCEPTED reduction to Open leaves nobody proved): do not extend their leaves; carve under a
  `statement_suffix` and add the second decomposition, its goal piece sent with a comparisons note.
- **A goal someone else has already proved** (oaiq-068): split_run's piece is refused by the live-proof
  guard and waits. Read their proof; write `<carve>/publish/comparisons/<slug>.md` (beside
  `explanations/`), "Different from <id>: …" or "Same as <id>: …", and resume `--publish`: a "Different"
  piece is sent with that reason, a "Same" one is settled unsent.

## Retrying an earlier attempt

- **Read references for the symptom first.** A blocker an older batch recorded as "untried next steps"
  may have a documented remedy by now (oaiq-118).
- **A carve from before `carve_pipeline.py`** (a `config.json` and no `pipeline.json`) cannot be resumed
  by the driver. Do not repair it: start a fresh pipeline carve under a new folder and bundle prefix,
  carrying over only its hand patches; drop those that now count 0 (oaiq-115).
- **A carve from before 2026-10-29**: before the first `--detach`, check `pipeline.json` and its meta
  against the current brief: `defs` (bare `Def_X` normalised since 1e02cec; it must include the goal
  statement's own import, which `inputs` checks only since q238: q256's carve could never finish), meta `prefixes` (the root's
  top directory), `overlap`. A driver killed mid-build shows `build: running` and no failure line;
  resuming replays the built modules in seconds (oaiq-125). Resume with `--upgrade --keep-port` unless the
  port rules' changes are wanted; on an unpublished carve, `--from plan` picks up carver fixes (oaiq-122).
  Re-derive every old patch's `old` from the current ported text, not the old notes (oaiq-117). One that
  never published needs no re-port: fix meta `prefixes` to `openai_prefixes(DIR/src/lean)`, add
  `"overlap": true` by editing `pipeline.json` (the CLI `--overlap` is refused as a changed parameter),
  then `--upgrade --keep-port --from plan --stop-after names --detach` and `--publish --detach` (q134).
- **A new port patch on an old unpublished carve whose port rules have changed since** (q140): editing the
  patches file makes `filter_patches` stale, and the re-run port uses the *current* rules even under
  `--keep-port` (which only suppresses re-ports caused by rule changes), rewriting every module under the
  old hand repairs. Re-port on the carve's own snapshot, `python3 ~/.cache/p2m/skill/<old
  sha>/prove2me/scripts/carve_pipeline.py DIR --detach --stop-after wsbuild`, then `--upgrade --keep-port
  --publish --detach` from the current snapshot.
- **Hand repairs on a `--keep-port` carve start from a stale port** (q136): `--redo filter_patches` with
  unchanged output does not re-port, so the workspace holds the port of the old rules while the log reads
  as if the new ones were in force, and `mkpatches.py` diffs against it. Before repairing by hand, `--redo
  port`.
- **Repairs left only in the workspace** (q147) are overwritten by any re-port, and a changed
  patches file re-ports even under `--keep-port` (q260: 14 repaired modules lost). Run `mkpatches.py` as
  each wave of repairs is done, before any resume. Start a retry by compiling
  the modules the last build log says failed; if they now pass, compare their mtimes with the log, diff
  against a pristine scratch port (`oai_port_modules.py … --ws SCRATCH`, on the carve's own snapshot), and
  turn what you find into patches first. A patch from an `mkpatches.py` before 83161d7 can hold an `import
  Solutions.` line in its `old`, which counts 0 under filter_patches' placeholder folder: check before
  resuming.
- **Before calling a prover part lost, look in the workspace too** (q157: a complete 746-line part sat
  untracked there). `workspace_audit.py --folder FOLDER` (the name in `import Solutions.<FOLDER>.Blueprint`)
  lists each file as `copy … = <repo path>` or `no-copy`; copy every `no-copy` part into the repo's
  `proofs/` before anything else, and a RESUME that calls work lost names both places it checked.
  `sync_workspace`'s summary counts no-copy files by folder (ports excluded).
- **A carve a full disk killed** (q150): the last log lines are an `OSError: [Errno 28]` traceback in
  `save()`, with a 0-byte `*.tmp` beside intact state files. Check that `pipeline_state.json` and
  `publish/run_state.json` parse, then resume on the carve's *own* snapshot with `--publish --detach`: no
  upgrade, no re-plan. The restarted publisher first looks up every unsent item (2–3 s each; a
  `reconcile  looking up N items` line in `PROGRESS.log`). A proof stuck PENDING on the platform is sent
  again after `stale_pending_hours` (default 3).
- **Leaves left Open by unsent pieces** (q129): before assuming a goal's open leaves are hard, check
  whether each has a pending or never-sent piece. A `--publish` run that stops at `calibrate_pieces` after
  publishing began releases the within-budget pieces itself (dc103c1; `publish/release.json` lists them
  and the `held` slow ones, and the stop message lists what went). On older snapshots send them by hand
  with `split_run.py` from a copy of the run config (`state` and `log` pointed into the job dir).
- **A carve published on an old skill with a few broken items**: finish its own `publish/` rather than
  re-planning frozen across many skill versions, since newer graph rules infer needs the published
  bundles never had (oaiq-120). Compile each item against the *published* bundles (`fetch_theorems.py
  --names Definitions.Def_X …`), fix it, and resend with `split_run.py publish/run.json --go --reset
  statement:NAME` (old run states have no `sha`, so a changed stopped item is not resent without
  `--reset`).
- **A `SORRY` verdict on a carved piece whose local `#print axioms solution` is clean** usually means the
  server failed to elaborate it (an unknown identifier): compile the submitted source (`GET
  /submissions/:id/solution`) against the published bundles; do not just resubmit (oaiq-120).
- **A goal Open with no open leaves**: `GET /theorems/:id/open-leaves` does not list a Disproved child;
  walk `/decompositions` (oaiq-109). Every submission path now refuses a Disproved import
  (`submit_solution.py` since 9397093, and through it `submit_all.py` and `oai_submit.py`; split_run's
  pieces for statements of others, 59f4e2a).
- **Folding on a carve whose snapshot predates `carve.py fold`** (oaiq-118): `carve.py fold CONFIG N…` from
  a current snapshot; `carve.py gen CONFIG pieces <changed>` from the carve's own snapshot (a newer gen
  emits different `attribute [-instance]` lines); `carve_measure.py --kinds piece` from the current one (it
  runs the CoeT check); then `publish-prep --sync`, prose, check-text, and write the `comparisons/<slug>.md`
  notes *before* resuming, since they are what makes split_run resend the live importers (2442579).

## Using a ported development inside another mission

- **Import the published bundle plus the accepted carved solution body**, never the `Solutions/OAIQW_*`
  module chain the port was built from: that chain's `Model.lean` redefines what the bundle declares, so
  importing both fails with `environment already contains …` (q167). The accepted carve solution
  (`Sol_<goal>.lean` in the carve's job dir) is self-contained over the published `Def_*` bundle; minus
  its `theorem solution` it is a drop-in module. Copy it into the mission repo's `proofs/` at once
  (viterbo-mission `proofs/capacity/OAIEngine.lean`), since the job dir is scratch.
- **Some published OAI bundles cannot be imported together**: `Def_OAIQ075A0xx` (Stinespring) clashes with
  `Def_KadisonRingroseSupport2` (`environment already contains OAI.PopaTypeII.AbelianProjection`). Before
  building a route on two ported developments, check that one file importing both compiles.
- **An "opaque" constant in an OpenAI existential is usually a chain of numeric cutoffs** (q339): trace
  each `∃ R`/`∀ᶠ` to its numeric inequalities (regex `∃ \w+ : ℕ, … ≤` over the published statements; a
  search for `∃R` alone missed `∃ qH`), prove them at an explicit cutoff, and publish `*_explicit`
  versions, before recording "blocked: constant not comparable".
- **OpenAI's stack-machine library is published**: `Realizes`, `RunsPoly`, `realizedMachine` in
  `Def_OAIQ241TT000`–`014`. A wrapper for another input encoding took one prover about 20 minutes (q339;
  q276 had called machine statements blocked for want of it).
