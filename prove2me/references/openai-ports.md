# Porting and carving openai/math results

How a ported openai/math proof reaches prove2.me: the single-file route, and when that is too
big or too slow, the carver that splits it into published bundles, statements and pieces. Loaded
from SKILL.md's *Porting an openai/math result* pointer.

## The route

The published OAI goals were generated from openai/math at `adc7f12`. Use the skill's scripts
for every port. Never copy them into a job directory: twenty carves each kept a private
`port_modules.py` / `measure.py`, and their fixes drifted apart (2026-10-18). The shared text
transformations are in `p2mlib.oaiport`, and `tests/test_oaiport.py` pins the bugs they fixed.

1. **Search first.** Before publishing anything, search prove2.me for the goal and for each
   named result (`/theorems?theorem_name=`, `/definitions?q=`, by title). Someone else's existing
   statement is imported or proved, never published a second time.
2. **The single-file route comes first.** Fetch the import closure with `oai_fetch.py`. Then
   `oai_port.py` merges it, drops every declaration of the statement's published bundles by full
   name, renames OpenAI's copy of the target `<name>_oai`, and checks the verifier's form locally
   with `-j1`. `oai_batch.py --dir JOB` does this for many goals; `oai_submit.py --dir JOB` is
   the submit queue (restart-safe: each goal's state is rebuilt from its log).
3. **Submit it as it is.** Don't optimize first. Up to about 70–80 s of local CPU passes the
   300 s verifier; 90 s and slower timed out (five of six such goals timed out twice). So the
   queue gives a file over ~90 s one attempt and a faster one an unchanged retry. A port that
   times out twice is carved.
4. **Carve with the named results forced.** The module route is `oai_port_modules.py` (the
   modules into `Solutions/FOLDER`, with the compatibility lemmas in namespace `OAI`), then
   `oai_build_modules.py --elab-log`, then `carve_prep.py config` with `--def` for each published
   bundle the goal imports and `--forced` for each theorem the paper names. Then run `carve.py
   graph`, `carve_prep.py ext-defs`, `carve.py plan/gen/order`, `carve_measure.py`, and `carve.py
   split` (see **Splitting a large ported proof**). The single-file patches go through
   `carve_prep.py filter-patches` first, with the same compat options as `oai_port_modules.py`.
   It counts each patch against the text the module port patches, not against OpenAI's source:
   the port's own rewrites can add a match (`OAI.tensorInductionOn`, below) or
   remove one (a compat alias): quote the ported text (an `inferInstance` at a `Measure.map` site
   is a long `first | infer_instance | …` line there) and count with `rg -c` in `Solutions/FOLDER`.
   A patch whose count differs fails the step, listing its occurrences per module (`"allow_drop":
   true` lets one go); so does a patch whose `old` starts or ends inside a longer identifier
   (oaiq-040: `hpos` matched `hpositive`), so end `old` at a delimiter. It also drops
   single-file-only patches, which are marked
   `"route": "single"` or reorder a universe list for merge.py's `universe` line. The module port
   inlines tactic macros across modules, as `oai_port.py` does. `oai_build_modules.py` rebuilds
   a module when anything it imports changed, so after a fix no `--force` is needed. Each forced theorem becomes its own published
   statement, so others can reuse it. `oai_build_modules.py`, `carve.py` and `carve_measure.py`
   each allow one live run per carve (`p2mlib/runlock.py`). A second copy exits 3 and names the
   pid already running it: wait for that run or stop it, and never start another (2026-10-23, a
   resumed agent had no record of a pipeline it had restarted an hour before). Stop a run with a
   plain `kill PID` (SIGTERM), never `kill -9`: a lock holder then stops everything it started
   (its `lake` and `lean` too) before it lets go of the lock. With `kill -9` they keep compiling for
   minutes and race the next run over the same `.olean` files (2026-10-26, oaiq-003 and oaiq-012).
5. **A bundle that needs a statement imports it.** With `bundles_import_statements` (the default),
   a bundle imports a forced theorem that definitions need. That import is allowed only once the
   theorem is Proved, so `publish_order` puts the bundle after the statement's piece.
6. **Before publishing:** `carve_prep.py publish-prep`, then `carve_prep.py prose-template DIR`,
   then write by hand only what it lists as "needs written prose", then `carve_prep.py check-text`.
   The last checks the explanation rules, that every backticked name exists, and that no stub
   contains a comment. Credit OpenAI and the result family in every description and explanation.
   - **Template prose for intermediate items; written prose only for the goal and the forced
     named results** (dbenbenn, 2026-10-24: a carved intermediate item's prose is rarely read soon
     and stays patchable, and model-written prose had become the biggest cost of a carve).
     `prose-template` makes no model call. From the plan, `publish/out/`, `work/decl_graph.jsonl`
     and `DIR/oai_meta.json` (title, date, family, full commit, paper URL, OpenAI module
     prefixes; `p2mlib/prosetemplate.py` has the format), it writes three kinds of file:
     - a statement's prose: the OpenAI credit, the GitHub link to the declaration at the commit,
       the published Lean in a code block, the split's declarations Lean records the statement
       using, and which items import it;
     - each bundle's prose: its declarations by kind, its modules, what it imports and what
       imports it;
     - each piece's explanation in prove.md's form.

     It makes no mathematical claim the Lean does not show. It skips the goal and every `forced`
     node and lists them as needing written prose. Generated files carry `template:` in their
     front matter (prose) and a sha1 in `.template.json`; a rerun regenerates only unchanged
     templates and keeps written prose unless `--force`. `bundle-prose` (a hand template) remains
     for a carve that wants written bundle prose. Fenced code blocks are code to `check-text` and
     `check_pronouns.py` (a binder `he` is not a pronoun).

The compatibility block lives in namespace `OAI` by default (`--root-compat` restores the old
form). Two bundles that both declared a root-level `ite_eq_left` would clash. A namespaced
`alias Finset.prod_le_prod₀ := …` would create `OAI.Finset`, which shadows Mathlib's `Finset`
under `open Finset`, so each alias is rewritten into the sources instead. Two bundles that were
already published still export root names: UniversalFInfinity's `OAIQWUFI004` (`ite_eq_left`,
`ite_eq_right`, `dite_eq_left`, `dite_eq_right`) and ESB's `OAIQWESB000` (`alias
Finset.prod_le_prod₀`). A port that imports either of them must not declare those names again.

**Mathlib drift that recurs in module-route ports (Sonnet trial, 2026-10-25: Markov, PlanarFPP, SymmetricMahler,
Problem336).** Fix each at the cause; none needs a macro.
- *Pi-form vs lambda-form (`to_fun`).* Our `HasDerivAt.mul/neg/sum/pow`, `DifferentiableAt.sum` conclude `c * d`, `-f`,
  `∑ i, f i` as functions; OpenAI's conclude the lambda. A `convert … using 1` then leaves extra goals (a function
  equality, an instance diamond like `Complex.addCommGroup = …CStarAlgebra…`). Use the `fun_` variant where it exists
  (`fun_mul`, `fun_neg`, `fun_sum`, `fun_pow`) and close what is left with `all_goals first | rfl | …`. `ContDiffAt.mul`
  has no `fun_` form: `convert … using 1 <;> first | rfl | (funext z; simp …)`.
- *Total `Measure.map`.* d13f23b's `Measure.map f μ` of a non-AEMeasurable `f` is a Dirac mass, so `IsProbabilityMeasure
  (μ.map f)` is an unconditional instance and `ProbabilityMeasure.map ν f` takes no proof. Ours is 0 there: no instance
  (a measurable *equivalence* has one in the compat block), `ProbabilityMeasure.map` wants `AEMeasurable f ν`. The port
  rewrites the textual sites (`oaiport.core_rewrites`, 8bac231): `have … : IsProbabilityMeasure _ := inferInstance`,
  a bare `infer_instance`, `inferInstance` inside `⟨…⟩`, `ProbabilityMeasure.map ν f` and `… := ν.map f`, the
  `Measure.map_smul` and `fst_map_prodMk` proof arguments; the measurability goal goes to `AEM_TAC`
  (`fun_prop | assumption | … | measurability`). By hand: `μ.map T` of an untyped `ProbabilityMeasure`, an instance
  used implicitly by a lemma statement (add `haveI … := Measure.isProbabilityMeasure_map …`), and a map whose
  measurability is a named lemma (`measurable_liftPair d`): name it directly, since the tactic chain can time out
  at `isDefEq` (oaiq-041, oaiq-044).
- *The `eLpNorm` family, `tendsto_integral_of_L1'`, renames, `mgf_gaussianReal`* (oaiq-036/038/048; rewritten by
  0cd4396). A trailing measurability argument was removed from `eLpNorm_eq_eLpNorm'`,
  `eLpNorm_eq_lintegral_rpow_enorm_toReal`, `eLpNorm_nnreal_eq_eLpNorm'`, `eLpNorm_mono_real` and
  `Lp.eLpNorm_le_of_ae_tendsto` (its `hg`), and the port drops it by position; `eLpNorm_sum_le`,
  `eLpNorm_le_eLpNorm_of_exponent_le` and Bochner `tendsto_integral_of_L1'` gained one, which the port inserts as
  a named argument proved by `AESM_TAC`; `eventuallyEqSet_univ` is `eventuallyEq_univ`; d13f23b's
  `eLpNorm_indicator_const` is our `eLpNorm_indicator_const₀`; `mgf_gaussianReal ⟨hm, heq⟩` is
  `mgf_gaussianReal heq`. By hand: an `apply` followed by one bullet per goal (delete the dropped goal's bullet),
  a `rw [foo a b]` that left the removed argument as a side goal, an `AESM_TAC` site where nothing fixes the
  function yet (`simpa … using eLpNorm_sum_le (…)` with no `(f := …)`).
- *Smaller drift seen once or twice, patched per site:* `MemLp g p μ` is a pair (a bare `lt_top` proof needs
  `⟨hg.aestronglyMeasurable, _⟩`), `MemLp.mul` swapped its factors; `norm_num [table defs]` leaves `vecCons`
  lookups or `Int.toNat 205` unevaluated where `simp [same]` evaluates them (oaiq-033/038); `rw
  [AddMonoidAlgebra.coeff_zero]` on an `MvPolynomial.coeff` goal is `MvPolynomial.coeff_zero` (and `coeff_add`);
  `tauto` no longer unfolds an applied set-builder membership; a multi-line `convert … using 1; first | rfl |
  ring` closes only the first goal (use `<;>`) (oaiq-045); `omit [BorelSpace E]` on a lemma that uses stdGaussian
  (oaiq-048).
- *"not type-correct under the `implicit` transparency level"* in `rw`/`simp`/`dsimp` (category theory,
  homological algebra; oaiq-032). Fix per failing module, never as a port default (making
  `backward.isDefEq.respectTransparency false` a header default broke modules that had built: synthInstance and
  whnf timeouts, a `simp` that now closes the goal). In order: the option as a port patch anchored inside the
  module before `namespace OAI` (a `set_option` inside a namespace ends with it); else `erw` at the failing step;
  when the option makes `simp` close a goal, `all_goals` or `simp only` for the next tactic.
  `set_option synthInstance.maxHeartbeats 200000` fixed "failed to synthesize … deterministic timeout" in 12
  modules with one patch.
- *`SimplexCategory.toTopHomeo` / `TopCat.toSSetObjEquiv` with `--stdsimplex auto`* (oaiq-043): ours lands in the
  subtype `stdSimplex`, d13f23b's in the structure; structure mode renames `toTopHomeo` to `toTopHomeoD…` from the
  module `StdSimplexTopCompat` (a040fa7). `--stdsimplex subtype` is no way out for code that also uses the
  structure's fields. Many hand patches are easier to keep as a diff of the repaired modules against a copy of the
  unpatched port turned into `patches.json` (oaiq-043/mkpatches.py: one line of context per hunk, never a line
  the port itself rewrites).
- *A `have` that states a hand-written `match`* (`have h : … (match vs with …) …; simp_rw [h]`) breaks when the
  function whose body has the same `match` comes from a bundle: Lean shares a matcher only within one module
  (oaiq-018). Patch the generated piece (config `patches`) with a defeq congruence instead of the rewrite.
- *`import all`.* OpenAI reaches Mathlib's *private* declarations (`import all …IsGaussianProcess` for
  `Finset.orderEmbOfFinWithBot`) with `import all`, which a non-`module` file cannot use. Copy the private declarations
  into the module (root names; the private ones are mangled, so nothing clashes).
- *`import Mathlib` in Compat leaks instances.* Mathlib's `CStarMatrix` (a type copy of `Matrix` here) breaks
  `simp only [Matrix.mul_apply]` on matrix products. `oai_port_modules.py --compat-imports narrow` gives Compat only the
  Mathlib files its lemmas need (`oaiport.COMPAT_NARROW_IMPORTS`); set the carve's `collapse_mathlib` to false so the
  carved files keep OpenAI's own narrow imports too. A module that then misses a name needs its import added by a patch.
- *Never edit a running shell driver*: bash reads a script as it runs, and an edit made mid-run executed garbage
  in a second carve (2026-10-25). There are no job-dir drivers any more: see the next paragraph.

**Run carves with `scripts/carve_pipeline.py`, from a snapshot; never write a job-dir driver** (dbenbenn,
2026-10-25). Agents kept hand-writing bash drivers (`plain_carve.sh`, `plain_pipeline3.sh`,
`ext_publish.sh`, ...); one was edited while two carves ran it, and a skill fix pushed mid-carve mixed old
and new `carve.py` inside one carve. So:
- `carve_pipeline.py DIR --folder F --root-module M --target T --bundle-prefix P [--def …] [--forced …]
  [--patches …] [--compat-imports narrow] [--budget N] [--config-set JSON] [--fetch]` is the whole module
  route of step 4 and 6 above: fetch, inputs (the targets' published statements and `Def_` bundles,
  fetched into the workspace when missing), filter-patches, port, build, workspace build, config, graph,
  ext-defs, plan, gen, order, measure (edge check on), calibrate, publish-prep, prose-template, check-text,
  and a `split_run` dry run (`--publish` adds `split_run --go`). `--fetch` copies the root's import closure
  from the local openai/math clone (`~/claude/openai-math`; raw GitHub only for what it lacks, with backoff on
  429); never pass a whole openai/math tree as `--lean-src` (port and filter-patches refuse more than 50 modules
  outside the closure; eleven workers lost hours to that and to 429s, 2026-10-26/27). The build keeps going past
  a failing module and reports every failure in one run.
- **Run it detached and wait on it** (2026-10-27): `carve_pipeline.py DIR … --detach` starts the run as a
  systemd user unit (log `DIR/logs/driver.log`); `carve_pipeline.py DIR --wait 100` returns its status, or
  exits 4 still running: re-arm that. A Bash background command dies at 2 h, and that killed drivers mid-build
  and mid-graph on every port over ~300 modules (oaiq-033..049); a killed wait costs nothing. Since a932a18 the
  build leaves `graph` its LeanInfo reading, so `graph` takes seconds after a build.
- Parameters live in `DIR/pipeline.json`: a different CLI value is refused, so edit the file. A changed
  `config_set.patches` needs `--redo config` and `--redo gen` (config alone leaves the generated files
  unpatched). Editing the patches file and resuming re-ports (stale-step detection). `--def` takes
  `Definitions.Def_X` (a bare `Def_X` is read so); `--measure-flag` takes the `=` form. Each step is idempotent, logged in
  `DIR/logs/STEP.log`, recorded in `DIR/pipeline_state.json`; the first failure stops the run with the log's
  tail and the same command resumes. Parameters are stored in `DIR/pipeline.json`. Written prose for the goal
  and `forced` items is still yours (it is listed, not generated).
- It re-execs itself from `scripts/skill_snapshot.py`'s read-only copy of the skill at HEAD
  (`~/.cache/p2m/skill/<sha>/`; `--allow-dirty` snapshots an uncommitted tree) and calls every tool from
  there, recording the sha; a resume stays on its snapshot (`--upgrade` moves to HEAD). Editing or pushing
  the live skill cannot reach a running carve.
- **The cost model is calibrated by the measurement, automatically** (batch 3, 2026-10-25). The first plans
  of QuarticPowerFree and KirchbergRordam measured 85–128 s per bundle against a 55 s budget (a 128 s bundle
  timed out three times) and needed `time_scale` 2.2 and 4.5. The `calibrate` step after `measure` takes any
  unfrozen item measured over 1.6 × budget, sets `time_scale` to scale × (its measured seconds / planned
  cost), re-plans, re-generates and re-measures (unchanged files are cached), at most twice, and stops with
  the offenders listed (then `carve.py split` or a manual `time_scale`). Never publish before it passes. It
  only raises the scale: a small sample cannot calibrate it down, since the per-item error is 0.3–1.4× even
  at a fitted scale. A piece measured under 200 s never counts (57119d3): it is a proof, resubmittable,
  so submit it as is and split only after two real verifier timeouts; bundles and statements freeze at
  publish and keep the strict limit (oaiq-035/037: a 106 s piece cost two hour-long re-plans).
  `accept_over` in pipeline.json excuses another item under the same 200 s cap. Outside the pipeline the
  manual rule is the same: measure everything, and if any bundle or statement is over ~90 s, multiply
  `time_scale` by the worst measured/planned ratio and plan again.
- To change a tool: change the skill (tests first), commit, push; new runs pick it up, running ones do not.
  A tool fix a running carve needs: `--upgrade --redo STEP` (from any snapshot, the carve's old one
  included, since 1dbb8c1). Any remaining shell script in the skill has
  its body in `main() { …; }; main "$@"; exit` (`tests/test_shell_scripts.py`).
- Long single tools outside the pipeline (a one-off `carve.py` call) should likewise run from
  `python3 "$(scripts/skill_snapshot.py)"/prove2me/scripts/X.py`.

**`TensorProduct.inductionOn` becomes the compat eliminator `OAI.tensorInductionOn`** (2026-10-24).
OpenAI's Mathlib (d13f23b) has `TensorProduct.inductionOn z tmul add`, with the zero case taken
from `tmul 0 0`; ours (0df444a) has only `induction_on`, which asks for a `zero` case. The ports
used to rename it and insert `| zero => simp only [map_zero]` at the `induction` line's
indentation. That failed on most real goals (`0 ∈ C`, `Commute _ 0`, a `Module.compHom` smul, a
coerced `0` in a completion) and landed misindented when OpenAI indented the `induction` line
differently from its alternatives; ComparatorModel and Boone–Higman each carried hand patches for
it. `lean/compat_4_34.lean` now declares `tensorInductionOn` with OpenAI's signature, and
`oaiport.core_rewrites` points every use at it, so alternatives, bullets and term-mode uses stay
as written and no zero case is ever guessed. It is not called `OAI.TensorProduct.inductionOn`:
an `OAI.TensorProduct` namespace makes `open TensorProduct` inside `namespace OAI` open only that
namespace (Lean warns "Ambiguous namespace"), which loses Mathlib's `⊗ₜ` lemmas. A carve's old
`| zero => …` patches now count 0 and must be dropped.

**`Convexity.StdSimplex` is handled by a shim, never by hand** (2026-10-24). OpenAI's Mathlib
(d13f23b) has `Convexity.StdSimplex` API ours (0df444a) lacks: its topology, compactness,
barycenters, `homeomorphI`, `range_toFun_comp_weights` and more. `lean/StdSimplexCompat.lean`
supplies all of it under the d13f23b names (Part 1, copied from Mathlib d13f23b), plus `OAI.SStd`,
the subtype `stdSimplex` with the same names (Part 2). Both port routes apply it automatically when a
source mentions `StdSimplex` (`--stdsimplex auto`, `p2mlib.oaiport.stdsimplex_*`). They drop the
d13f23b-only `Mathlib.Geometry.Convex.ConvexSpace.*` imports, and the module route adds the module
`StdSimplexCompat`. Our `SimplexCategory.toTop` is the subtype, so code that uses
`SimplexCategory.toTop.obj` as a `StdSimplex` (Problem340's singular homology) needs
`--stdsimplex subtype`, which renames `Convexity.StdSimplex` to `OAI.SStd`. That mode needs finite
index types and has no `ConvexSpace`, so Thomason-style code that mixes both kinds of use still needs
hand work. The shim is published as `Definitions.Def_OAIStdSimplexCompat`
(c7014b9a, p2m-standalone/oai-stdsimplex-compat). Once that bundle is in the workspace
(`Definitions/Def_OAIStdSimplexCompat.lean`, byte-identical to `lean/StdSimplexCompat.lean`, built),
`oai_port.py` imports it instead of inlining the shim, and `carve_prep.py config` adds it as a
`--def`, so a carve imports it rather than publishing the shim again. Pass the same `--stdsimplex`
to `oai_port_modules.py` and `carve_prep.py filter-patches`.

## Splitting a large ported proof

A port over the 1 MiB cap, or with pieces the 300 s verifier cannot finish, is split by
`scripts/carve.py` (`graph`, `plan`, `gen`, `order`; its docstring has the config). Never write
a per-mission carver: five did (Kaplansky, Deligne–Drinfeld, Catalan, Chowla, Erdős 3,
2026-10-07/08), and each relearned the same bugs, now tests in `tests/test_carve.py`. The tool
publishes every reachable definition in Definitions bundles and promotes theorems to published
statements until each piece fits its budget. It carves by Lean's own command ranges, and each
piece renames OpenAI's copy of its target `<name>_oai`; without the rename the submissions came
back WA. The lessons:
- **Budget.** Aim for pieces of about 60 s or less when compiled locally with `-j1`. That leaves
  margin under the 300 s verifier; the Erdős 3 cost model scales local build times by 1.5, and
  bundle B005 still timed out twice at 300 s before it was published.
- **Splitting only helps when it removes shared recomputation.** A definition that every piece
  re-elaborates costs every piece. Splitting pays when expensive shared material moves into a
  bundle or a published statement that later pieces import instead of re-proving. Cutting a proof
  whose pieces all redo the same heavy work only multiplies that work.
- **Publish concurrently along the DAG.** `carve.py order` prints waves. Everything in a wave can
  be published at once when the earlier waves are done: independent bundles together, then each
  statement after its bundles, then each piece after the statements it imports. Erdős 3 first
  published its bundles as a chain, one at a time, and then re-planned them as a DAG
  (2026-10-08).
- **Never edit the port's source after the graph is built.** The carver cuts each module by the
  command positions recorded when the port was compiled, so changing a proof in the source (even to
  speed it up) corrupts every later carve of that module: on Erdős 3 a five-line proof fix spliced
  text into two unpublished bundles (2026-10-16). Apply such fixes as post-carve text replacements
  to the generated files instead.
- **No `macro` or `syntax` commands.** The soundness guard refuses them, and the carver refuses to
  keep one. `notation` is fine.
- **Fix a carver bug in `p2mlib/carve.py` with a CarveDev test; don't patch it per carve.** Every
  carver bug so far was a text reading of a short name disagreeing with what Lean elaborated
  (a field token read as a same-named theorem, a `_oai` rename hitting other declarations, an
  `export` without its namespace, duplicate anonymous instances, a later module's instance
  changing elaboration). That is why the carver now reads Lean's records instead (next item); a
  post-carve patch is only for a proof fix.
- **The carver reads what Lean elaborated, not the source text** (2026-10-24). `carve.py graph`
  runs `lean/LeanInfo.lean --idents` *elaborating* each module (`--module M --no-decls`; cached
  by content under `~/.cache/p2m/leaninfo`). It costs about the module's own compile CPU time
  (FormalBoxes: 87 s against 93 s). Since 2026-10-27 the tool runs compiled
  (`p2mlib.leaninfo.native_tool`), and `oai_build_modules.py` compiles each module through it
  (`leaninfo.build_module`: one elaboration writes the .olean/.ilean and caches this reading, with
  the build's `autoImplicit=false`), so after a build `graph` reads every module from the cache
  instead of elaborating the port a second time. Before, the two passes were about two thirds and
  one third of all Lean slot time on the box. A module built some other way (by hand with `lean -o`,
  or before this change) is still elaborated by `graph`, as before. For
  every command it records from the info trees:
  - `resolved`: what each identifier token resolved to, the name part and each field part
    (`A.coord_eq` with `A : Space`, `(e).f`, an `open`-resolved name, a `simp only [h]` lemma, a
    notation's `=> foo`, an `attribute`/`export` target), a local as `""`, a declared or bound
    name and a structure-instance field marked;
  - `insts`/`sig_insts`: the non-library instances its elaborated terms use (a `Fact`/`NeZero`
    instance is a theorem only instance search uses; this is the only place its use shows);
  - `inst_keys`: what instance search solved (class and argument heads);
  - `declares_kinds`/`kinds_used`: the notations a command adds and the ones it is written with.

  The carver takes from these: dependency edges (instance uses included; a local notation only
  for the commands that use it), whether a context line names a gone declaration (fields
  included), the `_oai`/suffix renames (exactly the token parts that resolved to the renamed
  constant), and `_root_.` pins (only when the carved file would show the text other candidates
  than the port's module saw; never a declared name or a case name like `| zero =>`). It puts back
  in force exactly the local instances a kept declaration used (a stub: its statement), and at
  the top of each module section it hides again, with `attribute [-instance]` (section-local),
  the global instances that module never saw and whose type could match its problems: this fixed
  RationalHitting's witnessCharZero leak, which had needed a post-carve patch. What it cannot
  hide (an instance declared later in the same module, reached through a bundle) `plan`/`gen`
  still warn about. The text reading survives only as the fallback for a token with no record (a
  few per carve, inside some `simp`/`simpa` argument lists); `graph` and `gen` list them.
- **Heavy computations do not belong in bundles; publish them as statements.** Eilenberg–Ganea
  (2026-10-25): OpenAI's chain-contraction certificate is about 850 `decide +kernel` lemmas (the
  module: 900 s, 23 GiB), and a *definition* (`contraction`) rests on their aggregates, so the
  carver put them all in 17 bundles of about 58 s. Each published alone, but every bundle
  importing several of them failed with `dependency_oom` ("Failed to compile modules …: Lean
  exited with code 137"): a cold worker builds the imported bundles in parallel and runs out of
  memory. Unchanged retries failed the same way. The fix: `forced` the facts the definition needs
  (statements whose names are ASCII; `pinned` the definitions their statements mention, or the
  plan has a cycle), so bundles import cheap `sorry` stubs and the computation moves into
  pieces. When such a fact is proved directly from hundreds of per-index lemmas, the planner
  promotes each lemma to its own statement (561 here). Add block lemmas first, by a port patch
  that proves the aggregate from blocks (`interval_cases` over a range, then the per-index
  lemmas; `omega` picks the block); then it promotes blocks. Size blocks by the measured cost per
  lemma: 30 lemmas at 2.8 s made an 84 s block. Generator: `p2m-standalone/openai-ports/
  eilenberg-ganea-carve/gen_block_patches.py`; fold it into `carve_prep.py` the next time a carve
  needs it.
- **Uses the elaborated term cannot show** (batch 3, 2026-10-25; `pinned` groups and `synthInstance.maxHeartbeats`
  patches are no longer needed for these). (1) A `CoeSort`/`CoeFun`/`Coe…` instance that elaborates away
  (`↑p` is `p.carrier`, `f n` is `f.toFun n`) is a dependency of every declaration naming the function it wraps
  (`Carver._add_coercion_instances`). (2) Attributes only the declaring file may set (reducibility including
  `instance_reducible`, `inline`, `specialize`, `export`, `implemented_by`, `extern`, … `RESTRICTED_ATTRIBUTES`) stay in the file
  that has their target; elsewhere the bundle holding the target already carries them. (3) A local instance that
  won a subproblem but left no constant comes back when an `inst_keys` problem of the declaration has its
  class and heads. (4) An instance that only a `variable` binder needs (`NeZero n` for `W.x 0 0`) is a
  dependency of the declarations in its scope.
- **`carve_measure.py` checks every import edge, and fails the carve on a false one.** The
  carver infers dependencies partly from source text, so it can emit an `import Theorems.*` a
  piece never uses; the file compiles, and the false edge goes into the published graph
  (PosteriorReplicas 2026-10-23, caught only by hand: drop each import, recompile). After each
  file compiles, `lean/EdgeUses.lean` reads its .olean (a piece compiles as module
  `EdgeChk.Chk_<name>` for this) and lists the constants each import supplies to what `solution`
  reaches (for a bundle or statement, to every declaration). Each import it finds unused is
  confirmed by one compile without it, because a `dsimp only [rfl_lemma]`, a notation or an `open`
  leaves no constant behind. Checked: every `import Theorems.*`, and a bundle's imports of this
  carve's other bundles. The report is `work/false_edges.json`, which lists each false edge (with
  the bundle to import instead when the statement only brought one in), imports used only by dead
  code, and **orphaned statements**: no file imports them any more, and they are neither target nor
  forced, so drop them from the plan, as was done by hand for PosteriorReplicas. Results are cached
  in `work/edges.json`. `--drop-false-edges` cuts the false import lines and records the cuts in
  `work/repairs.json`, so they survive `carve.py gen`. `--allow-false-edges` reports without
  failing; `--no-edge-check` skips the check. Recompiling once per import gives the same answers
  except for an import that is also reached through a bundle, which it calls false. It is only the
  fallback, used when the scan fails. On the 17 hand-checked carves of 2026-10-23/24 (106 edges)
  the check agreed with the hand results: one false edge (PosteriorReplicas, with its orphaned
  statement) and every other edge used. It added 3–14% to the measure time, about 5 s per file
  that has an edge to check.
- **The soundness guard refuses the token `prelude`, even as an identifier** (WLTime 2026-10-23:
  OpenAI's `def prelude` failed a published bundle). Both port routes rename it to `prelude_`.
  `carve.py gen`, `split_run.py` and `submit_solution.py` refuse any file the guard would refuse
  (`p2mlib.leantext.guard_problems` holds the guard's rules; add a newly found rule there).
- **The cost model is a little pessimistic near the budget; trust the measurement.** On 195
  measured bundles and pieces of 27 carves (time_scale 1.2, 2026-10-24), measured -j1 time came
  out at about 0.65 × estimate + 7.6 s (residual sd 6 s). Items estimated at 40–60 s measured at
  0.74× (median), but the ratio ranged up to 1.43× (a ThorpNine piece: estimated 42 s, measured
  60.5 s). The carves' own medians ran from 0.56 to 1.34, so the spread is per carve, not a
  single scale to correct. The model is unchanged. Measure every carve (`carve_measure.py`), then
  re-plan or `carve.py split` from the times.
- `carve.py plan` refuses a plan in which a bundle misses a definition that one of its members
  needs (Erdős 3 B006 `A.space`, B024 `coord`), or in which a bundle or piece rests on `sorry`
  (B022). Compile every bundle locally before publishing it. A published bundle is frozen
  (`frozen` in the config), so a later re-plan keeps it as it is.
- **Extending a published carve** (a new statement after the first bundles are live) is the
  normal path. Make a second carve with the live bundles under `frozen` (`plan`: the first carve's
  plan; `bundles`: their names) and the live statements under `external_theorems`, then plan, gen,
  measure and `split_run.py` as usual, with a fresh run state.
  - **gen** writes each frozen bundle byte for byte from its published copy: `frozen.lib`, else
    the workspace's `Definitions/` (`fetch_theorems.py --names`). It refuses when there is no copy.
    It also re-applies `work/repairs.json` to every file, so a regenerated file is the one
    measured. With `frozen.repairs` (the first carve's repairs.json) it checks the regenerated
    text and prints `FROZEN … differs` on drift.
  - **split_run** starts every run (and the dry run, read-only) by looking up every bundle,
    statement and piece of the plan on the platform. It adopts each one live under its name with
    our text (a piece: our exact source as a live proof), without needing its prose. A live name
    with other text stops the whole run before anything is posted.
  - Boone–Higman, 2026-10-24: gen dropped a measure-time repair from a frozen bundle, and the
    agent seeded the run state by hand to keep five live bundles from being re-posted. Both are
    now in the tools.
- **Extending a split whose bundle another carver made** (the zero-divisor K(G,1) clause,
  2026-10-10): `carve.py` with a `frozen` bundle from the old per-mission carver produced pieces
  that imported none of the new bundles (its dependency edges missed names a `simp only` or `rw`
  uses). What worked instead: merge the whole port (`build_solution.py`), drop by exact full name
  every declaration the published bundles define (list them with a Lean `#eval` over
  `env.constants` filtered by module) and every published statement, import those, rename OpenAI's
  copy of the target, then `prune_solution.py`. Two traps: a bundle name can capture a bare name
  the port meant at the root (`GraphPresentation.Group` captured `[Group G]`; write
  `[_root_.Group G]`), and `prune_solution.py` drops `include` lines after kept `variable` lines
  and keeps `variable` binders that mention pruned variables (repair script:
  `p2m-standalone/openai-tfzd-kg1/fixup.py`; fold it into prune_solution next time it bites).
  When two pieces redo the same generic modules, move those modules whole into definitions
  bundles: 95 s became bundles of 20 s and 27 s plus pieces of 36 s and 59 s, all accepted.

- **Lessons of the abandoned first Erdős 3 split (2026-10-08..16; archive
  `p2m-standalone/openai-erdos3-split-v1`, README).** It published 244 bundles and proved 304 of 440
  pieces, then stalled: its deepest bundles never published (every attempt a cold "Module
  compilation timed out") because the bundle import chain was 92 levels deep (178 bundles in one
  closure, ~5,200 s of compile on the critical path). What to do instead:
  - **Rebuild the port before `carve.py graph`.** DeclGraph reads `.olean`s; proofs repaired in the
    source but never rebuilt still read as `sorry` with no dependencies, so helpers went missing
    one layer at a time. `lake build` the port's root first.
  - **Shallow bundles: `"chunker": "schedule"`.** Bands over modules follow the module DAG (163
    levels of bundle material); declaration-level list scheduling gives about 16 for the same
    material. Depth is what a cold verifier pays.
  - **Bundles hold only what definitions need.** The carver already keeps helper theorems out of
    bundles except those a definition uses (a definitions bundle may import a published statement,
    `import Theorems.Thm_…`, per prove.md's Platform Imports: config `bundles_import_statements`,
    on by default, publishes a forced theorem that definitions need as a statement and has their
    bundles import it; otherwise the bundle proves it itself); an
    earlier per-mission carver also put 68% theorems and ~17,000 dead `variable` commands into
    them. The shared carver drops scopes left without a kept declaration.
  - **Measure before publishing.** Build every bundle locally (`-j1`), re-pack any over budget, and
    only then publish; v1's scheduler split bundles while publishing, re-carved published bundles
    (two published chains then re-declared 169 names), and looped 1,112 times isolating one
    declaration that alone exceeded the budget.
  - **Retries: `p2mlib.verdicts`.** Transient failures retry (≤ 30); own timeouts split after 2
    (v1 retried one piece 740 times); CE/WA stop for a person.
  - **Local checks: `p2mlib.localcheck`.** Key each result by content (stale cached passes sent
    broken pieces) and compile the emulated verifier check (solution, published statement,
    `theorem _check : type_of% @T := @solution`): it reproduces the locationless WA.
  - The verifier compiles a solution **without its target in scope**; carved pieces must also
    re-activate local instances (`attribute [local instance] x` when the bundle exports `x`),
    avoid tokens full Mathlib adds (`Δ_[1]^[n]` → `Δ_[1] ^[n]`), and drop a theorem a published
    bundle already declares. Config `external_defs`, `statement_suffix`, `patches` (post-carve
    proof fixes) support a fresh split beside an abandoned one.
