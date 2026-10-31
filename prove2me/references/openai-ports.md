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
   contains a comment. So write bundle names in full: a backticked prefix such as `` `OAIQ030L…` `` is
   NOT FOUND; write "OAIQ030L000 to OAIQ030L035" without backticks (q137). Credit OpenAI and the result family in every description and explanation.
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
- *Smaller drift seen once or twice, patched per site:* `A ≤ᵐ[μ] B ∪ ⋃ …` with sets of sets fails to
  synthesize `Union (Set E → Prop)`: ascribe `(B ∪ … : Set (Set E))`; after `filter_upwards` on `=ᵐ` of sets the
  goal is applied sets (`E x = F x`), not `x ∈ E`, so `rw`, `simp only [mem_inter_iff]` and `simp only [mem_iUnion]`
  fail: `change (x ∈ E ∩ U) = (x ∈ G ∩ U)` / `show x ∈ …` first, `refine hx.trans ?_` for `rw [hx]`,
  `exact iff_of_true … (mem_univ x)` (oaiq-078, -079, -092); a root name Mathlib added since collides with
  OpenAI's under an `open`: `harmonic` with `open Harmonic` (oaiq-086, ~30 sites), `rotation` with `open
  TraceHessian` (oaiq-091): qualify it; a `local instance` whose explicit arguments typeclass synthesis cannot
  infer is now an error: make it a `theorem` (it never fired; oaiq-091, -092); `simpa [..] using X` reporting
  `(f ∘ g) / (f * g)` against a lambda: `exact X` (defeq; ~25 sites in oaiq-091's Sobolev modules);
  `norm_num` on `Fin` literals is rewritten by the port since 1a89f36 (below); still by hand: a bare `(by
  norm_num)` whose goal is a Fin literal fact (`(190 : Fin 768) ∉ list`, oaiq-081: `first | decide | norm_num`),
  and a non-terminal `norm_num` after `fin_cases` (more tactics follow in the block); `Finset.sum_le_sum_of_injOn` is gone (`sum_image` + `sum_le_sum_of_subset_of_nonneg`);
  `decide (G.Reachable …)` under `omit [Fintype V] in` needs `@decide _ (Classical.propDecidable _)` (oaiq-089);
  `liminf_le_liminf (hu := …) (hv := …)` has the two names swapped; `MemLp.smul` takes the function first;
  `toReal_eLpNorm` and `summable_norm_of_tsum_eLpNorm_ne_top` gained a measurability argument;
  `List.Pairwise.rel_getElem_of_lt h …` is `List.pairwise_iff_getElem.1 h _ _ hi hj hij`;
  `Nodup.eq_of_getElem_eq` is `(Nodup.getElem_inj_iff …).1`; `exists_contDiff_support_eq_eq_one_iff` is
  `exists_contMDiff_support_eq_eq_one_iff (I := modelWithCornersSelf ℝ E)` with `contMDiff_iff_contDiff`;
  `mem_closedBall_zero_iff` on a submodule subtype needs `(E := ↥S)` (oaiq-092); `ModelWithCorners.MfldCat` is
  missing (oaiq-091 patched in a local structure for its one model); `MemLp g p μ` is a pair (a bare `lt_top` proof needs
  `⟨hg.aestronglyMeasurable, _⟩`), `MemLp.mul` swapped its factors; `norm_num [table defs]` leaves `vecCons`
  lookups or `Int.toNat 205` unevaluated where `simp [same]` evaluates them (oaiq-033/038); `rw
  [AddMonoidAlgebra.coeff_zero]` on an `MvPolynomial.coeff` goal is `MvPolynomial.coeff_zero` (and `coeff_add`);
  `tauto` no longer unfolds an applied set-builder membership; `simpa only [ite_true]` no longer fires on an
  `if True` whose `Decidable` instance is not the standard one (use `↓reduceIte`, oaiq-056); a multi-line `convert … using 1; first | rfl |
  ring` closes only the first goal (use `<;>`) (oaiq-045); `omit [BorelSpace E]` on a lemma that uses stdGaussian
  (oaiq-048); `omit [CompleteSpace H] in` where our order on `H →L[ℂ] H` needs it: remove only the `omit`s Lean
  rejects, never all (`~/claude/p2m-standalone/openai-ports/oaiq-039/fix_omits_from_errors.py` writes those patches from a module's errors); an instance
  body `by unfold; infer_instance` on a type synonym breaks `simp`/`rw` instance matching, `inferInstanceAs` fixes
  it (oaiq-075); the port's `first | infer_instance | exact Measure.isProbabilityMeasure_map …` line times out at
  `whnf` when the measure is a `let`: name `Measure.isProbabilityMeasure_map hφ.aemeasurable` (oaiq-074).
- *Rewritten by the port since 2026-10-30.* `convert h using 1` + `· rfl` / `· ext x …` on a `HasDerivAt` /
  `HasFDerivAt` goal becomes `h.congr_deriv (Eq.symm ?_)` (`congr_fderiv`, or `(h.congr_of_eventuallyEq …)
  .congr_deriv (Eq.symm ?_)`), keeping convert's orientation `goal' = h'` (8fdf735; before it was `h' = goal'`,
  and hand patches adding a `symm` for that now count 0: drop them). A terminal `norm_num [L]` / `norm_num … at
  …` after `fin_cases` (also a `<;>` chain continued over lines), or one whose list names a `Fin.` lemma, becomes
  `first | (simp L; all_goals first | (norm_num L; done) | rfl | decide) | (norm_num L; done) | norm_num L`
  (1a89f36; 1,278 sites in openai/math; this Mathlib's `norm_num` runs no simprocs): drop hand patches
  `norm_num [L]` → `simp [L] <;> norm_num` at such sites. `List.TFAE.out N M` → `.out (N-1) (M-1)` (e359e08;
  d13f23b counts from 1). A hand patch dropped for too few occurrences prints `why:` in filter-patches: the rule
  that now rewrites its site and what the port writes there, or "not in the port's input"; check the new text and
  drop the patch rather than marking it `allow_drop` blindly (oaiq-090). `core_rewrites` is not idempotent as a
  whole (the argument-dropping rules drop again): never re-run it on ported text.
- *Rewritten by the port since 2026-10-28* (f6bb691, d0c5d2c, f76350b): the `Measure.map` fallback tries
  the mapped function's named measurability facts first (a hypothesis about it, or a `foo_measurable` /
  `measurable_foo` lemma anywhere in the port), then a bounded `infer_instance`, then `AEM_TAC`; also
  `inferInstanceAs (IsProbabilityMeasure (_.map _))`, `by unfold foo; infer_instance`, and the dot form
  `μ.map F` where `μ` is bound as a `ProbabilityMeasure`; `MemLp.mul`/`fun_mul`/`mul'` by argument name in our
  factor order; `Submodule.isTopologicalAddGroup` (now `topologicalAddGroup`), `LinearMap.coe_ofClass`,
  `Ordinal.lt_wf.induction` (now `WellFoundedLT.induction`, case `ind`), `unifIntegrable_iff.2`,
  `cgf_gaussianReal`, `isProbabilityMeasure_of_map`, `FiniteMeasure.mass_map_le`, `lintegral_bind_le`,
  `lintegral_map_le` (compat lemmas with d13f23b's signatures), `simp [ite_true]` gains `if_true` (ours
  takes only the standard `Decidable True`), `Finset.antidiagonal` outside Hahn-series files. Left by hand:
  a `measurability` fallback can still hit maxRecDepth when no named fact exists.
- *Drift verified but not automated* (needs types or a compat lemma): `unifIntegrable_iff.mp`/`.1` (ours has
  no iff: our `UnifIntegrable` is the real ε-δ, measurable-set, indicator form; a safe special case is
  `unifIntegrable_iff.mp hf.1` → `hf.unifIntegrable`); `UniformIntegrable` has three components here, two in
  d13f23b (`.1`/`.2` shift); `HasGaussianLaw` has one field, `isGaussian_map` (drop the `aemeasurable`
  component of a constructor; `HasGaussianLaw.aemeasurable` is a lemma); `LinearPMap.ker` and its lemmas are
  gone (`inverse_graph` and friends take `f.toFun.ker = ⊥`); `dite_true` takes only the standard instance;
  `toSSetObjEquiv` on singular simplices needs a subtype-to-structure bridge in `--stdsimplex auto` (oaiq-066:
  compose with the homeomorphism and add a naturality lemma; an import of `StdSimplexTopCompat` cannot be
  patched in, so inline it); `norm_num` no longer closes a constructor disequality of a local `inductive`
  (`IV.box a b ≠ IV.unk`, not even with `reduceCtorEq`): `nofun` / `⟨nofun, …⟩` does (q133, one site).
- *The real-valued `Lp` norm* (q136: 18 patches in 13 modules, five build rounds; oaiq-005, -062 and q141 hit it
  too). `lpNorm f p μ` is `if AEStronglyMeasurable f μ then (eLpNorm f p μ).toReal else 0`, so `toReal_eLpNorm`
  takes `hf` (a bare `rw [← toReal_eLpNorm]` leaves a side goal or makes no progress) and `lpNorm_congr_ae` cases
  on measurability; `eLpNorm_indicator_const` takes `MeasurableSet` (the null-measurable form is `…_const₀`); a
  `MemLp` built from the norm bound alone needs its measurability half, `⟨hg, …⟩`; some lemmas *dropped* the
  argument instead (`eLpNorm_eq_lintegral_rpow_enorm_toReal`, `Lp.eLpNorm_le_of_ae_tendsto`,
  `Lp.eLpNorm_lim_le_liminf_eLpNorm`). Several are port rules now (0888a41, af5cc81, 7a21c26); for the rest, when
  a port fails on one of these names, `rg` the whole port and repair every site at once, since a failing module
  hides its importers' failures until the next round.
- *A Mathlib definition that changed shape* (not a renamed lemma) wants a **shadowing shim**, not per-site
  patches (q141: d13f23b's `UnifIntegrable`, `UniformIntegrable` and `UnifTight` at about 260 sites in 80 of 526
  modules, after oaiq-080 spent 3.3 h patching sites). Write a module under `OAI` with the old shape and its API
  proved from ours: inside `namespace OAI` a declaration `OAI.X` wins over `open MeasureTheory`'s `X`, so bare
  names need no rewriting. Check the d13f23b source of the definition first. Models: `StdSimplexCompat`, and
  `UnifIntegrableCompat` (00f2d9c, 64c9ae2; opt-in per carve, pipeline.json `"unif_integrable": "on"`; each
  construction site needs one measurability line, and a lemma concluding `UniformIntegrable` from `eLpNorm`
  estimates alone gains a measurability hypothesis). Making it the default would re-port the carves that
  hand-patched uniform integrability, so it stays opt-in until those are published.
- *When a port rule matches a tactic spelling*, `rg` the port for the unspaced and variant spellings of the same
  tactic (q133: `; first|…` without spaces escaped the `; first | …` rule, 8af004c).
- *A simp-family step now closes the goal*, so its `; ring` fails "No goals" (oaiq-098: BasisIntervals,
  NodeIntervals). Port rule `_simp_semicolon_closer` (a910463): `simp`/`norm_num`/`field_simp`/`push_cast`/… `;
  ring` (or `ring_nf`, `linarith`, `positivity`, …, chained) becomes `<;> …`, a no-op on no goals and the same on
  one; after a `<;>` chain only where the line ends its block. It changes meaning only where the simp step closed
  one goal of an unbulleted block and the closer was meant for the next: a build error then, not a silent change.
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
  unpatched port turned into `patches.json`: `scripts/mkpatches.py PRISTINE REPAIRED OUT.json` (PRISTINE is
  the port run with patches `[]`; it grows each hunk's context until `old` is unique and not cut mid-identifier,
  merges into an existing OUT.json, and checks the result reproduces the repair byte for byte; oaiq-043, -080).
- *A `have` that states a hand-written `match`* (`have h : … (match vs with …) …; simp_rw [h]`) breaks when the
  function whose body has the same `match` comes from a bundle: Lean shares a matcher only within one module
  (oaiq-018). Patch the generated piece (config `patches`) with a defeq congruence instead of the rewrite.
  Same cause for a `simp only [hb]` whose `hb` mentions a `match` lambda (oaiq-087): close with `change`/`exact`/
  `refine Eq.trans (congrArg …) ?_`, which unify up to defeq.
- *Failures only in the carved bundle or piece*, never in the module build of the port (oaiq-085, -086, -087).
  Besides matcher sharing: two global instances on one carrier that no OpenAI module saw together become
  visible together ("synthesized type class instance is not definitionally equal"): compare the two names in the
  message and give the one the original module order preferred `priority := high` by patch (oaiq-086; making the
  other local broke its users); `Finset.filter` goals differing in `DecidablePred` instances: `congr!`; a
  `Subsingleton.elim` rewrite of a `Fintype` instance whose direction flips between the two contexts: `first |
  exact hh | (convert hh; all_goals first | rfl | exact Subsingleton.elim _ _)`; `Function.update` with
  `FunLike.toDecidableEq` vs `Classical.propDecidable`: `convert` where `exact` fails. The patch must keep the
  port's module compiling too. Test it on the stage file before another re-port and re-measure (about 15
  minutes): `LEAN_PATH=<carve>/olean:$(lake env printenv LEAN_PATH) lean -j1 -DautoImplicit=false <stage file>`
  from the workspace, with `~/claude/claude-private/tools/lean-cap` first on PATH (`which lean` shows the wrapper;
  `lake env env … lean` runs the toolchain's lean outside the cap, oaiq-114). Other carve-only causes: dot notation
  on a `def`-typed value (`ψ.map_zero`, `ψ : Nakayama …`) resolves to a `Nakayama.map_zero` the carved file now
  declares first, where the module had fallen through to `LinearMap.map_zero`: write `LinearMap.map_zero ψ`
  (oaiq-116); a `local notation` written with another local notation is dropped when the statement is carved,
  while the piece copying the whole module keeps it, so scope an insertion patch by its preceding context
  (oaiq-081); a `local instance : Coe …` or `@[local gcongr]` leaves no constant in the term, so it does not
  travel: a post-carve patch inserting `private local instance …` (private, or every bundle holding it declares
  it again) and `exact` in place of the `gcongr` (oaiq-096). A line patch whose `old` is also the tail of a
  more-indented line double-counts: anchor it with a leading `\n` (oaiq-086).
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
  exits 4 still running: re-arm that. Arm the wait with the Bash tool's `timeout` set above the wait (e.g.
  7000000 ms for `--wait 100`): without it the harness stops a background command after 10 minutes (q137). A Bash
  background command dies at 2 h, and that killed drivers mid-build
  and mid-graph on every port over ~300 modules (oaiq-033..049); a killed wait costs nothing. Since a932a18 the
  build leaves `graph` its LeanInfo reading, so `graph` takes seconds after a build.
  `--wait` reports only its own run (never while the unit is active, and it says when the run had already
  ended); `--detach` refuses at once with exit 3, naming the pid and command line of a driver that holds the
  carve: stop that one or wait for it (oaiq-084; 1a4f175).
- **The carve's own section on the monitoring page** (2026-10-30): the driver publishes `carve-<hash>` (the
  unit's hash; p2mlib.carvemonitor) with the current step, steps done, modules built, items measured of planned,
  items live of the plan and its processes, refreshed every minute and at each step boundary, and marks it done
  or failed with the stopping reason; `split_run --go` keeps the counts current while a background publisher
  outlives its driver. A worker's own section need not repeat any of that. A carve on a snapshot from before
  it shows no section until it is resumed with `--upgrade`.
- **What re-runs by itself after `--upgrade`** (2026-10-29, oaiq-047/-085/-092). `port` and `filter_patches`
  record the port rules and options they ran with, so a skill fix to a port rewrite re-ports without `--redo
  port`; a re-port that changes no module's text rebuilds nothing. Once publishing has started a rule change keeps
  the port: `--redo port` only deliberately. "Started" is a state fact (`pipeline_state.json` `publishing_started`,
  since 2026-10-29), set the first time publish or publish_early runs or `publish/run_state.json` or config `frozen`
  is seen, and kept: a frozen re-plan drops publish_early's record, and with no run state written yet a rule change
  had counted as safe to re-port. After it a changed input from outside (an edited patches file, a port folder
  rewritten under the carve) stops the run until you `--redo` that step. A carve that has planned and measured
  should take new tools with `--upgrade --keep-port`: the port stays as it is across rule changes, on that run
  and every later one, until `--redo port` or `--redo filter_patches` (`pipeline_state.json` `keep_port`; before
  2026-10-29 it held only until the next skill commit). oaiq-081: the new compat rules changed port_patches.json
  and most modules, which would have rebuilt and re-planned 1,586 measured items. filter_patches' rule input is
  carve_prep.py's filter-patches code only, no longer the whole file. A change to
  `LeanInfo.lean` re-runs `graph`, with a warning giving the module count, while a step that loads the graph is
  still to run; a `config.json` that `--redo config` changed re-runs from `extdefs`. A rebuild keeps the replayed
  modules' times in `build_elab.log`: carves built before 2026-10-29 can have a log missing most modules (oaiq-047:
  37 of 1,259), which costs each at a default 2 s, so run `--redo build` once before planning such a carve again.
  The build depends on nothing of the skill snapshot (not LeanInfo, not the snapshot path): an unchanged port
  replays. What rebuilds everything is a changed `lean/compat_4_34.lean` (44 changes since 2026-10-20): a re-port
  rewrites `Compat.lean`, which every module imports (oaiq-088: four full rebuilds of 2,385 modules, each starting
  `Built …Compat`). The driver warns when a re-port would do that; on a built carve use `--upgrade --keep-port`
  unless the new shims are needed (df97e19). Every plain `--upgrade` of a built carve re-ports (oaiq-098: two
  11-hour rebuilds of 564 modules, the second only to pick up a planner fix). When a built carve needs a missing
  Mathlib name, add it to `compat_4_34.lean` (with its test) for later carves, but in this carve declare it by a
  port patch in a common ancestor of its users (oaiq-107: 9 users of `SimpleGraph.ncard_neighborSet` among 444
  modules that all import Compat). A LeanInfo change re-elaborates the whole graph (oaiq-081: 3,092 modules): a
  large published carve that needs one tool fix takes it on a private snapshot, `--snapshot <commit>`, rather than
  a HEAD that also changed LeanInfo. After a build failure, skipped importers hide the next errors: stop the
  driver after each fix (`systemctl --user stop carve-<hash>`) and resume rather than waiting for the build to
  end (oaiq-107). An in-place `lake build` of the root to see them all can invalidate the pipeline's oleans
  (q128: a full 70-minute rebuild; q136 got away with it): build single modules in place instead. `names` prints progress and runs four lookups at a time. A
  kinds-limited `measure` judges only its kinds' edge records (oaiq-081), and a cached ok is reused only while its
  `.olean` exists, so a repair cut needs no `times.json` edit (oaiq-096; 17b6d76).
- **The port folder has an owner; rehearse on a copy only with its own workspace** (2026-10-29). The port writes
  `WORKSPACE/Solutions/FOLDER`, outside the carve dir, and a `cp -a` copy of oaiq-081 still on the shared
  workspace re-ported and rewrote 228 files of the live carve's folder (its config.json also named the original's
  `out/` and `work/`). Now `Solutions/FOLDER/.carve_owner.json` names the owning carve directory, and the driver
  refuses before any step when the folder belongs to another carve, config `out`/`work` lie in another carve, or
  config `src` is not the run's workspace.
  A folder from before has no owner file: the carve whose recorded port hash it holds, and whose `logs/port.log`
  names no other carve, adopts it on its next run; otherwise `--claim-folder` (also to take a folder over on
  purpose, e.g. an extension carve on its parent's port). A moved carve keeps its folder. To rehearse: copy the
  carve, point every absolute path in the copy's `pipeline.json` and `config.json` (`out`, `work`, `meta`,
  `patches`; `src` at the new workspace) at the copy, and run it with `P2M_WORKSPACE` set to a workspace of its own holding the folder (and
  its `.lake` build) as copies; never on `~/claude/prove2me_workspace`.
- **Missing prose stops `check_text`**: the "needs written prose" lines name the files to write (forced and goal
  items), and check-text and the dry run fail (MISSING / CANNOT BE SENT) until they exist, in any wave, not only
  the first (oaiq-047: twelve forced statements passed both, then blocked the live run; eafc6da).
- Parameters live in `DIR/pipeline.json`: a different CLI value is refused, so edit the file. A changed
  `config_set` in pipeline.json reaches config.json on the next resume by itself, without re-running `config`
  (which would reset calibrate's `time_scale`): `patches` re-runs from `gen`, any other key from `plan`
  (oaiq-051). `measure` keeps going past a failing file and lists them all. Editing the patches file and resuming re-ports (stale-step detection). `--def` takes
  `Definitions.Def_X` (a bare `Def_X` is read so); `--measure-flag` takes the `=` form. `oai_meta.json`
  `prefixes` are the port's own prefixes, `OAI.<top directory>` (what `oai_port_modules` strips, e.g.
  `OAI.Algebra`), never the result's folder: step `config` refuses another value (oaiq-031: 181 links
  repeated a directory). Each step is idempotent, logged in
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
  at a fitted scale. A piece measured under 120 s (`PIECE_CAP`, 150 s before 2026-10-29) never counts: it is a proof, resubmittable, so submit
  it as is and split only after two real verifier timeouts; bundles and statements freeze at publish and
  keep the strict limit (oaiq-035/037: a 106 s piece cost two hour-long re-plans; oaiq-031: a 192 s piece
  timed out three times at the verifier's 300 s, so the cap is 150, not 200). When only pieces are over,
  calibrate stops at once: re-planning re-splits bundles but has never shrunk a piece. Then force the heavy
  lemmas the piece keeps into statements of their own (`forced` in pipeline.json; a private one by its graph
  node name, `_private.<module>.0.<name>`, published without the prefix) and resume `--from config`.
  Kernel computation (`decide +kernel`, `native_decide`) is the usual cause, since the cost model cannot
  see it: oaiq-031's piece of 20 private `decide +kernel` lemmas became 20 pieces of ~11 s, with the plan's
  bundles unchanged, so live bundles kept their text. `accept_over` in pipeline.json excuses another item
  (`bundle:NAME`) under a 200 s cap. Outside the pipeline the
  manual rule is the same: measure everything, and if any bundle or statement is over ~90 s, multiply
  `time_scale` by the worst measured/planned ratio and plan again.
- **Overlap mode: bundles and statements publish while the pieces are measured** (dbenbenn 2026-10-29: "a slow
  proof really shouldn't need to block submitting definition bundles"; oaiq-081 had all 194 bundles and 696
  statements fine after ~1.5 h of measuring, then ~4 h of pieces and five slow ones before anything could go).
  On for every carve created since then (`pipeline.json` `"overlap": true`, written at the first run; `--no-overlap`
  to opt out); a `pipeline.json` without the key is a classic carve and stays one, `--upgrade` included; add the key
  by hand to switch a carve that has not published. The steps:
  `measure` (`--kinds bundle,statement`), `calibrate` (those only), `publish_prep`, `prose`, `check_text`
  (`--kinds bundle,statement`: written prose for forced *statements* is needed now, explanations later), `dryrun`
  (`publish/run_early.json`), `publish_early`, `measure_pieces`, `calibrate_pieces`, `pieces_prep` (publish-prep
  `--sync`, prose-template, check-text of the explanations, the full dry run), `publish`.
  - `publish_early` (only with `--publish`) first freezes what it publishes: `DIR/published/` keeps the plan and the
    lib files, and config `frozen` (that plan, all its bundles, `published/lib`), `forced` (its statements) and
    `template_forced` (those not named in `forced` by you) are set, recorded in `pipeline_state.json`
    `auto_config` and re-applied whenever config.json is rewritten. Then it starts the background publisher,
    `split_run.py publish/run_early.json --go`, as its own systemd user unit `carve-pub-<hash>` (output
    `logs/publish_early.log`, progress `publish/PROGRESS.log`). Pieces are held by the gate
    (`publish/release.json`, see p2mlib.splitrun) until `publish` releases them for exactly this plan; the
    publisher ends once nothing but held pieces is left. `split_run --go` now holds a lock per `publish/`, so a
    second publisher (the final one, or one started by hand) exits 3 while the background one runs.
  - A failure after `publish_early` (a piece that does not compile, a missing explanation, a slow piece) stops the
    driver at once, and the publisher goes on; `--wait` and the failure message say so. Fix and resume as usual;
    steps that write `publish/` sync it (atomic file replacement), never rebuild it, and stop if a published
    bundle or statement file would change (`gen` checks the same right away). `publish` writes the release, waits
    for the background publisher to end (it sends the pieces itself if it is still running), then runs the
    final `split_run publish/run.json --go`, which resumes.
  - Pieces publish as one final wave once every piece fits, not one by one: calibrate judges the pieces as a set,
    a remedy re-plan changes piece files and their imports, and a piece cannot go before its statement is live
    anyway, which phase-1 publishing usually outlasts.
  - **A slow bundle** in `calibrate`: if at least three bundles and a quarter of the measured ones are over the limit
    (a systematic cost-model error, batch 3) and nothing is published (no publishing started, no config `frozen`),
    the global re-plan at a larger `time_scale` as before; otherwise each slow bundle is split alone
    (`carve.py split CONFIG TIMES --limit BUDGET --only NAMES`, up to three rounds): every other bundle keeps its
    declarations, name and imports, so only the files importing the split one change and are measured again.
  - **A slow piece** in `calibrate_pieces`, nothing published: as before (a uniform overrun re-plans at the ratio, a
    lone one stops with the profiling hint). Once published, nothing is re-planned globally: each slow piece gets
    one frozen re-plan in which only its own declarations (`keep` in the plan) cost its measured / planned ratio
    (config `cost_factors`, `pipeline_state.json` `auto_split`), so the planner promotes lemmas inside it to new
    statements (template prose) and nowhere else; at most two such rounds. It stops for a person, naming the
    piece and why, when a piece is still over after its split, or its statement alone takes half its time (the
    type is the cost: `abbrev`s cannot be added to a live statement; `theorem _root_.solution` halves the
    serialization), or the rounds are used up. Remedies then: `accept_over` (`piece:NAME`, under 200 s), or forced
    lemmas in `pipeline.json` `forced` plus `config_set.template_forced` and `--from config --publish`.
  - **Switching a classic carve** that has not published (oaiq-081, 2026-10-29): wait for its driver to end (`--wait`),
    add `"overlap": true` to `pipeline.json`, then `carve_pipeline.py DIR --upgrade --keep-port --publish --detach`.
    A finished `measure` stands (one that failed re-runs for bundles and statements, all cached), the plan is
    kept, and the run goes on from the phase-1 `calibrate`; `measure_pieces` finds the pieces cached. Rehearsed on a
    copy of oaiq-081: HEAD's `gen` writes its 1,617 files byte for byte, and only unmeasured items compiled. If the
    classic driver got past `publish_prep` (from a skill before overlap mode: no `publish/run_early.json`), add
    `--redo publish_prep`; `publish_early` refuses without that file rather than start a publisher that dies.
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
    avoid tokens full Mathlib adds (`Δ_[1]^[n]` → `Δ_[1] ^[n]`; the port escapes a bare `variables` as
    `«variables»` and an index `c[j]` as `(c)[j]`, oaiq-082), and drop a theorem a published
    bundle already declares. Config `external_defs`, `statement_suffix`, `patches` (post-carve
    proof fixes) support a fresh split beside an abandoned one.

## Slow or odd failures: what to try first (worker lessons, 2026-10-28)

- **Calibrate's two outcomes for pieces** (classic carves, and overlap carves before anything is published; once
  published, an overlap carve splits each slow piece by a frozen re-plan by itself, "Overlap mode" above, and stops
  with this list only for what that cannot fix). When three or more pieces are over the plan by a similar factor (median
  ≥ 2.5, spread ≤ 2×), the plan's cost model was off and calibrate re-plans at that ratio by itself (oaiq-073).
  A lone slow piece, or a scatter, stops it with a profiling hint: re-planning has never shrunk one. In order:
  1. `lean -o x.olean -Dprofiler=true FILE` (with `LEAN_PATH=<carve>/olean:$(lake env printenv LEAN_PATH)`).
     If `.olean serialization` dominates while elaboration is fast (oaiq-075: 316 s of 328, `sorry` just as slow),
     the statement's *type* is huge: print `Expr.sizeWithoutSharing` per binder (`forallTelescope` in a
     `#eval show MetaM Unit`). Only declaration *types* cost: the same term inside a proof or as a definition's
     value writes in 0.2 s (opus-kadison: 105 s as a theorem's type). Remedy: `abbrev`s naming the large sides or
     subterms, in a bundle (in the same `attribute [-instance]` context as the stubs), and the statement restated
     with them; its piece starts with `unfold` of them, and importers still work, even `with_reducible exact`,
     since an `abbrev` unfolds at reducible transparency. When the large part is the conclusion under binders,
     name the *whole conclusion* as a `Prop`-valued `abbrev` taking the binders (q140: 5.9e9 nodes to 6.3e3,
     serialization 316 s to 0.4 s; an `abbrev` of the large subterm alone only halved it, since every instance on
     the subtype embeds it again); measure `sizeWithoutSharing` per binder and of the body first. Give the
     `abbrev` a type ascription and copy every instance binder the statement has (`[IsClosed (B : Set _)]`),
     else its body elaborates with a metavariable or another instance path and the importers stop matching.
     Where the type cannot shrink (a frozen statement),
     declaring OpenAI's theorem directly as `theorem _root_.solution` instead of `<name>_oai` plus a `solution`
     copy halves the serialization (98 s to 61 s). Profile the `chk/` file whose name matches the current plan:
  earlier plans' files stay there (oaiq-078). A *statement* over the limit stops calibrate: it publishes,
     but every verify that imports it times out compiling it. Never `forced`:
     the item is already one small proof.
  2. `lean -Dtrace.profiler=true -Dtrace.profiler.threshold=20000 FILE` names the slow tactic with its position;
     plain `-Dprofiler` gives only the cumulative "type checking" (oaiq-074: one `fun_prop` measurability goal
     took 53 s; `Real.continuous_exp.aestronglyMeasurable` as a term fixed it).
  3. No heavy declaration, just many small lemmas: force two or three mid-chain theorems (`forced`, chosen by
     transitive-closure size at about 1/3, 1/2, 5/6 of the total; oaiq-031, oaiq-074). Verifier data
     (oaiq-078): pieces at 118-126 s local CPU timed out three times; 93.7, 99.6 and 102.7 s passed first time,
     so the real limit is about 100-110 s, below `PIECE_CAP` (120 s since 2026-10-29, above the limit on purpose so that a borderline piece is tried before it is
     split). Chains of `decide +kernel` theorems are worse: pieces at 97-130 s (oaiq-084) and 147-186 s
     (oaiq-047) timed out three times each; forcing every kernel theorem the piece keeps (or a fraction of them,
     evenly spaced: `~/claude/p2m-standalone/openai-ports/oaiq-047/resplit_prep.py`) brought them to 85-97 s and all passed first time. In a
     kernel-heavy carve, force them at the first plan rather than after the verifier's timeouts. Big carves take
     time: a 1,300-module carve took about 20 driver restarts and two days at load 15-22 (oaiq-050).
- **Calibrate stops on a bundle splitting cannot shrink** (df97e19): a slow bundle down to one declaration, or one a
  split round returned unchanged, is not split again; once only such bundles are over, calibrate profiles each once
  (`carve_measure.py CONFIG --profile bundle:NAME`; `work/profiles.json`, `work/profile_<name>.log`) and stops with
  the diagnosis naming the declaration: serialization-bound (name the type's large sides with `abbrev`s by post-carve
  patch, oaiq-124), kernel-bound (rewrite it, or `cost_factors` + `accept_over`, oaiq-092) or elaboration-bound. The
  automatic frozen split of a slow piece also promotes its private lemmas (config `promote_private`, graph node
  names), so no hand `forced` entry is needed for them (oaiq-091).
- **A slow, memory-heavy piece with a short tactic proof** (oaiq-123: 281 s, ~22 GiB): compile it with `set_option
  debug.skipKernelTC true in` on the theorem. If that makes it fast (4 s there), the kernel is re-evaluating a
  certificate term a cheap `simp` left behind (`simp only [List.sum_cons]` over `[augmentation (residualBucket 0),
  …]` made the kernel compute what the cached `bucket_aug_k` lemmas exist to avoid): rewrite the cached-value
  lemmas in before any arithmetic `simp` (3 s). On a loaded machine bisect with `sorry` truncations under
  `timeout 300`, not the profiler.
- **Kernel time is invisible to the cost model** (oaiq-092, oaiq-114). `lean -Dtrace.profiler=true
  -Dtrace.profiler.threshold=4000 FILE` prints `[Kernel] typechecking declarations [X]` lines: single opaque
  `Procedure …` defs and one `structure … : Prop` took 23-474 s in oaiq-092, and splitting a bundle cannot get
  one declaration under the limit. Rewrite the heavy declaration by patch (state the function up front instead of
  leaving the kernel to unify it), else `cost_factors` + `accept_over`. The `.olean serialization` case above
  applies to bundles too (oaiq-124: a one-theorem bundle at 92 s, `sizeWithoutSharing` 2.0e9; an `abbrev` for
  the map in the same bundle brought it to 55 s). Kernel pieces are load-sensitive (42 s measured, 85 s on a
  rerun, three verifier timeouts): profile any kernel piece over ~30 s. A `decide` on `Finset.card` or Finset
  equality over a long `List.toFinset` is quadratic in the kernel; when the list is sorted, prove `Nodup` from a
  strict chain (`List.IsChain (toLex · < toLex ·)` by `decide +kernel`, `List.isChain_iff_pairwise`) and use
  `List.toFinset_card_of_nodup` (85 s to 0.3 s). In a kernel-heavy development, force the source's own block or
  merge lemmas at the first plan (oaiq-114: 31 of them, every piece under 42 s, Proved in 80 minutes).
  A piece that measures under the limit but times out on the verifier, with elaboration a few seconds and the rest
  "type checking", is kernel-bound in one or two terms (oaiq-081, q131: 55-99 s locally, three verifier timeouts
  each). Bisect with `sorry` truncations, two variants at a time; splitting cannot help a single slow term.
  q131's case: a generic lemma about `compiled c` applied to a *constant* (`highLoop`) defined as `.seq A B`,
  with hypotheses proved for `compiled (.seq A B)`; the elaborator accepts it at once, the kernel compares the
  two compiled tables for minutes. Move the step into a local `have generic : ∀ {c first second …}, c = .seq
  first second → … := by intro …; subst hceq; exact …` and apply it as `generic (c := highLoop) rfl …` (134 s to
  0.07 s): the kernel checks the lemma on variables and a one-step `rfl`. No declaration is added, so the plan
  is unchanged.
- **Category theory / homological algebra: try the transparency option first** (oaiq-116). Errors full of `simp
  made no progress` / `rewrite failed` on `comp_f`, `ShiftedHom`, `Cocycle`, `single…` lemmas are the "not
  type-correct under the `implicit` transparency level" check, not API drift: compile each failing module as is
  and with `set_option backward.isDefEq.respectTransparency false` at module scope and keep the version with
  fewer errors (`scripts/try_module.py FILE [--show LINE,...]` does both, with the pipeline's `-j1 -DautoImplicit=false`
  and through the lean-cap wrapper, and names the version with fewer errors); where the option
  breaks later steps, scope it with `set_option … false in` per declaration. Since f252eeb the pipeline's build
  does the first half by itself (q128: a chain of 15 such modules surfaced over seven build rounds, three hours): a
  module failing with the transparency note is compiled again with the option at module scope, and if that
  builds, its `.olean` stands in so its importers build in the same round. The module is still reported as failed
  ("builds only with the transparency option … needs a patch", listed together in the last line), so the build
  step stops until each gets its port patch (`openai-ports/q128-finitistic-retry/add_option_patch.py` writes them). oaiq-002's "several more hours" of
  drift became 2 hours. Repair with the pipeline's own flags (`lean -j1 -DautoImplicit=false`): a `-j1` build can
  hit heartbeats an in-place `lake build` does not.
- **`(kernel) deterministic timeout` where the elaborator accepted every step** (oaiq-068): typically a goal
  equating `f a i₁` with `f a i₂` for two proofs of a Prop-valued instance argument (a `letI … := h ▸
  inferInstance` in two statements). State the irrelevance as a lemma, `@f … i₁ = @f … i₂ := by cases
  Subsingleton.elim i₁ i₂; rfl`, and chain with `.trans`, so the kernel never compares the proof terms.
  Bisect by `sorry`-ing the tail of the proof (about 40 s a trial; three variants in parallel).
- **"failed to synthesize" an instance in a bundle at `measure`**: read `work/repairs.json` first. A REPAIR that
  deleted an `omit`/`include`/`variable` line changes the signatures of everything after it in that section, so
  the error surfaces in a later file (q139: a broken `omit […] [D]` was deleted, `at_correct` gained three
  instance arguments, and the failure showed six bundles later, followed by 23 "olean does not exist"). The
  carver now drops only the binder holding the gone class (df42c97).
- **"maximum recursion depth" at a line that looks fine**: the position can belong to a later declaration;
  bisect with `#exit` cuts (oaiq-080, where an `IsProbabilityMeasure` instance that is false here made
  `infer_instance` loop).
- **A tactic defined by `syntax` + `elab_rules`** (oaiq-076): the port builds but the carver and soundness
  guard refuse the commands, so the bundle says "unknown tactic". Replace the tactic at its uses with a
  combinator of existing lemmas, `iterate N (all_goals first | with_reducible exact l₁ _ | with_reducible
  apply l₂ | … | with_reducible fun_prop | fun_prop)`, and delete the block with a patch. `with_reducible` on
  each `apply` matters (an unrestricted `apply` unfolds projections and times out in `whnf`); test the fix in
  the carved bundle's context (a scratch file importing `<carve>/olean`), since its `attribute [-instance]`
  lines change what `fun_prop` finds.
- **OpenAI lemmas that are false as ported** (oaiq-080). OpenAI's `eLpNorm f p μ` is `∞` for a
  non-`AEStronglyMeasurable` `f`; ours is a lower integral. So `eLpNorm_add_le`,
  `tendstoInMeasure_of_tendsto_eLpNorm`, `eLpNorm_mono` and lemmas built on them hold there without
  measurability and fail here (`f n = 0`, `g = 1_A`, `A` non-measurable of inner measure 0). The repair is no
  shim: each site needs a measurability fact of the limit, and lemmas that took arbitrary limits gain a
  hypothesis their callers pass. Likewise `μ.map Φ` is a probability measure there for every `Φ`, here only
  for an `AEMeasurable` one. `UniformIntegrable` has three components here, two there (the opt-in shim above restores d13f23b's shape). Budget a module-route
  port of an analysis development at about 12% of modules needing a hand repair, a third of them measurability.
- **Foreign packages** (oaiq-083). OpenAI's lakefile requires about twenty packages (PrimeNumberTheoremAnd,
  StrongPNT, RellichKondrachov, TauCeti, ClassFieldTheory, …) that the repo does not contain. `oai_fetch.py`
  exits 1 naming any root the closure imports that is neither OpenAI's nor in our toolchain. Put its sources
  beside `OAI/` in `src/lean` (the commit pinned in `lean/lake-manifest.json`, LeanArchitect annotations
  stripped: `~/claude/p2m-standalone/openai-ports/oaiq-083/prep_upstream.py`; the `Erdos970` forks are in `prove2me_workspace/Solutions/OAIChowla`)
  and resume; the port takes them as OpenAI's. With a local checkout at the pinned commit, `oai_fetch.py DEST ROOT
  --foreign <checkout>` (repeatable) copies the package's import closure itself and names any module the
  checkout lacks (oaiq-093: `Gromov.PolynomialGrowth`, a stray import to patch away). Packages written in the
  module system (`module`, `public import`, `public section`, `@[expose]`, `public def`) need no strip script:
  the port's `demodule` makes them plain (0edecdf, fb51151). LeanArchitect annotations still need
  `prep_upstream.py`. Very large closures with foreign packages (oaiq-093: 2,679 modules, OpenAI's Mathlib
  ahead of ours by missing structures such as `Group.Generators`) are a day's work, not a batch. Look for statements already published from them (the Chowla
  split) to use as `external_theorems`.
- **The CoeT WA: "failed to synthesize CoeT … timeout at `typeclass` (20000)"** (opus-kadison, oaiq-039; also
  Erdős 3 v2, oaiq-003 Rokhlin, oaiq-122, q129). The verifier's plain comparison of `solution`'s type with the
  target's fails for some polymorphic statements, and the fallback `CoeT` search then times out on a heavy type.
  That fallback reproduces exactly: it failed locally for precisely the 13 rejected statements of 246
  polymorphic ones, and the local check runs it (19c7a63), so carve_measure reports such a piece. **The cost is
  the type's unshared size** (q129, measured): the check fails even comparing a statement with itself;
  `isDefEq` takes 4 ms and the time goes to `synthInstance` on `CoeT T x T`, whose budget counts heartbeats,
  that is allocations, while it walks instance terms that are shared in the DAG as a tree. `(u v : unitary (Q τ
  ω)) : u * v = 1` over a `RingCon` quotient is 18.9M nodes and fails; `u = 1` is 8.5M and passes. COE_CHECK
  prints `sizeWithoutSharing` (facecb3). Remedies, in order:
  1. **Shortcut instances** for the carrier's algebraic classes, in a bundle the statement imports (a post-carve
     patch): `instance (priority := high) q129Monoid : Monoid (TracialQuotient τ l) := inferInstance`, plus
     `StarMul`, `Ring`, `Algebra ℂ`, …, in a `noncomputable section`. q129's statement fell to 2,613 nodes and
     passed, and the same shortcuts prepended to three slow pieces of the family cut their kernel time from 306 s
     to 170 s. Try them in slow pieces first: pieces are not frozen. (Proposed, not built: a pipeline.json
     `shortcut_instances: {type pattern: [classes]}` that emits this bundle.)
  2. State it monomorphically if every importer is (earlier probes with `{H : Type}` passed: smaller terms).
  3. Fold, last: folding makes the importers' pieces slow, the second blocker this family hit.
  CoeT failures come in families: after `measure_pieces` fails, list every FAIL of the run (`awk '$1=="piece" &&
  $4=="FAIL"'` from the run's `====` line) and treat them together (oaiq-122: 19 of 51 pieces, folded in three
  20-minute rounds from the driver's tail). Folding: `carve.py fold CONFIG NODE…` (config `folded`) folds the statement into every importer's
  piece, whose live statements stay, and only those pieces are resubmitted (through split_run with a
  `comparisons/` note on each, since the old sketches are live). Regenerate pieces of a published carve with the
  carve's own snapshot (pipeline_state.json `snapshot`): a newer carver emits more `attribute [-instance]` lines
  than the frozen stubs have. A re-plan with a snapshot older than 19c7a63 drops the fold.
- **CStarMatrix takes over `*` on Matrix products** (oaiq-092): Mathlib has `@[default_instance 100]` HMul instances on
  both Matrix and CStarMatrix, and for a product whose factor's dimensions are still metavariables the later one,
  CStarMatrix's, wins: `rw [Matrix.sum_mul]` fails with `CStarMatrix.inst…` in the error, while `#synth` shows
  Matrix's instance. `--compat-imports narrow` and `attribute [-instance]` do not cure it. Patch the failing module
  with `attribute [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid` after its imports (global:
  `local` is refused; it would turn CStarMatrix products in importers into Matrix ones). `oaiport.module_texts`
  can add it to every module naming `Matrix` (`matrix_default_instance=True`), off by default: one failure in
  about 11,000 such modules, and the attribute rides along in every bundle carved from them.
- **Platform lexer timeouts** ("Token scanner timed out after 10s", "Import parser timed out after 5s") on small
  statements are platform load and retried automatically (2675af1); an item an older snapshot stopped:
  `split_run.py publish/run.json --go --reset statement:NAME` once (oaiq-089).
- **Unused imports of a definitions bundle are kept** (oaiq-075, 733702b). carve_measure reports them and fails
  or cuts only false edges between statements: a later bundle's `attribute [-instance]` line can name an
  instance it sees only through that import, and cutting it broke 17 items with "Unknown constant".

- **The same theorem name in two modules is handled** (2ae7988; oaiq-088, -090, -095, -096). OpenAI's sibling
  modules, never imported together, can both declare `OAI.X.foo`; Lean keeps one constant. DeclGraph now records
  every copy; the carver keeps the name for the copy most modules see, renames the others `<name>_dup<i>` with the
  references that mean them, and `graph`/`plan` list each case (`DUPLICATE …`). No port patch is needed. A graph
  recorded before this change is re-run by the pipeline after `--upgrade` (DeclGraph changed) while planning is
  still ahead; a published carve keeps its graph.
- **Universes only under `max`** (oaiq-124): `plan` never makes such a theorem a statement on its own (it stays
  inside its importers' pieces, as a fold would put it); a target or forced statement with one gets a WARNING:
  fold it, or restate it with every universe bare.
- **A stale post-carve patch stops `gen`** (20365e5): a full `carve.py gen` fails when a post-carve patch matches
  no generated file and names it (oaiq-123).

## After publishing: re-splitting, extending, overlapping carves

From worker lessons oaiq-055, -057, -065, -067, -071 (2026-10-27/28).

- **Overlap-mode carves freeze themselves** (2026-10-29): once `publish_early` ran, config `frozen` and `forced`
  already hold the published plan, bundles and statements (`pipeline_state.json` `auto_config`), and a slow piece
  gets its frozen re-plan automatically (previous section). The recipe below is what that automates; it is still
  the way for classic carves, for a piece the automation hands back, and for real verifier timeouts.
- **Frozen bundles keep their old imports** (20365e5): with `frozen`, published bundles keep their old plan's
  imports, and `check_plan` no longer reports their inferred needs or cycles, unless the frozen carve used another
  external bundle (`frozen_external_conflicts`) (oaiq-120).
- **Re-split one item after real verifier timeouts** (two or more on a bundle or piece). Keep everything
  live as it is: in `pipeline.json` `config_set`, set `frozen` = {`plan`: a copy of the published
  plan.json, `bundles`: every live bundle, `lib`: `publish/out/lib`} and `forced` = the live intermediate
  statements plus the new ones you want (without the live ones the planner re-chooses intermediates by
  cost, dropping live statements and inventing new ones: oaiq-071). The config_set change applies on the
  next resume. Then `--publish --detach`: `--publish` always re-enters split_run, and an item stopped for
  a person whose file changed since is sent again by itself (both since 2026-10-28). `gen` needs each
  frozen bundle in `Definitions/`: `fetch_theorems.py --names Definitions.Def_X` (or the bare `X`) fetches
  it. `prose-template` skips `forced` nodes ("needs written prose"); for a mechanical split, generate the
  prose on a scratch copy with `forced` emptied and copy the files back.
- **Heartbeat timeouts on the server.** A bundle or piece that compiled in `measure` can still hit the
  verifier's `maxHeartbeats 200000` (oaiq-055: `rfl` lemmas, instance-heavy statements). split_run adds
  `set_option maxHeartbeats 1000000` after the imports and resends once; a second one waits for a person.
- **Extending another carve's frozen plan** (oaiq-088): a private node name embeds the old port folder
  (`_private.Solutions.OAIQ038_FA…`): rewrite the frozen plan's folder name to the new one, or a spurious import
  cycle appears; every `external_theorems` entry must exist in the new graph (drop those outside the new closure,
  else `unknown external definition`).
- **A later target of an already-carved family** (oaiq-057): extend it with the earlier carve's plan,
  bundles and lib as `frozen`; the planner takes the frozen plan's `external_defs` as its own (56fd083),
  so declarations the earlier carve took from a published bundle stay there. Not handled: a frozen bundle
  that imports one of the old carve's statements (then use a fresh `statement_suffix`). The pipeline's `names`
  step, right after `gen`, looks every planned bundle and statement up (read-only, a few minutes) and stops on
  one live with other text, before the hours of measuring (oaiq-068, -074): then a `statement_suffix` and
  `--from plan`, or extend the earlier carve as here.
- **Overlap with someone else's published work** (oaiq-067): `pipeline.json` `defs` replaces the list
  derived from the targets (keep the goal's own `Def_` in it); earlier published statements go in
  `config_set.external_theorems` (`{lean name: "Theorems.Thm_<name with _>"}`) after `fetch_theorems.py
  --names`; a bundle of another author that declares the same names as the goal's own bundle cannot be
  combined with it, so take a `statement_suffix`. Another user's *stalled* carve of the same goal (oaiq-082:
  ten bundles, a SKETCH_ACCEPTED goal reduction to three Open leaves nobody proved): do not extend their leaves;
  carve under a `statement_suffix` and add the second decomposition, whose goal piece goes in with a
  comparisons note (below) and was Proved at once, having no open leaf.
- **A goal someone else has already proved** (oaiq-068: four SKETCH_ACCEPTED reductions of the goal by others):
  split_run's piece is refused by the live-proof guard and waits. Read their proof; write
  `<carve>/publish/comparisons/<slug>.md` (beside `explanations/`), "Different from <id>: …" or "Same as <id>: …",
  and resume `--publish`: a "Different" piece is sent with that reason, a "Same" one is settled unsent.
- **Iterating on drift fixes:** edit the ported file in `prove2me_workspace/Solutions/FOLDER` and compile it
  alone (`lake env lean FILE`, seconds), or the whole closure with in-place edits (`lake build ROOT` keeps going
  past failures and caches, so a round is minutes; oaiq-075; for oaiq-092's 2102 modules a round was 10-30 min
  in place against 1 h through the pipeline's `build`). Three habits that save rounds: after the first failure of
  a kind, `rg` the whole port for the same pattern and patch every site before rebuilding (oaiq-089: five
  2.5 h rounds); batch compat changes before the first full build, since a compat change rebuilds everything
  (oaiq-091); and let the pipeline's `build` build the modules, since an in-place build writes neither module
  times nor the LeanInfo cache: `graph` then elaborates every module itself (oaiq-092: about 6 h) and the plan
  is blind. `config` fills missing times from the LeanInfo cache and stops when under half the port is timed;
  then delete `.lake/build/{lib/lean,ir}/Solutions/FOLDER` and `--redo build` (a03f3b3). Then turn the diff into patches whose `count` is taken over the
  unpatched port, never the patched workspace (oaiq-063, -071, -072). A patch `why` lands in the piece's
  explanation: write Lean names in it in backticks (oaiq-064: a hypothesis `he` failed the pronoun check).

## Retrying an earlier attempt (worker lessons, 2026-10-30)

- **Read references for the symptom first.** A blocker an older batch recorded as "untried next steps" may have a
  documented remedy by now (oaiq-118: the CoeT WA fold had been documented for a day).
- **A carve from before `carve_pipeline.py`** (a `config.json` and no `pipeline.json`) cannot be resumed by the
  driver. Do not repair it: start a fresh pipeline carve under a new folder and bundle prefix, carrying over only
  its hand patches; expect some to count 0 now (the port rewrites them) and drop those (oaiq-115: ported,
  built, planned and measured clean in 55 minutes).
- **A carve from before 2026-10-29**: before the first `--detach`, check `pipeline.json` and its meta against the
  current brief: `defs` (bare `Def_X` normalised since 1e02cec), meta `prefixes` (the root's top directory, never
  the result's own folder), `overlap`; a driver killed mid-build shows `build: running` and no failure line, and
  resuming replays the built modules in seconds (oaiq-125). Resume with `--upgrade --keep-port` unless the port
  rules' changes are wanted; on an unpublished carve, `--from plan` picks up carver fixes (oaiq-122). Re-derive
  every old patch's `old` from the current ported text, not from the old notes (oaiq-117). One that never
  published needs no re-port: fix meta `prefixes` to `openai_prefixes(DIR/src/lean)`, add `"overlap": true` by
  editing `pipeline.json` (the CLI `--overlap` is refused as a changed parameter), then `--upgrade --keep-port
  --from plan --stop-after names --detach` and `--publish --detach` (q134: about 35 minutes, all 7 pieces
  accepted first try).
- **A new port patch on an old unpublished carve whose port rules have changed since** (q140): editing the
  patches file makes `filter_patches` stale, and the re-run port uses the *current* rules even under
  `--keep-port` (it only suppresses re-ports caused by rule changes), which would rewrite every module under the
  old hand repairs. Re-port on the carve's own snapshot, `python3 ~/.cache/p2m/skill/<old sha>/prove2me/scripts/
  carve_pipeline.py DIR --detach --stop-after wsbuild` (only the patched module's text changes), then `--upgrade
  --keep-port --publish --detach` from the current snapshot. (Not built: `--keep-port` re-running a stale port
  with the snapshot recorded for the port step.)
- **Hand repairs on a `--keep-port` carve start from a stale port** (q136): `--redo filter_patches` whose output is
  unchanged does not re-port, so the workspace still holds the port of the old rules while the log reads as if
  the new ones were in force, and `mkpatches.py` diffs against it. Before repairing by hand, `--redo port`. When
  filter_patches drops a patch as "the port now writes it", check whether that patch carried another repair in the
  same hunk, and re-add that as its own entry (q136 lost two that way, a build round each).
- **Leaves left Open by unsent pieces** (q129): before assuming a goal's open leaves are hard, check whether each
  has a pending or never-sent piece. oaiq-122 stopped at `calibrate_pieces` on three slow pieces and never sent
  the other 36 (10-112 s); sent by hand with `split_run.py` from a copy of the run config (`state` and `log`
  pointed into the job dir), 36 were accepted at once.
- **A carve published on an old skill with a few broken items**: finish its own `publish/` rather than
  re-planning frozen across many skill versions: newer graph rules infer needs the published bundles never had
  (oaiq-120: 40 plan problems). Compile each item against the *published* bundles (`fetch_theorems.py --names
  Definitions.Def_X …`), fix it, and resend with `split_run.py publish/run.json --go --reset statement:NAME`
  (old run states have no `sha`, so a changed stopped item is not resent without `--reset`).
- **A `SORRY` verdict on a carved piece whose local `#print axioms solution` is clean** usually means the server
  failed to elaborate it (an unknown identifier): compile the submitted source (`GET /submissions/:id/solution`)
  against the published bundles; do not just resubmit (oaiq-120).
- **A goal Open with no open leaves**: `GET /theorems/:id/open-leaves` does not list a Disproved child; walk
  `/decompositions` (oaiq-109: a sketch imported a Disproved statement and was still SKETCH_ACCEPTED).
  Every submission path refuses a Disproved import: `submit_solution.py` since 9397093 (and through it
  `submit_all.py` and `oai_submit.py`), and split_run's pieces for statements of others (59f4e2a).
- **Folding on a carve whose snapshot predates `carve.py fold`** (oaiq-118): `carve.py fold CONFIG N…` from a
  current snapshot; `carve.py gen CONFIG pieces <changed>` from the carve's own snapshot (a newer gen emits
  different `attribute [-instance]` lines); `carve_measure.py --kinds piece` from the current one (it runs the
  CoeT check); then `publish-prep --sync`, prose, check-text, and write the `comparisons/<slug>.md` notes *before*
  resuming, since they are what makes split_run resend the live importers (2442579; oaiq-124).
- **An `elab` that builds tactic syntax** (oaiq-119, `pts_pl`, 54 sites): expand it at its call sites by running a
  logging variant in place (build the replacement text, parse and run it, log it), then `mkpatches.py`; traps:
  restore the message log before logging a failure, count error messages around `evalTactic`, `try a; b` is
  `try (a; b)`, no `pp.oneline`, keep explicit atoms. Budget an hour or two: not a blocker.
- **Compat instances are global** (oaiq-122): one added for Kadison similarity made `whnf` time out in three
  FactorGeneration modules. A compat instance carrying data is a `@[reducible] def` made local by a port rule keyed
  on what the module names (2165390); a carve whose port built before a compat instance was added can hide it with
  pipeline.json `hide_instances` (0eea563). A module that built before and now times out at `whnf` after an
  upgrade: bisect the compat instances first (`attribute [-instance]` in a copy, ~20 s each). A heartbeat failure
  in the pipeline's build is not evidence until plain `lean -DautoImplicit=false` reproduces it: LeanInfo
  elaborates synchronously and spends more (3230451 retries such modules with plain `lean -o`). Bundles and pieces
  are the opposite case: the verifier elaborates synchronously too (verifier-failures.md, q128).
- **Post-carve patches naming a collision suffix** (`_r<hex>_<n>`) break silently across snapshots: prefer a
  carver fix (oaiq-123). After a re-plan, re-read every post-carve patch that names an `<x>_oai`: it is right
  only while `x` is still a piece target (oaiq-122: one still matched and broke a piece, the other matched nothing
  and its heartbeat timeout came back). A plan from before 20365e5 recomputes frozen bundles' imports: after
  `--upgrade`, `--redo plan` (plain `--upgrade` keeps the old plan). A heartbeat raise by split_run updates the
  frozen `published/lib` copy too since 4b230e3. Editing the post-carve patches file re-runs `gen` since dad2e72 (older: `--redo gen`).

## Which local instances and lemmas a carved file brings back (carver rules, 2026-10-27/28)

A carved file loses the context its module had, so the carver restores what its declarations used.
Lean's records (LeanInfo `insts`, `inst_keys`, `declares`) name most uses, but some leave no trace, so
these rules over-approximate on purpose; each comes from a worker carve that failed without it:
- (2ae7988, 2026-10-30) a global `@[simp]` declaration of this carve that a module never saw is hidden at the
  top of that module's section with `attribute [-simp]` (section-local) when a kept declaration there calls the
  default simp set and the lemma could apply; never a library lemma (oaiq-081: `status_read` closed goals
  early, about 40 hand patches). A local coercion instance between library types (`local instance : Coe (E → ℝ)
  (E → ℂ)`) comes back for every kept declaration in its scope, since its use leaves no constant (oaiq-096
  `Wiener`). A `@[local X]` attribute (`gcongr`, `simp`, …) on a declaration the file imports from a bundle is
  applied again, `attribute [local X] _root_.N`, before the kept commands that use it (oaiq-096). In a notation
  body, a token that starts with a section variable is that variable: LeanInfo reads notation bodies without
  the section's variables, which once dropped a statement's `local notation "work"` and turned `run.output`
  into `run.run_oai` (oaiq-081). An `export` that still exports something keeps its namespace block (oaiq-081
  `PA.denote`).
- (0871d92, q135) a dotted declaration `Poly.finite` is elaborated with `Poly` open, so a short name in it
  (even a `match` pattern head, `| some s =>`) can mean a `Poly.some` the bundle holds though the module never
  imported it; the carver pins such names, including library names reached by `export`. (0b402cf) an
  *imported* `@[simp] … := rfl` lemma counts for a default simp call when it mentions a project definition the
  caller mentions. To diagnose "unsolved goals" after `simp` in a bundle, run `simp?` at that line in the original
  module and look for each lemma it names in the bundles; for "Invalid pattern" or a type mismatch on a short
  name, `#check` it at that point of a truncated copy of the bundle.
- a local instance used by a kept command comes back, reactivated (`attribute [local instance P] N`,
  with its source priority) when an imported bundle declares it, else emitted again under a file-unique
  name after the earlier local instances its own elaboration used (oaiq-032, oaiq-031);
- with it come its siblings: other classes on the same carrier type (a `Module` and its `IsScalarTower`
  partner, oaiq-031) and the same class (three `DecidableEq` instances, oaiq-060), in source order so the
  instance that won in the port still wins; a sibling that a later kept instance of its class would lose
  to stays out;
- a local instance whose type mentions a project declaration the kept command uses comes back even with
  no recorded use (a `CoeFun` used as `w 3`, `Primcodable`, oaiq-066/043);
- a global instance the module never saw is hidden (`attribute [-instance]`) also when the declaration
  solved a problem of its class whose heads include the instance's; a project `abbrev` head matches
  anything, since instance search sees through it (oaiq-071);
- a call to the default simp set (`simp`, `simpa`, `simp_all`, `dsimp`, `norm_num`, `field_simp`, `aesop`
  without `only`) depends on the module's earlier `@[simp]` lemmas proved by `rfl` (only those: any other
  simp lemma leaves a constant in the term; oaiq-067);
- an attribute that declares constants (`reassoc`, `elementwise`, `simps`, `to_additive`, `mk_iff`,
  `ext`, ...) is applied only in the file that declares its target, when that target is the module's own
  (oaiq-065: a re-applied `reassoc` declared `_assoc` twice).
`carve_measure` deletes a module's old `.olean`/`.ilean` before compiling it, so a failed file never
leaves an earlier plan's module of the same name for later files to import (oaiq-065's "Unknown
constant" and "Unknown identifier" after a re-plan).
