# Recurring Lean 4 / Mathlib pitfalls

Tactic-level failures that cost real time on a paper formalization. Symptoms
first, so this is greppable when stuck.

## Casts and `linarith`

**Symptom:** `linarith` fails on a goal that is visibly linear.

`linarith` treats `↑(k + n % k)` and `(↑k + ↑(n % k))` as *different atoms*. It
will not close the goal even though the two are propositionally equal. Fix:
`push_cast at h1 h2 h3 ⊢` — and list **every** hypothesis you want used,
including the recursive-call hypothesis and the induction hypothesis. Missing
one leaves the mismatched atom in play and the failure looks identical.

## `omega` and nonlinear atoms

**Symptom:** `omega` fails on a goal about `/` and `%` that looks arithmetical.

`omega` handles `Nat` division/modulo by *constants*, but treats `(n / k + 1) * k`
and `n / k * k` as unrelated opaque atoms. Bridge them yourself first:

```lean
have hmul : (n / k + 1) * k = n / k * k + k := by ring
rw [hmul]
omega
```

Same trick for any product of two variable subterms. Supply `Nat.div_add_mod'`
explicitly when the goal needs `n / k * k + n % k = n` (note the order: the
primed form multiplies on the right; unprimed `Nat.div_add_mod` is `k * (n / k) + n % k = n`).

## `decide` cannot reduce well-founded recursion

**Symptom:** `decide` times out or reports the proposition is not decidable, on
a base case of a function defined with `termination_by`.

Definitions compiled by well-founded recursion do not reduce definitionally.
Prove the unfolding lemma once (`theorem remSum_of_pos …`) and use it:

```lean
rw [remSum_of_pos (by norm_num)]
norm_num [Nat.fib]
```

`#guard` on such a definition fails for the same reason — spot-check via the
unfolding lemma, or via `#eval`.

## Fibonacci index conventions

**Symptom:** an induction that works for large `j` fails at `j = 0`.

`Nat.fib 1 = Nat.fib 2 = 1`, so strict monotonicity is not universal:
`Nat.fib_lt_fib_succ` requires `2 ≤ n`. An index shift that is one too low makes
the base case false while every later case is fine. Either re-index the whole
statement (state it at `j + 3` / `j + 4` rather than `j + 1` / `j + 2`) or split
off `j = 0` explicitly. Related: `Nat.fib_mono` is non-strict, `Nat.fib_pos`
needs positivity, `Nat.fib_coprime_fib_succ` is the coprimality workhorse.

## Rewrites hitting unintended occurrences

**Symptom:** `rw [e1, e2]` succeeds but produces a mangled goal, or fails with
"motive is not type correct".

When the rewritten variable appears in several roles (an index and a bound, say),
`rw` takes them all. Restructure so the variable is destructured up front:

```lean
obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
```

then state the index equalities you need as separate `have`s and rewrite with
those. `conv` targeting also works but is more brittle to maintain.

## Signature drift in Mathlib

**Symptom:** "function expected" / argument-order errors on a lemma you are sure
exists, e.g. `div_le_div_of_nonneg_right`.

Ordering and implicitness of monotonicity lemmas churn between Mathlib versions.
Prefer `gcongr`, which discharges these congruence goals without naming a lemma
and survives upgrades. `positivity` plays the same role for side conditions.

## `field_simp` closing the goal

**Symptom:** `error: no goals` on a trailing `ring`.

`field_simp` frequently finishes the goal on its own. The idiomatic
`field_simp; ring` then errors. Drop the trailing tactic — or, if you want the
proof robust either way, use `field_simp <;> ring_nf`.

## Rewrites that need an explicit intermediate

**Symptom:** `rw [sq_abs]` reports the pattern was not found, though `|θ|^2` is
plainly there.

The term is often `(2 * |θ|)^2`, not `|θ|^2`. State the step you mean:

```lean
have hsq : (2 * |θ|) ^ 2 = 4 * θ ^ 2 := by rw [mul_pow, sq_abs]; norm_num
```

## Degenerate `Finset` ranges

`Finset.Ico_self` does not apply to `Finset.Ico 1 0`. For an empty range from a
numeric inequality use `Finset.Ico_eq_empty (by omega)`.

Similarly, `linarith` can stall on unnormalized zero terms like `0 * π / (2*|θ|)`;
clear them first with `rw [zero_mul, zero_div, add_zero]`.

## Case names of a custom induction principle

**Symptom:** `induction m using Int.induction_on with | hz => …` fails with
"Invalid alternative name `hz`: Expected `zero`, `succ`, or `pred`".

The alternatives are named by the eliminator Lean actually uses, not by the
hypothesis binders in the source declaration — `Int.induction_on`'s binders are
`hz`/`hp`/`hn`, and reading them off the source is how you get this wrong. Let the
error enumerate them, or write `induction m using Int.induction_on` with no `with`
and read the resulting goals.

## `to_additive`-generated names are invisible to grep

**Symptom:** `grep -rn "def addRight" Mathlib/` finds nothing, so you conclude
`OrderIso.addRight` does not exist and hand-build the order isomorphism `y ↦ y + 1`.

It does exist — generated from `OrderIso.mulRight` by `@[to_additive]`, so no
additive declaration appears in the source at all. Search the multiplicative
spelling, or just try the name in a scratch file. This nearly cost a needless
`StrictMono.orderIsoOfSurjective` construction for a map Mathlib already had.

## `ℝ ≃o ℝ` as a group

The `RelIso` group instance is `mul f₁ f₂ := f₂.trans f₁`, so **`(f * g) x = f (g x)`**
— right to left, the opposite of sources that compose maps left to right. `f⁻¹` is
`f.symm`, and `RelIso.apply_inv_self f x : f (f⁻¹ x) = x` plus `f.injective` is how you
evaluate an inverse: prove `f candidate = y`, then conclude `f⁻¹ y = candidate`.

## `linear_combination` when `field_simp` stalls

**Symptom:** `field_simp` reports "made no progress", or leaves a goal `ring` cannot
close, on an affine identity true only modulo one cancellation such as `a * a⁻¹ = 1`
or `2 ^ n * 2 ^ (-n) = 1`.

Prove the cancellation as its own `have`, then close with
`linear_combination <coefficient> * that`. The coefficient is what the goal's
difference factors by: for `a * (a⁻¹ * (y - p) + p - p) + p = y` with
`haa : a * a⁻¹ = 1`, the difference is `(a * a⁻¹ - 1) * (y - p)`, so
`linear_combination (y - p) * haa`. More robust than pushing `field_simp` around, and
it documents which cancellation the step depends on.

## "Abelian" as a property, not a bundled structure

**Symptom:** you want "this subgroup is abelian" as a hypothesis and cannot find a name;
`Subgroup.IsCommutative` does not exist (it did in older Mathlib).

It is `IsMulCommutative` (`Mathlib/Algebra/Group/Defs.lean`), an unbundled `Prop` class on a
type, with `isMulCommutative_iff : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a`.
`HierarchyDesign.lean` recommends it over bundling `CommGroup` for exactly the
`S : Subgroup G` case — as guidance only; see the next entry. It applies to a subgroup through the coercion, so `IsMulCommutative H`
elaborates — but it is then a statement about the **subtype** `↥H`, not about elements of `G`
with membership proofs. The hand-written `∀ a ∈ H, ∀ b ∈ H, a * b = b * a` is therefore a
*different* proposition, equivalent via `Subtype.ext` in one direction and
`congrArg Subtype.val` in the other. Choose deliberately, and note that the choice is about *terms*, not
about being a class. `[Group G]` and `[IsFreeGroup G]` are instance-implicit too, and cost a
caller nothing, because they are properties of a **type** that inference already has in scope;
a conclusion like `IsCyclic H` costs nothing either, since nobody has to supply it. But an
instance argument about a **term** is found only through registered propagation instances — for
subgroups at this rev, `Prod`, `Pi` and directed `iSup`, not `closure` — so a contingent fact
you derived mid-proof has to be installed with `haveI`, and instance search matches the term up
to reducible unfolding, so it can miss a definitionally-equal but differently-spelled one. An
explicit hypothesis is a proof you pass, with no matching step.

## Code in a Mathlib doc file may be illustration, not declaration

**Symptom:** grep finds `instance Subgroup.instIsMulCommutative_closure` and you cite it, or
try to use it; it does not exist.

`Mathlib/Algebra/HierarchyDesign.lean` and files like it are prose. Their declarations sit
inside fenced code blocks in doc comments, showing a recommended *shape*. Real instances of
that same shape existed elsewhere (subrings, subalgebras) which made the hit look corroborated.
Before citing any grep hit, check whether the surrounding lines are code or commentary — or
elaborate the name in a scratch file, which settles it in one compile.

## Metavariables in `refine` make `linarith` fail on the wrong goal

**Symptom:** `refine foo _ bar ⟨by linarith, by linarith⟩` reports "linarith failed" with a
context that looks sufficient, or "don't know how to synthesize implicit argument".

The `_` is still a metavariable when the anonymous constructor's subgoals are elaborated, so the
tactics run against goals mentioning `?m`. Pin the argument explicitly —
`isCompact_Icc (a := lo) (b := hi)`, `mem_closure_iff.mp h (Set.Ioo a b) isOpen_Ioo` — rather
than adjusting the tactic. Hit twice in one session, both times looking like a `linarith`
weakness.

## `by rw [...]` as a proof of an equation with metavariables proves nothing

**Symptom:** a lemma application type-checks but the result is vacuous, e.g. `haa : a = a` where
`a = a'` was intended.

Passing `(by rw [← h1, h2])` for an argument whose type has metavariables lets the elaborator
choose the metavariables to make the goal trivially true. Supply an explicit term instead —
`h1.symm.trans h2` — so the unifier has no freedom.

## The `group` tactic for commutator algebra

`group` proves identities in free groups, which covers most commutator rearrangement:
`f * g = (f * g * f⁻¹ * g⁻¹) * (g * f)` closes with `by group`, and integer exponents are
handled. It cannot use hypotheses, so the idiom is `calc` through a `group`-provable identity and
then `rw` the hypothesis.

## Apply an "infinite order" lemma at the shifted point

**Symptom:** from `f ^ m (f ^ q x) = f ^ q x` you want `m = 0`, but the lemma is about `x`.

Do not try to cancel `f ^ q`. The hypothesis is literally that `f ^ m` fixes the point
`y = f ^ q x`, so apply the lemma at `y` — and `y` is still moved by `f`, because a support is
invariant under powers. Choosing the right base point avoids a rearrangement entirely.

## Recent renames seen in one session

`div_lt_iff` → `div_lt_iff₀`; `le_or_lt` gone (use `by_cases`, or `le_total`); `Set.image_subset`
→ `Set.image_mono`; `Set.diff_subset` → `Set.sdiff_subset`; `push_neg` deprecated in favour of
`push Not`; `Subgroup.IsCommutative` → `IsMulCommutative`. Name-guessing is the single largest
time sink; prefer restructuring to avoid a named lemma (`field_simp` into a hypothesis then
`nlinarith`) over hunting for the new spelling.

## `connectedComponentIn_eq` direction

`connectedComponentIn_eq (h : y ∈ connectedComponentIn F x) : connectedComponentIn F x =
connectedComponentIn F y` — the *hypothesis* point is on the left. Getting it backwards gives an
"argument has type `z ∈ …` but is expected to have type `y ∈ …`" mismatch that reads like a
different bug.

## Declaration order

**Symptom:** `unknown identifier` for something defined in the same file.

Lean files are processed top to bottom with no forward references. When adding a
theorem about an existing definition, append it *after* that definition — a new
section inserted textually earlier will not see it.

## Guessed lemma names

**Symptom:** `unknown identifier` for a lemma you are confident exists.

Mathlib's naming is close enough to guessable to be a trap: `cos_lt_one_of_ne_zero`,
`pow_le_pow_right_of_le_one`, `measurable_iSup`, `Metric.eventually_nhdsWithin_iff`
all sound right and none exist under that name. A `grep -rn "theorem cos_lt"` over
`.lake/packages/mathlib/Mathlib/` costs seconds; a guessed name costs a build
cycle each time. Grep for the *statement shape* (`"arccos_le_arccos"`,
`"_lt_cos_of"`), not the name you expect.

## Measure theory: `lintegral` and `ℝ≥0∞`

**Symptom:** the integrand is not what you wrote.

`∫⁻ x in s, f x + g x` parses the whole sum as the integrand. Parenthesise every
summand in `calc` steps and `have` statements: `(∫⁻ x in s, f x) + ∫⁻ x in s, g x`.

**Symptom:** `zero_le` fails; `norm_num` will not close `2⁻¹ + 2⁻¹ = 1`.

In `ℝ≥0∞` use `bot_le` for `0 ≤ a`, and the named lemmas for arithmetic
(`ENNReal.inv_two_add_inv_two`, `ENNReal.add_le_add_iff_left/right` with a
finiteness side condition). Subtraction is truncated, so never state a step as
`a - b ≤ c`; state `a ≤ c + b` and cancel with `add_le_add_iff_*`, which needs
the cancelled term to be `≠ ∞`. `lintegral_const_mul'` wants the constant
`≠ ∞`; `lintegral_const_mul` wants measurability instead — pick by which side
condition you can discharge.

**Symptom:** `Set.indicator_of_mem h` does not typecheck though `h` proves
membership.

It needs membership in the *named* set: `Set.indicator_of_mem (show x ∈ S from h)`.
For rewriting under an indicator, `simp only [Set.indicator_apply]` and then
splitting on the condition is more robust than `rw`.

**Symptom:** `rw` fails with a higher-order unification error under `∫⁻`, or
elaboration times out in a large file.

Do not rewrite under the binder. State the equation as a `have` about the whole
integral and close it with `lintegral_congr` (pointwise) or by `rfl`. A
`rw [show (fun t => …) = … from funext h]` can blow the heartbeat limit on a big
file where `lintegral_congr h` is instant. Likewise prefer `by fun_prop` (after
`unfold`ing your own definitions) to hand-built `Measurable.comp` chains, which
are a common source of `whnf` timeouts.

**Useful idioms.** Density points: `Besicovitch.ae_tendsto_measure_inter_div`
together with `(ae_restrict_iff' hs).mp` to turn `∀ᵐ x ∂μ.restrict s` into
`∀ᵐ x, x ∈ s → …`. Slice measures: `measurable_measure_prodMk_left` makes
`fun x => volume (U ∩ ball x r)` measurable. Swapping the two points of a pair
integral: `lintegral_prod_swap`, applied to the indicator of the region.

## Named arguments when the metavariable is undetermined

**Symptom:** an `exact` on a lemma with two implicit endpoints fails with
`-1 ≤ ?m`.

Lemmas like `Real.arccos_lt_arccos (hx : -1 ≤ x) (hlt : x < y) (hy : y ≤ 1)`
elaborate their side conditions before `x` and `y` are known. Supply them:
`Real.arccos_lt_arccos (x := √2/2) (y := √(14/15)) …`.

## Deprecation churn

Names move between Mathlib releases and the linter only warns after the fact.
Seen in one project: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `measure_diff` →
`measure_sdiff`, `Set.diff_eq` → `Set.sdiff_eq`, `measure_inter_add_diff` →
`measure_inter_add_sdiff`, `lintegral_finset_sum` → `lintegral_finsetSum`,
`push_neg` → `push Not`, `Set.diff_subset_diff_left` →
`Set.sdiff_subset_sdiff_left`; `le_or_lt` gone entirely (use `by_cases` or
`rcases le_total`). Build with warnings visible and fix them as they appear —
they are cheap then and a large diff later.

