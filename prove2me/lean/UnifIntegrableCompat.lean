import Mathlib

/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

/-- Uniform integrability in the measure theory sense, with the measurability of each member
(`d13f23b`'s `UnifIntegrable`, whose `eLpNorm` bounds carry it). -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  MeasureTheory.UnifIntegrable f p μ ∧ ∀ i, AEStronglyMeasurable (f i) μ

/-- Uniform integrability in the probability sense, in `d13f23b`'s two-component shape. -/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  UnifIntegrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) p μ ≤ C

/-- Uniform tightness with an extended-real `ε` (`d13f23b`'s `UnifTight`). -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ε > 0, ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε

theorem unifIntegrable_iff_mathlib :
    UnifIntegrable f p μ ↔ MeasureTheory.UnifIntegrable f p μ ∧ ∀ i, AEStronglyMeasurable (f i) μ :=
  Iff.rfl

theorem uniformIntegrable_iff_mathlib :
    UniformIntegrable f p μ ↔ MeasureTheory.UniformIntegrable f p μ :=
  ⟨fun ⟨⟨u, hm⟩, b⟩ => ⟨hm, u, b⟩, fun ⟨hm, u, b⟩ => ⟨⟨u, hm⟩, b⟩⟩

theorem unifTight_iff_mathlib : UnifTight f p μ ↔ MeasureTheory.UnifTight f p μ :=
  (MeasureTheory.unifTight_iff_ennreal f p μ).symm

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff`. -/
theorem enn_spec (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ _ => le_top⟩
  obtain ⟨δ, hδ, h⟩ := hf.1 (ENNReal.toReal_pos hε.ne' hεt.ne)
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun i s hs => ?_⟩
  have ht := measurableSet_toMeasurable μ s
  calc eLpNorm (f i) p (μ.restrict s)
      ≤ eLpNorm (f i) p (μ.restrict (toMeasurable μ s)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (subset_toMeasurable μ s) le_rfl)
    _ = eLpNorm ((toMeasurable μ s).indicator (f i)) p μ :=
        (eLpNorm_indicator_eq_eLpNorm_restrict ht).symm
    _ ≤ ENNReal.ofReal ε.toReal := h i _ ht (by rwa [measure_toMeasurable])
    _ = ε := ENNReal.ofReal_toReal hεt.ne

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff'`. -/
theorem enn_spec' (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε :=
  fun ε hε => (hf.enn_spec ε hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s _ => h i s⟩

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff'`, with the measurability. -/
theorem of_enn' (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) (hm : ∀ i, AEStronglyMeasurable (f i) μ) :
    UnifIntegrable f p μ := by
  refine ⟨fun ε hε => ?_, hm⟩
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne, fun i s hsm hs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s hsm (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff`, with the measurability. -/
theorem of_enn (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) : UnifIntegrable f p μ :=
  of_enn' (fun ε hε => (h ε hε).imp fun _ ⟨hδ, hb⟩ => ⟨hδ, fun i s _ => hb i s⟩) hm

protected theorem aestronglyMeasurable (hf : UnifIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.2 i

protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) :
    UnifIntegrable (f + g) p μ :=
  ⟨hf.1.add hg.1 hp hf.2 hg.2, fun i => (hf.2 i).add (hg.2 i)⟩

protected theorem neg (hf : UnifIntegrable f p μ) : UnifIntegrable (-f) p μ :=
  ⟨hf.1.neg, fun i => (hf.2 i).neg⟩

protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) :
    UnifIntegrable (f - g) p μ :=
  ⟨hf.1.sub hg.1 hp hf.2 hg.2, fun i => (hf.2 i).sub (hg.2 i)⟩

protected theorem ae_mono (hg : UnifIntegrable g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifIntegrable f p μ :=
  of_enn (fun ε hε => (hg.enn_spec ε hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s hs =>
    (eLpNorm_mono_enorm_ae ((hfg i).filter_mono ae_restrict_le)).trans (h i s hs)⟩) hf_meas

protected theorem ae_eq (hf : UnifIntegrable f p μ) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable g p μ :=
  ⟨hf.1.ae_eq hfg, fun i => (hf.2 i).congr (hfg i)⟩

/-- Uniform integrability is preserved by restriction of the functions to a set. -/
protected theorem indicator (hf : UnifIntegrable f p μ) (s : Set α) (hs : MeasurableSet s) :
    UnifIntegrable (fun i ↦ s.indicator (f i)) p μ :=
  ⟨hf.1.indicator s, fun i => (hf.2 i).indicator hs⟩

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
protected theorem restrict (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable f p (μ.restrict s) :=
  ⟨hf.1.restrict s, fun i => (hf.2 i).restrict⟩

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ :=
  ⟨fun _ hε => (hf.1 hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s => h (g i) s⟩, fun i => hf.2 (g i)⟩

lemma unifIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ := by
  refine ⟨hUI.1.unifIntegrable_of_tendstoInMeasure u hfn, fun ⟨f, s, hs⟩ => ?_⟩
  exact hs.aestronglyMeasurable fun n => hfn (s n)

lemma unifIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UnifIntegrable fn p μ)
    (hfn : ∀ i, AEStronglyMeasurable (fn i) μ) :
    UnifIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ := by
  refine ⟨hUI.1.unifIntegrable_of_ae_tendsto u hfn, fun ⟨f, s, hs⟩ => ?_⟩
  exact aestronglyMeasurable_of_tendsto_ae u (fun n => hfn (s n)) hs

end UnifIntegrable

theorem unifIntegrable_congr_ae (hfg : ∀ i, f i =ᵐ[μ] g i) :
    UnifIntegrable f p μ ↔ UnifIntegrable g p μ :=
  ⟨fun hf => hf.ae_eq hfg, fun hg => hg.ae_eq fun n => (hfg n).symm⟩

theorem unifIntegrable_of_isEmpty [IsEmpty ι] : UnifIntegrable f p μ :=
  ⟨fun _ _ => ⟨1, one_pos, fun i => isEmptyElim i⟩, fun i => isEmptyElim i⟩

theorem unifIntegrable_zero_meas [MeasurableSpace α] : UnifIntegrable f p (0 : Measure α) :=
  ⟨MeasureTheory.unifIntegrable_zero_meas, fun _ => aestronglyMeasurable_zero_measure _⟩

theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ :=
  ⟨MeasureTheory.unifIntegrable_const hp hp_ne_top hg, fun _ => hg.1⟩

theorem unifIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_subsingleton hp_one hp_top hf, fun i => (hf i).1⟩

theorem unifIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_finite hp_one hp_top hf, fun i => (hf i).1⟩

theorem unifIntegrable_of_tendsto_Lp_zero {f : ℕ → α → β} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_of_tendsto_Lp_zero hp hp' hf hf_tendsto, fun n => (hf n).1⟩

theorem unifIntegrable_of_tendsto_Lp {f : ℕ → α → β} {g : α → β} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_of_tendsto_Lp hp hp' hf hg hfg, fun n => (hf n).1⟩

theorem unifIntegrable_of' (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_of' hp hp' hf fun _ hε => h _ (ENNReal.ofReal_pos.2 hε),
    fun i => (hf i).aestronglyMeasurable⟩

theorem unifIntegrable_of (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UnifIntegrable f p μ :=
  ⟨MeasureTheory.unifIntegrable_of hp hp' hf fun _ hε => h _ (ENNReal.ofReal_pos.2 hε), hf⟩

theorem tendsto_Lp_finite_of_tendsto_ae_of_meas [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' hf hg hg' hui.1 hfg

theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendsto_ae hp hp' hf hg hui.1 hfg

theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure hp hp' hf hg hui.1 hfg

/-- **Vitali's convergence theorem** in `d13f23b`'s form. -/
theorem tendstoInMeasure_iff_tendsto_Lp_finite [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [← MeasureTheory.tendstoInMeasure_iff_tendsto_Lp_finite hp hp' hf hg]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun n => (hf n).1⟩⟩

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

protected theorem unifIntegrable (hf : UniformIntegrable f p μ) : UnifIntegrable f p μ :=
  hf.1

protected theorem aestronglyMeasurable (hf : UniformIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.1.2 i

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) : MemLp (f i) p μ :=
  (uniformIntegrable_iff_mathlib.1 hf).memLp i

theorem toMathlib (hf : UniformIntegrable f p μ) : MeasureTheory.UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.1 hf

theorem ae_eq (hf : UniformIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable g p μ :=
  uniformIntegrable_iff_mathlib.2 (hf.toMathlib.ae_eq hfg)

theorem spec' (hp : p ≠ 0) (hp' : p ≠ ∞) (hf : ∀ i, StronglyMeasurable (f i))
    (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨0, fun _ => le_top⟩
  obtain ⟨C, hC⟩ := hfu.toMathlib.spec' hp hp' hf (ENNReal.toReal_pos hε.ne' hεt.ne)
  exact ⟨C, fun i => (hC i).trans (ENNReal.ofReal_toReal hεt.ne).le⟩

theorem spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨0, fun _ => le_top⟩
  obtain ⟨C, hC⟩ := hfu.toMathlib.spec hp hp' (ENNReal.toReal_pos hε.ne' hεt.ne)
  exact ⟨C, fun i => (hC i).trans (ENNReal.ofReal_toReal hεt.ne).le⟩

lemma uniformIntegrable_of_tendstoInMeasure {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      TendstoInMeasure μ (fn ∘ ni) u g}) ↦ f.1) p μ :=
  uniformIntegrable_iff_mathlib.2 (hUI.toMathlib.uniformIntegrable_of_tendstoInMeasure u)

lemma memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) : MemLp g p μ :=
  hUI.toMathlib.memLp_of_tendstoInMeasure htends

lemma integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) : Integrable g μ :=
  hUI.toMathlib.integrable_of_tendstoInMeasure htends

lemma uniformIntegrable_of_ae_tendsto {κ : Type*} (u : Filter κ) [NeBot u]
    [IsCountablyGenerated u] {fn : ι → α → β} (hUI : UniformIntegrable fn p μ) :
    UniformIntegrable (fun (f : {g : α → β | ∃ ni : κ → ι,
      ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ fn (ni n) x) u (𝓝 (g x))}) ↦ f.1) p μ :=
  uniformIntegrable_iff_mathlib.2 (hUI.toMathlib.uniformIntegrable_of_ae_tendsto u)

lemma memLp_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f p μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) : MemLp g p μ :=
  hUI.toMathlib.memLp_of_ae_tendsto htends

lemma integrable_of_ae_tendsto {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β} (hUI : UniformIntegrable f 1 μ)
    (htends : ∀ᵐ (x : α) ∂μ, Tendsto (fun n ↦ f n x) u (𝓝 (g x))) : Integrable g μ :=
  hUI.toMathlib.integrable_of_ae_tendsto htends

end UniformIntegrable

theorem uniformIntegrable_zero_meas [MeasurableSpace α] : UniformIntegrable f p (0 : Measure α) :=
  uniformIntegrable_iff_mathlib.2 MeasureTheory.uniformIntegrable_zero_meas

theorem uniformIntegrable_congr_ae (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable f p μ ↔ UniformIntegrable g p μ :=
  ⟨fun h => h.ae_eq hfg, fun h => h.ae_eq fun i => (hfg i).symm⟩

theorem uniformIntegrable_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_finite hp_one hp_top hf)

theorem uniformIntegrable_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrable f p μ :=
  uniformIntegrable_finite hp_one hp_top hf

theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_const hp hp_ne_top hg)

theorem uniformIntegrable_of' [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, StronglyMeasurable (f i))
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.2
    (MeasureTheory.uniformIntegrable_of' hp hp' hf fun _ hε => h _ (ENNReal.ofReal_pos.2 hε))

theorem uniformIntegrable_of [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε) :
    UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.2
    (MeasureTheory.uniformIntegrable_of hp hp' hf fun _ hε => h _ (ENNReal.ofReal_pos.2 hε))

theorem uniformIntegrable_iff [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    UniformIntegrable f p μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧
        ∀ ε > 0, ∃ C : ℝ≥0,
          ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε :=
  ⟨fun h => ⟨h.aestronglyMeasurable, fun _ => h.spec (lt_of_lt_of_le zero_lt_one hp).ne' hp'⟩,
    fun h => uniformIntegrable_of hp hp' h.1 h.2⟩

theorem uniformIntegrable_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hp : 1 ≤ p) {f : ℕ → α → E} (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun (n : ℕ) => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, f i)) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_average hp hf.toMathlib)

theorem uniformIntegrable_average_real (hp : 1 ≤ p) {f : ℕ → α → ℝ}
    (hf : UniformIntegrable f p μ) :
    UniformIntegrable (fun n => (∑ i ∈ Finset.range n, f i) / (n : α → ℝ)) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_average_real hp hf.toMathlib)

/-! ### `UnifTight` -/

namespace UnifTight

theorem toMathlib (hf : UnifTight f p μ) : MeasureTheory.UnifTight f p μ :=
  unifTight_iff_mathlib.1 hf

theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ s in μ.cofinite.smallSets,
      MeasurableSet s → ∀ i, eLpNorm (s.indicator (f i)) p μ ≤ ε :=
  (hf.toMathlib.eventually_cofinite_indicator hε).mono fun _ h _ => h

protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  hf.toMathlib.exists_measurableSet_indicator hε

/-- `d13f23b`'s `UnifTight.add`, with the measurability `0df444a` needs. -/
protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ :=
  unifTight_iff_mathlib.2 (hf.toMathlib.add hg.toMathlib hf_meas hg_meas)

protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ :=
  unifTight_iff_mathlib.2 hf.toMathlib.neg

/-- `d13f23b`'s `UnifTight.sub`, with the measurability `0df444a` needs. -/
protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ :=
  unifTight_iff_mathlib.2 (hf.toMathlib.sub hg.toMathlib hf_meas hg_meas)

protected theorem aeeq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) : UnifTight g p μ :=
  unifTight_iff_mathlib.2 (hf.toMathlib.aeeq hfg)

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifTight f p μ) :
    UnifTight (f ∘ g) p μ :=
  fun ε hε => (hf ε hε).imp fun _ ⟨hμ, h⟩ => ⟨hμ, fun i => h (g i)⟩

end UnifTight

theorem unifTight_congr_ae (hfg : ∀ n, f n =ᵐ[μ] g n) : UnifTight f p μ ↔ UnifTight g p μ :=
  ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

theorem unifTight_const {g : α → β} (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifTight (fun _ : ι => g) p μ :=
  unifTight_iff_mathlib.2 (MeasureTheory.unifTight_const hp_ne_top hg)

theorem unifTight_of_subsingleton [Subsingleton ι] (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ :=
  unifTight_iff_mathlib.2 (MeasureTheory.unifTight_of_subsingleton hp_top hf)

theorem unifTight_finite [Finite ι] (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, MemLp (f i) p μ) : UnifTight f p μ :=
  unifTight_iff_mathlib.2 (MeasureTheory.unifTight_finite hp_top hf)

theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_of_tendsto_ae hp hp' haef hg' hui.1 hut.toMathlib hfg

theorem tendsto_Lp_of_tendstoInMeasure (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_of_tendstoInMeasure hp hp' hf hg hui.1 hut.toMathlib hfg

/-- **Vitali's convergence theorem** for infinite measures, in `d13f23b`'s form. -/
theorem tendstoInMeasure_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ ↔
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [← MeasureTheory.tendstoInMeasure_iff_tendsto_Lp hp hp' hf hg]
  exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.2.toMathlib⟩,
    fun h => ⟨h.1, ⟨h.2.1, fun n => (hf n).1⟩, unifTight_iff_mathlib.2 h.2.2⟩⟩

end OAI

end UnifIntegrableCompat
