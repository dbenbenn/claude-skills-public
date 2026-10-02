import Solutions.LM56.Blueprint

/-!
# Lemma 5.6 under positive commutation — part S2: words act, steps preserve the action

`act_append`, `act_posStep`, `genP_x_of_xFin`, `genP_x_inv_of_xFinInv`, `genP_y_zpow_of_not_mem`,
`genP_y_zpow_mem_iff`, `psi_D_00`, `psi_D_01`, `psi_D_1`, from the part-S1 lemmas of the Blueprint
(recursion equations, inverse laws, `localize` lemmas).
-/

open LodhaMoore LM56

namespace LM56.PartS2

/-! ## Helpers: generators applied to sequences -/

theorem genP_y_apply (s : Seq) (ξ : Str) : genP (.y s) ξ = localize s (yFun true) ξ := rfl
theorem genP_y_inv_apply (s : Seq) (ξ : Str) :
    (genP (.y s))⁻¹ ξ = localize s (yFun false) ξ := rfl
theorem genP_x_apply (s : Seq) (ξ : Str) : genP (.x s) ξ = localize s xFun ξ := rfl
theorem genP_x_inv_apply (s : Seq) (ξ : Str) : (genP (.x s))⁻¹ ξ = localize s xInvFun ξ := rfl

/-- Two sequences with a common infinite extension are compatible. -/
theorem compat_of_append_eq : ∀ {u v : Seq} {η ζ : Str}, u ++ₛ η = v ++ₛ ζ → u <+: v ∨ v <+: u
  | [], _, _, _, _ => Or.inl List.nil_prefix
  | _ :: _, [], _, _, _ => Or.inr List.nil_prefix
  | a :: u, b :: v, η, ζ, h => by
    rw [Stream'.cons_append_stream, Stream'.cons_append_stream] at h
    obtain ⟨rfl, h'⟩ := Stream'.cons_injective2 h
    rcases compat_of_append_eq h' with h | h
    · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h⟩)

theorem not_mem_cone_of_incompat {u v : Seq} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (η : Str) :
    u ++ₛ η ∉ cone v := by
  rintro ⟨ζ, hζ⟩
  rcases compat_of_append_eq hζ with h | h
  · exact h2 h
  · exact h1 h

theorem not_mem_cone_append {u v : Seq} (s : Seq) (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (η : Str) :
    s ++ₛ (u ++ₛ η) ∉ cone (s ++ v) := by
  rw [← Stream'.append_append_stream]
  exact not_mem_cone_of_incompat (by rwa [List.prefix_append_right_inj])
    (by rwa [List.prefix_append_right_inj]) η

theorem not_mem_cone_of_incompatible {u v : Seq} (h : Incompatible u v) {ξ : Str}
    (hu : ξ ∈ cone u) : ξ ∉ cone v := by
  obtain ⟨η, rfl⟩ := hu
  exact not_mem_cone_of_incompat h.1 h.2 η

theorem mem_cone_of_mem_cone_append {s v : Seq} {ξ : Str} (h : ξ ∈ cone (s ++ v)) :
    ξ ∈ cone s := by
  obtain ⟨ζ, rfl⟩ := h
  exact ⟨v ++ₛ ζ, (Stream'.append_append_stream s v ζ).symm⟩

theorem not_mem_cone_append_of_not_mem {s v : Seq} {ξ : Str} (h : ξ ∉ cone s) :
    ξ ∉ cone (s ++ v) := fun h' => h (mem_cone_of_mem_cone_append h')

theorem y_app (s : Seq) (η : Str) : genP (.y s) (s ++ₛ η) = s ++ₛ yFun true η :=
  localize_append s (yFun true) η
theorem yinv_app (s : Seq) (η : Str) : (genP (.y s))⁻¹ (s ++ₛ η) = s ++ₛ yFun false η :=
  localize_append s (yFun false) η
theorem x_app (s : Seq) (η : Str) : genP (.x s) (s ++ₛ η) = s ++ₛ xFun η :=
  localize_append s xFun η
theorem xinv_app (s : Seq) (η : Str) : (genP (.x s))⁻¹ (s ++ₛ η) = s ++ₛ xInvFun η :=
  localize_append s xInvFun η

theorem y_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : genP (.y s) ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem yinv_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : (genP (.y s))⁻¹ ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem x_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : genP (.x s) ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem xinv_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : (genP (.x s))⁻¹ ξ = ξ :=
  localize_of_not_mem s _ ξ h

theorem y_app' (s u : Seq) (η : Str) :
    genP (.y (s ++ u)) (s ++ₛ (u ++ₛ η)) = s ++ₛ (u ++ₛ yFun true η) := by
  rw [← Stream'.append_append_stream, y_app, Stream'.append_append_stream]
theorem yinv_app' (s u : Seq) (η : Str) :
    (genP (.y (s ++ u)))⁻¹ (s ++ₛ (u ++ₛ η)) = s ++ₛ (u ++ₛ yFun false η) := by
  rw [← Stream'.append_append_stream, yinv_app, Stream'.append_append_stream]

theorem xInvFun_0 (η : Str) : xInvFun ([false] ++ₛ η) = [false, false] ++ₛ η := by
  rw [← xFun_00, xInvFun_xFun]
theorem xInvFun_10 (η : Str) : xInvFun ([true, false] ++ₛ η) = [false, true] ++ₛ η := by
  rw [← xFun_01, xInvFun_xFun]
theorem xInvFun_11 (η : Str) : xInvFun ([true, true] ++ₛ η) = [true] ++ₛ η := by
  rw [← xFun_1, xInvFun_xFun]

/-- The cones `[00]`, `[01]`, `[1]` cover everything. -/
theorem tri_x (ζ : Str) : (∃ η, ζ = [false, false] ++ₛ η) ∨ (∃ η, ζ = [false, true] ++ₛ η) ∨
    ∃ η, ζ = [true] ++ₛ η := by
  have h2 : ζ = [ζ 0, ζ 1] ++ₛ ζ.drop 2 := by
    conv_lhs => rw [← Stream'.append_take_drop 2 ζ]
    rfl
  have h1 : ζ = [ζ 0] ++ₛ ζ.drop 1 := by
    conv_lhs => rw [← Stream'.append_take_drop 1 ζ]
    rfl
  generalize ζ 0 = a at h1 h2
  generalize ζ 1 = b at h2
  cases a
  · cases b
    · exact Or.inl ⟨_, h2⟩
    · exact Or.inr (Or.inl ⟨_, h2⟩)
  · exact Or.inr (Or.inr ⟨_, h1⟩)

/-- The cones `[0]`, `[10]`, `[11]` cover everything. -/
theorem tri_xinv (ζ : Str) : (∃ η, ζ = [false] ++ₛ η) ∨ (∃ η, ζ = [true, false] ++ₛ η) ∨
    ∃ η, ζ = [true, true] ++ₛ η := by
  have h2 : ζ = [ζ 0, ζ 1] ++ₛ ζ.drop 2 := by
    conv_lhs => rw [← Stream'.append_take_drop 2 ζ]
    rfl
  have h1 : ζ = [ζ 0] ++ₛ ζ.drop 1 := by
    conv_lhs => rw [← Stream'.append_take_drop 1 ζ]
    rfl
  generalize ζ 0 = a at h1 h2
  generalize ζ 1 = b at h2
  cases a
  · exact Or.inl ⟨_, h1⟩
  · cases b
    · exact Or.inr (Or.inl ⟨_, h2⟩)
    · exact Or.inr (Or.inr ⟨_, h2⟩)

/-! ## `act_append` -/

theorem act_append (u v : Word) : act (u ++ v) = act v * act u := by
  induction u with
  | nil => simp [act]
  | cons p u ih =>
    obtain ⟨g, n⟩ := p
    simp only [List.cons_append, act, ih, mul_assoc]

/-! ## The `x`-moves and the `y`-powers -/

/-- `x_s` moves `t` to `t' = t.x_s` by prefix replacement. -/
theorem genP_x_of_xFin {s t t' : Seq} (h : xFin s t = some t') (η : Str) :
    genP (.x s) (t ++ₛ η) = t' ++ₛ η := by
  unfold xFin at h
  split_ifs at h with h1 h2
  · obtain ⟨d, rfl⟩ := h1
    rw [List.drop_left] at h
    rcases d with _ | ⟨_ | _, d⟩
    · simp at h
    · rcases d with _ | ⟨_ | _, r⟩
      · simp at h
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show genP (.x s) (s ++ₛ ([false, false] ++ₛ (r ++ₛ η))) = s ++ₛ ([false] ++ₛ (r ++ₛ η))
        rw [x_app, xFun_00]
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show genP (.x s) (s ++ₛ ([false, true] ++ₛ (r ++ₛ η))) =
          s ++ₛ ([true, false] ++ₛ (r ++ₛ η))
        rw [x_app, xFun_01]
    · simp at h
      subst h
      rw [Stream'.append_append_stream, Stream'.append_append_stream]
      show genP (.x s) (s ++ₛ ([true] ++ₛ (d ++ₛ η))) = s ++ₛ ([true, true] ++ₛ (d ++ₛ η))
      rw [x_app, xFun_1]
  · simp at h
    subst h
    exact x_fix (not_mem_cone_of_incompat h2 h1 η)

/-- `x_s⁻¹` moves `t` to `t' = t.x_s⁻¹` by prefix replacement. -/
theorem genP_x_inv_of_xFinInv {s t t' : Seq} (h : xFinInv s t = some t') (η : Str) :
    (genP (.x s))⁻¹ (t ++ₛ η) = t' ++ₛ η := by
  unfold xFinInv at h
  split_ifs at h with h1 h2
  · obtain ⟨d, rfl⟩ := h1
    rw [List.drop_left] at h
    rw [Equiv.Perm.inv_eq_iff_eq]
    rcases d with _ | ⟨_ | _, d⟩
    · simp at h
    · simp at h
      subst h
      rw [Stream'.append_append_stream, Stream'.append_append_stream]
      show s ++ₛ ([false] ++ₛ (d ++ₛ η)) = genP (.x s) (s ++ₛ ([false, false] ++ₛ (d ++ₛ η)))
      rw [x_app, xFun_00]
    · rcases d with _ | ⟨_ | _, r⟩
      · simp at h
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show s ++ₛ ([true, false] ++ₛ (r ++ₛ η)) =
          genP (.x s) (s ++ₛ ([false, true] ++ₛ (r ++ₛ η)))
        rw [x_app, xFun_01]
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show s ++ₛ ([true, true] ++ₛ (r ++ₛ η)) = genP (.x s) (s ++ₛ ([true] ++ₛ (r ++ₛ η)))
        rw [x_app, xFun_1]
  · simp at h
    subst h
    exact xinv_fix (not_mem_cone_of_incompat h2 h1 η)

/-- `y_s^n` fixes the sequences outside `[s]`. -/
theorem genP_y_zpow_of_not_mem (s : Seq) (n : ℤ) (ξ : Str) (h : ξ ∉ cone s) :
    (genP (.y s) ^ n) ξ = ξ :=
  Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (y_fix h) n

/-- `y_s^n` maps `[s]` to itself. -/
theorem genP_y_zpow_mem_iff (s : Seq) (n : ℤ) (ξ : Str) :
    (genP (.y s) ^ n) ξ ∈ cone s ↔ ξ ∈ cone s := by
  constructor
  · intro h
    by_contra hξ
    rw [LM56.PartS2.genP_y_zpow_of_not_mem s n ξ hξ] at h
    exact hξ h
  · intro h
    by_contra h'
    have h'' := LM56.PartS2.genP_y_zpow_of_not_mem s (-n) _ h'
    rw [zpow_neg, Equiv.Perm.inv_eq_iff_eq] at h''
    rw [← (genP (.y s) ^ n).injective h''] at h'
    exact h' h

/-! ## `psi .D` -/

theorem psi_D_apply (ξ : Str) :
    psi .D ξ = genP (.y [false, false]) (genP (.y [false, true]) (genP (.y [true]) ξ)) := by
  show (act (W0.take 3)).symm ξ = _
  rw [show W0.take 3 = [(.y [false, false], -1), (.y [false, true], -1), (.y [true], -1)] from rfl,
    ← Equiv.Perm.inv_def]
  simp only [act, one_mul, zpow_neg_one, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

theorem psi_D_00 (ρ : Str) :
    psi .D ([false, false] ++ₛ ρ) = [false, false] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ),
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ), y_app]

theorem psi_D_01 (ρ : Str) :
    psi .D ([false, true] ++ₛ ρ) = [false, true] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ), y_app,
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) _)]

theorem psi_D_1 (ρ : Str) : psi .D ([true] ++ₛ ρ) = [true] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_app, y_fix (not_mem_cone_of_incompat (by decide) (by decide) _),
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) _)]

/-! ## Steps preserve the action -/

/-- Conjugating `y_t` by a permutation that replaces the prefix `t` by `t'` gives `y_{t'}`. -/
theorem semiconj_y {g : Equiv.Perm Str} {t t' : Seq} (hg : ∀ η, g (t ++ₛ η) = t' ++ₛ η) :
    SemiconjBy g (genP (.y t)) (genP (.y t')) := by
  show g * genP (.y t) = genP (.y t') * g
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases h : ξ ∈ cone t
  · obtain ⟨η, rfl⟩ := h
    rw [y_app, hg, hg, y_app]
  · rw [y_fix h]
    symm
    apply y_fix
    rintro ⟨η, hη⟩
    exact h ⟨η, g.injective (by rw [hg]; exact hη)⟩

/-- Letters with incompatible subscripts commute. -/
theorem commute_y {u v : Seq} (h : Incompatible u v) (i j : ℤ) :
    Commute (genP (.y u) ^ i) (genP (.y v) ^ j) := by
  show _ * _ = _ * _
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  have h' : Incompatible v u := ⟨h.2, h.1⟩
  by_cases hu : ξ ∈ cone u
  · have hAu := (LM56.PartS2.genP_y_zpow_mem_iff u i ξ).2 hu
    rw [LM56.PartS2.genP_y_zpow_of_not_mem v j ξ (not_mem_cone_of_incompatible h hu),
      LM56.PartS2.genP_y_zpow_of_not_mem v j _ (not_mem_cone_of_incompatible h hAu)]
  · rw [LM56.PartS2.genP_y_zpow_of_not_mem u i ξ hu]
    by_cases hv : ξ ∈ cone v
    · have hBv := (LM56.PartS2.genP_y_zpow_mem_iff v j ξ).2 hv
      rw [LM56.PartS2.genP_y_zpow_of_not_mem u i _ (not_mem_cone_of_incompatible h' hBv)]
    · rw [LM56.PartS2.genP_y_zpow_of_not_mem v j ξ hv,
        LM56.PartS2.genP_y_zpow_of_not_mem u i ξ hu]

theorem moveX_block {s t t' : Seq} (h : xFin s t = some t') (i : ℤ) :
    act [(.y t, i), (.x s, 1)] = act [(.x s, 1), (.y t', i)] := by
  simp only [act, one_mul, zpow_one]
  exact (semiconj_y (LM56.PartS2.genP_x_of_xFin h)).zpow_right i

theorem moveXInv_block {s t t' : Seq} (h : xFinInv s t = some t') (i : ℤ) :
    act [(.y t, i), (.x s, -1)] = act [(.x s, -1), (.y t', i)] := by
  simp only [act, one_mul, zpow_neg_one]
  exact (semiconj_y (LM56.PartS2.genP_x_inv_of_xFinInv h)).zpow_right i

theorem expand_block (s : Seq) :
    act [(.y s, 1)] = act [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
      (.y (s ++ [true, true]), 1)] := by
  simp only [act, one_mul, zpow_one, zpow_neg_one]
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hξ : ξ ∈ cone s
  · obtain ⟨ζ, rfl⟩ := hξ
    rcases tri_x ζ with ⟨η, rfl⟩ | ⟨η, rfl⟩ | ⟨η, rfl⟩
    · rw [y_app s, yFun_true_00, x_app s, xFun_00, y_app' s [false],
        yinv_fix (not_mem_cone_append (u := [false]) (v := [true, false]) s (by decide)
          (by decide) _),
        y_fix (not_mem_cone_append (u := [false]) (v := [true, true]) s (by decide)
          (by decide) _)]
    · rw [y_app s, yFun_true_01, x_app s, xFun_01,
        y_fix (not_mem_cone_append (u := [true, false]) (v := [false]) s (by decide)
          (by decide) _),
        yinv_app' s [true, false],
        y_fix (not_mem_cone_append (u := [true, false]) (v := [true, true]) s (by decide)
          (by decide) _)]
    · rw [y_app s, yFun_true_1, x_app s, xFun_1,
        y_fix (not_mem_cone_append (u := [true, true]) (v := [false]) s (by decide)
          (by decide) _),
        yinv_fix (not_mem_cone_append (u := [true, true]) (v := [true, false]) s (by decide)
          (by decide) _),
        y_app' s [true, true]]
  · rw [y_fix hξ, x_fix hξ, y_fix (not_mem_cone_append_of_not_mem hξ),
      yinv_fix (not_mem_cone_append_of_not_mem hξ), y_fix (not_mem_cone_append_of_not_mem hξ)]

theorem expandInv_block (s : Seq) :
    act [(.y s, -1)] = act [(.x s, -1), (.y (s ++ [false, false]), -1),
      (.y (s ++ [false, true]), 1), (.y (s ++ [true]), -1)] := by
  simp only [act, one_mul, zpow_one, zpow_neg_one]
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hξ : ξ ∈ cone s
  · obtain ⟨ζ, rfl⟩ := hξ
    rcases tri_xinv ζ with ⟨η, rfl⟩ | ⟨η, rfl⟩ | ⟨η, rfl⟩
    · rw [yinv_app s, yFun_false_0, xinv_app s, xInvFun_0, yinv_app' s [false, false],
        y_fix (not_mem_cone_append (u := [false, false]) (v := [false, true]) s (by decide)
          (by decide) _),
        yinv_fix (not_mem_cone_append (u := [false, false]) (v := [true]) s (by decide)
          (by decide) _)]
    · rw [yinv_app s, yFun_false_10, xinv_app s, xInvFun_10,
        yinv_fix (not_mem_cone_append (u := [false, true]) (v := [false, false]) s (by decide)
          (by decide) _),
        y_app' s [false, true],
        yinv_fix (not_mem_cone_append (u := [false, true]) (v := [true]) s (by decide)
          (by decide) _)]
    · rw [yinv_app s, yFun_false_11, xinv_app s, xInvFun_11,
        yinv_fix (not_mem_cone_append (u := [true]) (v := [false, false]) s (by decide)
          (by decide) _),
        y_fix (not_mem_cone_append (u := [true]) (v := [false, true]) s (by decide)
          (by decide) _),
        yinv_app' s [true]]
  · rw [yinv_fix hξ, xinv_fix hξ, yinv_fix (not_mem_cone_append_of_not_mem hξ),
      y_fix (not_mem_cone_append_of_not_mem hξ), yinv_fix (not_mem_cone_append_of_not_mem hξ)]

theorem commute_block {u v : Seq} (h : Incompatible u v) (i j : ℤ) :
    act [(.y u, i), (.y v, j)] = act [(.y v, j), (.y u, i)] := by
  simp only [act, one_mul]
  exact ((commute_y h i j).symm).eq

theorem split_block (g : Gen) (i j : ℤ) : act [(g, i + j)] = act [(g, i), (g, j)] := by
  simp only [act, one_mul]
  rw [add_comm, zpow_add]

theorem cancel_block (s : Seq) (i : ℤ) : act [(.y s, i), (.y s, -i)] = 1 := by
  simp only [act, one_mul, zpow_neg, inv_mul_cancel]

/-- Every substitution preserves the value. -/
theorem act_posStep {V V' : Word} (h : PosStep V V') : act V = act V' := by
  cases h with
  | moveX pre post s t t' i h => simp only [LM56.PartS2.act_append, moveX_block h i]
  | moveXInv pre post s t t' i h => simp only [LM56.PartS2.act_append, moveXInv_block h i]
  | expand pre post s => simp only [LM56.PartS2.act_append, expand_block s]
  | expandInv pre post s => simp only [LM56.PartS2.act_append, expandInv_block s]
  | commute pre post u v i j hi hj h =>
    simp only [LM56.PartS2.act_append, commute_block h i j]
  | split pre post g i j hi hj hij => simp only [LM56.PartS2.act_append, split_block g i j]
  | merge pre post g i j hi hj hij => simp only [LM56.PartS2.act_append, split_block g i j]
  | cancel pre post s i hi => simp only [LM56.PartS2.act_append, cancel_block s i, one_mul]

end LM56.PartS2
