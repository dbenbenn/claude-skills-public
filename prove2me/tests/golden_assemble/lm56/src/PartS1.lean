import Solutions.LM56.Blueprint

/-!
# Lemma 5.6 under positive commutation — part S1: functions of streams

The recursion equations of `x`, `x⁻¹`, `y`, `y⁻¹`, the inverse laws, and the basic facts about
`localize`.
-/

open LodhaMoore LM56

namespace LM56.PartS1

/-! ## Digits of `l ++ₛ s` -/

/-- Every stream is its first two digits followed by the rest. -/
theorem decomp2 (ξ : Str) : ξ = [ξ 0, ξ 1] ++ₛ ξ.drop 2 := by
  apply Stream'.ext
  intro n
  rcases n with _ | _ | n <;> rfl

/-- Two streams with the same finite prefix agree at a digit if the tails agree at the
corresponding digit. -/
theorem append_get_eq (l : List Bool) (s t : Str) (n : ℕ)
    (h : ∀ j, l.length + j = n → s j = t j) : (l ++ₛ s) n = (l ++ₛ t) n := by
  rcases lt_or_ge n l.length with hn | hn
  · exact (Stream'.get_append_left n l s hn).trans (Stream'.get_append_left n l t hn).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (Stream'.get_append_right j l s).trans
      ((h j rfl).trans (Stream'.get_append_right j l t).symm)

/-! ## `x` and `x⁻¹` -/

theorem xFun_00 (η : Str) : xFun ([false, false] ++ₛ η) = [false] ++ₛ η := rfl
theorem xFun_01 (η : Str) : xFun ([false, true] ++ₛ η) = [true, false] ++ₛ η := rfl
theorem xFun_1 (η : Str) : xFun ([true] ++ₛ η) = [true, true] ++ₛ η := rfl

theorem xInvFun_0 (η : Str) : xInvFun ([false] ++ₛ η) = [false, false] ++ₛ η := rfl
theorem xInvFun_10 (η : Str) : xInvFun ([true, false] ++ₛ η) = [false, true] ++ₛ η := rfl
theorem xInvFun_11 (η : Str) : xInvFun ([true, true] ++ₛ η) = [true] ++ₛ η := rfl

theorem xInvFun_xFun (ξ : Str) : xInvFun (xFun ξ) = ξ := by
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases a <;> cases b
  · rw [PartS1.xFun_00, PartS1.xInvFun_0]
  · rw [PartS1.xFun_01, PartS1.xInvFun_10]
  · exact (congrArg xInvFun (PartS1.xFun_1 ([false] ++ₛ η))).trans
      (PartS1.xInvFun_11 ([false] ++ₛ η))
  · exact (congrArg xInvFun (PartS1.xFun_1 ([true] ++ₛ η))).trans
      (PartS1.xInvFun_11 ([true] ++ₛ η))

theorem xFun_xInvFun (ξ : Str) : xFun (xInvFun ξ) = ξ := by
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases a <;> cases b
  · exact (congrArg xFun (PartS1.xInvFun_0 ([false] ++ₛ η))).trans
      (PartS1.xFun_00 ([false] ++ₛ η))
  · exact (congrArg xFun (PartS1.xInvFun_0 ([true] ++ₛ η))).trans
      (PartS1.xFun_00 ([true] ++ₛ η))
  · rw [PartS1.xInvFun_10, PartS1.xFun_01]
  · rw [PartS1.xInvFun_11, PartS1.xFun_1]

/-! ## The recursion of `y` and `y⁻¹` -/

/-- Each step of the recursion outputs at least one digit. -/
theorem one_le_length_yStep (σ : Bool) (ξ : Str) : 1 ≤ (yStep σ ξ).1.length := by
  cases σ <;> simp only [yStep] <;> split <;> simp

/-- The first `k` steps output at least `k` digits. -/
theorem le_length_yOut (k : ℕ) (σ : Bool) (ξ : Str) : k ≤ (yOut k σ ξ).length := by
  induction k generalizing σ ξ with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := one_le_length_yStep σ ξ
    have h2 := ih (yStep σ ξ).2.1 (yStep σ ξ).2.2
    show k + 1 ≤ ((yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2).length
    rw [List.length_append]
    omega

/-- `yOut k` is a prefix of `yOut (k + 1)`. -/
theorem yOut_prefix_succ (k : ℕ) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut (k + 1) σ ξ := by
  induction k generalizing σ ξ with
  | zero => exact List.nil_prefix
  | succ k ih =>
    show (yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2 <+:
      (yStep σ ξ).1 ++ yOut (k + 1) (yStep σ ξ).2.1 (yStep σ ξ).2.2
    exact (List.prefix_append_right_inj _).2 (ih _ _)

theorem yOut_prefix_of_le {k m : ℕ} (h : k ≤ m) (σ : Bool) (ξ : Str) :
    yOut k σ ξ <+: yOut m σ ξ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (yOut_prefix_succ _ _ _)

/-- Digit `n` of `yFun` is digit `n` of the output of any number of steps that reaches it. -/
theorem yFun_eq_getD {σ : Bool} {ξ : Str} {n m : ℕ} (h : n < (yOut m σ ξ).length) :
    yFun σ ξ n = (yOut m σ ξ).getD n false := by
  show (yOut (n + 1) σ ξ).getD n false = _
  have h1 : n < (yOut (n + 1) σ ξ).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (le_length_yOut _ _ _)
  rcases le_total (n + 1) m with hm | hm
  · obtain ⟨t, ht⟩ := yOut_prefix_of_le hm σ ξ
    rw [← ht, List.getD_append _ _ _ _ h1]
  · obtain ⟨t, ht⟩ := yOut_prefix_of_le hm σ ξ
    rw [← ht, List.getD_append _ _ _ _ h]

/-- One step of the recursion. -/
theorem yFun_step (σ : Bool) (ξ : Str) :
    yFun σ ξ = (yStep σ ξ).1 ++ₛ yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 := by
  apply Stream'.ext
  intro n
  have ho := one_le_length_yStep σ ξ
  have hrec : ∀ k, yOut (k + 1) σ ξ =
      (yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2 := fun _ => rfl
  rcases lt_or_ge n (yStep σ ξ).1.length with hn | hn
  · rw [Stream'.get_append_left _ _ _ hn]
    show (yOut (n + 1) σ ξ).getD n false = _
    rw [hrec, List.getD_append _ _ _ _ hn, List.getD_eq_getElem _ _ hn]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Stream'.get_append_right]
    show (yOut ((yStep σ ξ).1.length + j + 1) σ ξ).getD ((yStep σ ξ).1.length + j) false = _
    rw [hrec, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have hlen := le_length_yOut ((yStep σ ξ).1.length + j) (yStep σ ξ).2.1 (yStep σ ξ).2.2
    exact (yFun_eq_getD (by omega)).symm

theorem yFun_true_00 (η : Str) : yFun true ([false, false] ++ₛ η) = [false] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
theorem yFun_true_01 (η : Str) :
    yFun true ([false, true] ++ₛ η) = [true, false] ++ₛ yFun false η := by
  rw [yFun_step]; rfl
theorem yFun_true_1 (η : Str) : yFun true ([true] ++ₛ η) = [true, true] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
theorem yFun_false_0 (η : Str) :
    yFun false ([false] ++ₛ η) = [false, false] ++ₛ yFun false η := by
  rw [yFun_step]; rfl
theorem yFun_false_10 (η : Str) :
    yFun false ([true, false] ++ₛ η) = [false, true] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
theorem yFun_false_11 (η : Str) :
    yFun false ([true, true] ++ₛ η) = [true] ++ₛ yFun false η := by
  rw [yFun_step]; rfl

/-! ## The inverse laws of `y` -/

/-- `yFun (!σ)` inverts `yFun σ`, digit by digit. -/
theorem yFun_not_yFun_get (n : ℕ) : ∀ (σ : Bool) (ξ : Str), yFun (!σ) (yFun σ ξ) n = ξ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ ξ
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases σ <;> cases a <;> cases b
  -- `y⁻¹`
  · show yFun true (yFun false ([false] ++ₛ ([false] ++ₛ η))) n = ([false] ++ₛ ([false] ++ₛ η)) n
    rw [PartS1.yFun_false_0, PartS1.yFun_true_00]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun true (yFun false ([false] ++ₛ ([true] ++ₛ η))) n = ([false] ++ₛ ([true] ++ₛ η)) n
    rw [PartS1.yFun_false_0, PartS1.yFun_true_00]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun true (yFun false ([true, false] ++ₛ η)) n = ([true, false] ++ₛ η) n
    rw [PartS1.yFun_false_10, PartS1.yFun_true_01]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun true (yFun false ([true, true] ++ₛ η)) n = ([true, true] ++ₛ η) n
    rw [PartS1.yFun_false_11, PartS1.yFun_true_1]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  -- `y`
  · show yFun false (yFun true ([false, false] ++ₛ η)) n = ([false, false] ++ₛ η) n
    rw [PartS1.yFun_true_00, PartS1.yFun_false_0]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun false (yFun true ([false, true] ++ₛ η)) n = ([false, true] ++ₛ η) n
    rw [PartS1.yFun_true_01, PartS1.yFun_false_10]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun false (yFun true ([true] ++ₛ ([false] ++ₛ η))) n = ([true] ++ₛ ([false] ++ₛ η)) n
    rw [PartS1.yFun_true_1, PartS1.yFun_false_11]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun false (yFun true ([true] ++ₛ ([true] ++ₛ η))) n = ([true] ++ₛ ([true] ++ₛ η)) n
    rw [PartS1.yFun_true_1, PartS1.yFun_false_11]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _

theorem yFun_false_true (ξ : Str) : yFun false (yFun true ξ) = ξ :=
  Stream'.ext fun n => yFun_not_yFun_get n true ξ

theorem yFun_true_false (ξ : Str) : yFun true (yFun false ξ) = ξ :=
  Stream'.ext fun n => yFun_not_yFun_get n false ξ

/-! ## Localization -/

theorem localize_append (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  unfold localize
  rw [if_pos (by rw [Stream'.take_append_of_le_length _ _ _ le_rfl, List.take_length]),
    Stream'.drop_append_stream]

theorem localize_of_not_mem (s : Seq) (f : Str → Str) (ξ : Str) (h : ξ ∉ cone s) :
    localize s f ξ = ξ := by
  unfold localize
  rw [if_neg]
  intro h'
  apply h
  have := Stream'.append_take_drop s.length ξ
  rw [h'] at this
  exact ⟨_, this⟩

theorem localize_symm (s : Seq) (p : Equiv.Perm Str) (ξ : Str) :
    localize s p.symm (localize s p ξ) = ξ := by
  by_cases h : ξ ∈ cone s
  · obtain ⟨η, rfl⟩ := h
    rw [PartS1.localize_append, PartS1.localize_append, Equiv.symm_apply_apply]
  · rw [PartS1.localize_of_not_mem s _ ξ h, PartS1.localize_of_not_mem s _ ξ h]

end LM56.PartS1
