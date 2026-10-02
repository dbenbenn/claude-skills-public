import Solutions.LM56.Blueprint

/-!
# Lemma 5.6 under positive commutation — part L: the forest

`Forest.not_pos_pos` and `Forest.region_ne`, each from an invariant of the form
`List.IsChain R L` (a relation between consecutive labels) proved by induction on `Forest`.
-/

open LodhaMoore LM56

namespace LM56.PartL

/-! ### Expanding one entry of a chain -/

/-- Replacing the entry `a` of a chain by `a₁, a₂, a₃` keeps it a chain, when `a₁` inherits the
left relations of `a` and `a₃` its right relations. -/
theorem isChain_expand {α : Type*} {R : α → α → Prop} {L₁ L₂ : List α} {a a₁ a₂ a₃ : α}
    (h : List.IsChain R (L₁ ++ [a] ++ L₂))
    (hl : ∀ x, R x a → R x a₁) (hr : ∀ y, R a y → R a₃ y) (h12 : R a₁ a₂) (h23 : R a₂ a₃) :
    List.IsChain R (L₁ ++ [a₁, a₂, a₃] ++ L₂) := by
  rw [List.isChain_append, List.isChain_append] at h
  obtain ⟨⟨h1, -, h1a⟩, h2, ha2⟩ := h
  refine List.isChain_append.2 ⟨List.isChain_append.2 ⟨h1, ?_, ?_⟩, h2, ?_⟩
  · simp [List.isChain_cons_cons, h12, h23]
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hl x (h1a x hx a (by simp))
  · intro x hx y hy
    have hx' : a₃ = x := by simpa using hx
    subst hx'
    exact hr y (ha2 a (by simp) y hy)

/-! ### Signs -/

/-- Two consecutive labels are not both positive. -/
def SignRel (a b : Label) : Prop := ¬ (a.2.2 = true ∧ b.2.2 = true)

theorem isChain_sign {L : List Label} (hL : Forest L) : List.IsChain SignRel L := by
  induction hL with
  | init => simp [List.isChain_cons_cons, SignRel]
  | expandPos L₁ L₂ r w _ ih =>
    exact isChain_expand ih (fun _ hx => hx) (fun _ hy => hy) (by simp [SignRel])
      (by simp [SignRel])
  | expandNeg L₁ L₂ r w _ ih =>
    exact isChain_expand ih (fun _ _ => by simp [SignRel]) (fun _ _ => by simp [SignRel])
      (by simp [SignRel]) (by simp [SignRel])

/-- No two consecutive labels are positive. -/
theorem Forest.not_pos_pos {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    ¬ (L[i].2.2 = true ∧ L[i + 1].2.2 = true) :=
  (isChain_sign hL).getElem i hi

/-! ### Incompatibility -/

theorem incompatible_append_right {u v : Seq} (x : Seq) (h : Incompatible u v) :
    Incompatible u (v ++ x) := by
  refine ⟨fun h' => ?_, fun h' => h.2 ((List.prefix_append v x).trans h')⟩
  rcases List.prefix_or_prefix_of_prefix h' (List.prefix_append v x) with h'' | h''
  · exact h.1 h''
  · exact h.2 h''

theorem incompatible_append_left {u v : Seq} (x : Seq) (h : Incompatible u v) :
    Incompatible (u ++ x) v :=
  let h' := incompatible_append_right x ⟨h.2, h.1⟩
  ⟨h'.2, h'.1⟩

theorem incompatible_append_same (w : Seq) {x y : Seq} (h : Incompatible x y) :
    Incompatible (w ++ x) (w ++ y) := by
  simpa [Incompatible] using h

/-- Two sequences with a common extension are comparable. -/
theorem prefix_or_prefix_of_append_stream_eq :
    ∀ {u v : Seq} {η η' : Str}, u ++ₛ η = v ++ₛ η' → u <+: v ∨ v <+: u
  | [], _, _, _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _, _, _ => Or.inr (List.nil_prefix)
  | b :: u, b' :: v, η, η', h => by
    rw [Stream'.cons_append_stream, Stream'.cons_append_stream] at h
    have hb : b = b' := by simpa using congrArg Stream'.head h
    have ht : u ++ₛ η = v ++ₛ η' := by simpa using congrArg Stream'.tail h
    subst hb
    rcases prefix_or_prefix_of_append_stream_eq ht with h' | h'
    · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h'⟩)
    · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h'⟩)

theorem not_incompatible_of_append_stream_eq {u v : Seq} {η η' : Str}
    (h : u ++ₛ η = v ++ₛ η') : ¬ Incompatible u v := by
  rintro ⟨h1, h2⟩
  rcases prefix_or_prefix_of_append_stream_eq h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ### Regions -/

theorem append_stream_inj (u : Seq) {η η' : Str} (h : u ++ₛ η = u ++ₛ η') : η = η' := by
  rw [← Stream'.drop_append_stream u η, h, Stream'.drop_append_stream]

theorem psi_injective (r : Root) : Function.Injective (psi r) := by
  cases r with
  | D => exact (act (W0.take 3)).symm.injective
  | A => exact fun _ _ h => append_stream_inj [false, false] h
  | B => exact fun _ _ h => append_stream_inj [false, true] h
  | C => exact fun _ _ h => append_stream_inj [true] h

theorem append_stream_mem_cone (u : Seq) (η : Str) : u ++ₛ η ∈ cone u := ⟨η, rfl⟩

/-- Consecutive labels are related: same root and incompatible leaves, or roots `A|B`, `B|C`,
or `C|D` with the `D` leaf empty or starting with `00`. -/
def RegRel (a b : Label) : Prop :=
  (a.1 = b.1 ∧ Incompatible a.2.1 b.2.1) ∨
  (a.1 = .A ∧ b.1 = .B) ∨ (a.1 = .B ∧ b.1 = .C) ∨
  (a.1 = .C ∧ b.1 = .D ∧ (b.2.1 = [] ∨ [false, false] <+: b.2.1))

/-- The empty leaf of `D` is positive. -/
def DOk (a : Label) : Prop := a.1 = .D → a.2.1 = [] → a.2.2 = true

theorem regRel_region_ne {a b : Label} (h : RegRel a b) : region a ≠ region b := by
  obtain ⟨r, u, c⟩ := a
  obtain ⟨r', v, c'⟩ := b
  intro hab
  simp only [RegRel] at h
  rcases h with ⟨hr, hi⟩ | ⟨hr, hr'⟩ | ⟨hr, hr'⟩ | ⟨hr, hr', hv⟩
  · -- same root, incompatible leaves
    subst hr
    have hm : psi r (u ++ₛ Stream'.const false) ∈ region (r, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, ⟨η', rfl⟩, hξ⟩ := hm
    exact not_incompatible_of_append_stream_eq (psi_injective r hξ).symm hi
  · subst hr hr'
    have hm : psi .A (u ++ₛ Stream'.const false) ∈ region (.B, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide
  · subst hr hr'
    have hm : psi .B (u ++ₛ Stream'.const false) ∈ region (.C, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide
  · subst hr hr'
    -- an element `ψ_D (00 ρ) = 00 (ρ.y)` of the `D` region
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Str, [false, false] ++ₛ ρ ∈ cone v := by
      rcases hv with rfl | ⟨v', rfl⟩
      · exact ⟨Stream'.const false, [false, false] ++ₛ Stream'.const false, rfl⟩
      · exact ⟨v' ++ₛ Stream'.const false, Stream'.const false,
          Stream'.append_append_stream _ _ _⟩
    have hm : psi .D ([false, false] ++ₛ ρ) ∈ region (.C, u, c) := by
      rw [hab]; exact ⟨_, hρ, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    rw [psi_D_00] at hξ
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide

theorem regInv {L : List Label} (hL : Forest L) :
    List.IsChain RegRel L ∧ ∀ a ∈ L, DOk a := by
  induction hL with
  | init =>
    refine ⟨?_, ?_⟩
    · simp [List.isChain_cons_cons, RegRel]
    · simp [DOk]
  | expandPos L₁ L₂ r w _ ih =>
    refine ⟨isChain_expand ih.1 ?_ ?_ ?_ ?_, ?_⟩
    · rintro ⟨x, xw, xc⟩ hx
      simp only [RegRel] at hx ⊢
      rcases hx with ⟨hr, hi⟩ | h | h | ⟨hr, hr', hv⟩
      · exact Or.inl ⟨hr, incompatible_append_right _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨hr, hr', Or.inr ?_⟩))
        rcases hv with rfl | hv
        · simp
        · exact hv.trans (List.prefix_append _ _)
    · rintro ⟨y, yw, yc⟩ hy
      simp only [RegRel] at hy ⊢
      rcases hy with ⟨hr, hi⟩ | h | h | h
      · exact Or.inl ⟨hr, incompatible_append_left _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (ha | ha | ha | ha) | ha
      · exact ih.2 a (by simp [ha])
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · exact ih.2 a (by simp [ha])
  | expandNeg L₁ L₂ r w _ ih =>
    have hD : DOk (r, w, false) := ih.2 _ (by simp)
    refine ⟨isChain_expand ih.1 ?_ ?_ ?_ ?_, ?_⟩
    · rintro ⟨x, xw, xc⟩ hx
      simp only [RegRel] at hx ⊢
      rcases hx with ⟨hr, hi⟩ | h | h | ⟨hr, hr', hv⟩
      · exact Or.inl ⟨hr, incompatible_append_right _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨hr, hr', Or.inr ?_⟩))
        rcases hv with rfl | hv
        · exact absurd (hD hr' rfl) (by simp)
        · exact hv.trans (List.prefix_append _ _)
    · rintro ⟨y, yw, yc⟩ hy
      simp only [RegRel] at hy ⊢
      rcases hy with ⟨hr, hi⟩ | h | h | h
      · exact Or.inl ⟨hr, incompatible_append_left _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (ha | ha | ha | ha) | ha
      · exact ih.2 a (by simp [ha])
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · exact ih.2 a (by simp [ha])

/-- Consecutive labels have different regions. -/
theorem Forest.region_ne {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    region L[i] ≠ region L[i + 1] :=
  regRel_region_ne ((regInv hL).1.getElem i hi)

end LM56.PartL
