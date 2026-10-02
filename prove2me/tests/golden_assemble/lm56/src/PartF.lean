import Solutions.LM56.Blueprint

/-!
# Lemma 5.6 under positive commutation — part F

`isStandardForm_W0` and `not_sufficientlyExpanded_of_frozen` (RESULT.md §5).

Plan of the main proof:
* cones of finite sequences (`mem_cone_iff`, compatibility, the non-cone lemma `ne_cone`);
* the advance lemma `ADV` and the forest invariant `Inv` (D-leaf shapes, coverage, block order);
* the support fact (g): in a standard form, the letters before a `y_t` preserve `[t]` and `[t z]`;
* reading `Good` along `Ξ ++ Υ`: every label's region is `g⁻¹[t_k]` with `g` the value of `Ξ`;
* phase 1 (`(D, [], true)` is a label) and phase 2 (some `(D, 00w, c)` is a label).
-/

open LodhaMoore LM56

namespace LM56.PartF

/-! ## 1. Cones -/

theorem mem_cone_iff {ξ : Str} {p : Seq} :
    ξ ∈ cone p ↔ ∀ i (h : i < p.length), ξ.get i = p[i] := by
  constructor
  · rintro ⟨η, rfl⟩ i h
    exact Stream'.get_append_left i p η h
  · intro h
    refine ⟨ξ.drop p.length, ?_⟩
    funext n
    show (p ++ₛ ξ.drop p.length).get n = ξ.get n
    by_cases hn : n < p.length
    · rw [Stream'.get_append_left n p _ hn, h n hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = p.length + m := ⟨n - p.length, by omega⟩
      rw [Stream'.get_append_right, Stream'.get_drop]

theorem append_mem_cone (p : Seq) (η : Str) : p ++ₛ η ∈ cone p := ⟨η, rfl⟩

theorem cone_nil : cone [] = Set.univ := by
  ext ξ
  simp [mem_cone_iff]

theorem cone_mono {p q : Seq} (h : p <+: q) : cone q ⊆ cone p := by
  obtain ⟨r, rfl⟩ := h
  rintro _ ⟨η, rfl⟩
  exact ⟨r ++ₛ η, (Stream'.append_append_stream p r η).symm⟩

theorem append_mem_cone_append {ρ : Str} {p : Seq} (w : Seq) (h : ρ ∈ cone p) :
    w ++ₛ ρ ∈ cone (w ++ p) := by
  obtain ⟨η, rfl⟩ := h
  exact ⟨η, (Stream'.append_append_stream w p η)⟩

theorem prefix_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hq : ξ ∈ cone q)
    (hl : p.length ≤ q.length) : p <+: q := by
  rw [mem_cone_iff] at hp hq
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    rw [List.getElem_take, ← hp i h1, hq i (by omega)]

theorem compat_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hq : ξ ∈ cone q) :
    p <+: q ∨ q <+: p := by
  rcases le_total p.length q.length with h | h
  · exact Or.inl (prefix_of_mem_cone hp hq h)
  · exact Or.inr (prefix_of_mem_cone hq hp h)

theorem not_incompatible_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p)
    (hq : ξ ∈ cone q) : ¬ Incompatible p q := by
  rintro ⟨h1, h2⟩
  rcases compat_of_mem_cone hp hq with h | h
  · exact h1 h
  · exact h2 h

/-- `q η ∈ [p]` for `|p| ≤ |q|` iff `p` is a prefix of `q`. -/
theorem append_mem_cone_iff {p q : Seq} (η : Str) (hl : p.length ≤ q.length) :
    q ++ₛ η ∈ cone p ↔ p <+: q :=
  ⟨fun h => prefix_of_mem_cone h (append_mem_cone q η) hl,
    fun h => cone_mono h (append_mem_cone q η)⟩

theorem append_left_cancel {p : Seq} {α β : Str} (h : p ++ₛ α = p ++ₛ β) : α = β := by
  funext n
  have := congrArg (fun s : Str => s.get (p.length + n)) h
  simp only [Stream'.get_append_right] at this
  exact this

theorem image_append_cone (p w : Seq) : (fun η => p ++ₛ η) '' cone w = cone (p ++ w) := by
  ext ξ
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    exact ⟨η, Stream'.append_append_stream p w η⟩
  · rintro ⟨η, rfl⟩
    exact ⟨w ++ₛ η, ⟨η, rfl⟩, (Stream'.append_append_stream p w η).symm⟩

theorem eq_nil_of_cone_eq_univ {p : Seq} (h : cone p = Set.univ) : p = [] := by
  cases p with
  | nil => rfl
  | cons a p =>
    have hm : ([!a] ++ₛ Stream'.const false) ∈ cone (a :: p) := h ▸ Set.mem_univ _
    rw [mem_cone_iff] at hm
    have := hm 0 (by simp)
    rw [Stream'.get_append_left 0 [!a] _ (by simp)] at this
    cases a <;> simp at this

/-- The non-cone lemma (NC): a set containing `q a α` and `q (¬a) β` but not some `q γ` is not a
cone. -/
theorem ne_cone {S : Set Str} {q : Seq} {a : Bool} {α β γ : Str}
    (h1 : q ++ₛ Stream'.cons a α ∈ S) (h2 : q ++ₛ Stream'.cons (!a) β ∈ S) (h3 : q ++ₛ γ ∉ S)
    (p : Seq) : S ≠ cone p := by
  rintro rfl
  rw [mem_cone_iff] at h1 h2
  apply h3
  rw [mem_cone_iff]
  by_cases hl : q.length < p.length
  · exfalso
    have e1 := h1 (q.length + 0) (by omega)
    have e2 := h2 (q.length + 0) (by omega)
    rw [Stream'.get_append_right, Stream'.get_zero_cons] at e1 e2
    rw [← e1] at e2
    cases a <;> simp at e2
  · intro i hi
    rw [Stream'.get_append_left i q _ (by omega), ← h1 i hi, Stream'.get_append_left i q _ (by omega)]

/-! ## 2. `W0` is a standard form -/

theorem isStandardForm_W0 : IsStandardForm W0 := by
  refine ⟨?_, ⟨[], W0, rfl, ?_, ?_⟩, ?_⟩
  · simp [IsWord, W0]
  · simp [IsXWord, IsWord]
  · refine ⟨by simp [IsWord, W0], ?_⟩
    simp [W0]
  · intro i j hi hj s t m n h1 h2 hp
    simp only [W0, List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      first
      | omega
      | (simp only [W0, List.getElem_cons_zero, List.getElem_cons_succ, Prod.mk.injEq,
            Gen.y.injEq] at h1 h2
         obtain ⟨rfl, -⟩ := h1
         obtain ⟨rfl, -⟩ := h2
         exact absurd hp (by decide))

/-! ## 3. The advance lemma (ADV) -/

/-- `(w η).y^σ = o (η.y^c)` for some output `o`. -/
def ADV (σ : Bool) (w : Seq) (c : Bool) : Prop :=
  ∃ o : Seq, ∀ η, yFun σ (w ++ₛ η) = o ++ₛ yFun c η

theorem adv_nil (σ : Bool) : ADV σ [] σ := ⟨[], fun η => by simp⟩

theorem adv_pos {σ : Bool} {w : Seq} (h : ADV σ w true) :
    ADV σ (w ++ [false, false]) true ∧ ADV σ (w ++ [false, true]) false ∧
      ADV σ (w ++ [true]) true := by
  obtain ⟨o, ho⟩ := h
  refine ⟨⟨o ++ [false], fun η => ?_⟩, ⟨o ++ [true, false], fun η => ?_⟩,
    ⟨o ++ [true, true], fun η => ?_⟩⟩
  · rw [Stream'.append_append_stream, ho, yFun_true_00, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_true_01, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_true_1, Stream'.append_append_stream]

theorem adv_neg {σ : Bool} {w : Seq} (h : ADV σ w false) :
    ADV σ (w ++ [false]) false ∧ ADV σ (w ++ [true, false]) true ∧
      ADV σ (w ++ [true, true]) false := by
  obtain ⟨o, ho⟩ := h
  refine ⟨⟨o ++ [false, false], fun η => ?_⟩, ⟨o ++ [false, true], fun η => ?_⟩,
    ⟨o ++ [true], fun η => ?_⟩⟩
  · rw [Stream'.append_append_stream, ho, yFun_false_0, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_false_10, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_false_11, Stream'.append_append_stream]

/-! ## 4. The forest invariant -/

/-- The block order of the roots. -/
def rank : Root → ℕ
  | .A => 0
  | .B => 1
  | .C => 2
  | .D => 3

/-- The shape of a `D`-leaf: the root (positive), or a leaf of the `00`, `01` or `1` subtree, with
the advance lemma for the `00` subtree. -/
def DShape (w : Seq) (c : Bool) : Prop :=
  (w = [] ∧ c = true) ∨ (∃ w', w = [false, false] ++ w' ∧ ADV true w' c) ∨
    (∃ w', w = [false, true] ++ w') ∨ (∃ w', w = [true] ++ w')

theorem dShape_pos {w : Seq} (h : DShape w true) :
    DShape (w ++ [false, false]) true ∧ DShape (w ++ [false, true]) false ∧
      DShape (w ++ [true]) true := by
  rcases h with ⟨rfl, -⟩ | ⟨w', rfl, hw⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact ⟨Or.inr (Or.inl ⟨[], rfl, adv_nil true⟩), Or.inr (Or.inr (Or.inl ⟨[], rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨[], rfl⟩))⟩
  · obtain ⟨h1, h2, h3⟩ := adv_pos hw
    exact ⟨Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h1⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h2⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h3⟩)⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩))⟩

theorem dShape_neg {w : Seq} (h : DShape w false) :
    DShape (w ++ [false]) false ∧ DShape (w ++ [true, false]) true ∧
      DShape (w ++ [true, true]) false := by
  rcases h with ⟨-, h⟩ | ⟨w', rfl, hw⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact absurd h (by decide)
  · obtain ⟨h1, h2, h3⟩ := adv_neg hw
    exact ⟨Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h1⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h2⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h3⟩)⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩))⟩

/-- The facts about `Forest` used here: D-leaf shapes, each tree's leaves cover every sequence,
and the roots come in the order `A, B, C, D`. -/
structure Inv (L : List Label) : Prop where
  shape : ∀ l ∈ L, l.1 = .D → DShape l.2.1 l.2.2
  cover : ∀ (r : Root) (η : Str), ∃ l ∈ L, l.1 = r ∧ η ∈ cone l.2.1
  order : L.Pairwise (fun a b => rank a.1 ≤ rank b.1)

theorem eq_append_two (ρ : Str) : ∃ a b ρ', ρ = [a, b] ++ₛ ρ' :=
  ⟨_, _, _, (Stream'.append_take_drop 2 ρ).symm⟩

theorem cone_cases_pos (ρ : Str) :
    ρ ∈ cone [false, false] ∨ ρ ∈ cone [false, true] ∨ ρ ∈ cone [true] := by
  obtain ⟨a, b, ρ', rfl⟩ := eq_append_two ρ
  cases a <;> cases b
  · exact Or.inl ⟨ρ', rfl⟩
  · exact Or.inr (Or.inl ⟨ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨[false] ++ₛ ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨[true] ++ₛ ρ', rfl⟩)

theorem cone_cases_neg (ρ : Str) :
    ρ ∈ cone [false] ∨ ρ ∈ cone [true, false] ∨ ρ ∈ cone [true, true] := by
  obtain ⟨a, b, ρ', rfl⟩ := eq_append_two ρ
  cases a <;> cases b
  · exact Or.inl ⟨[false] ++ₛ ρ', rfl⟩
  · exact Or.inl ⟨[true] ++ₛ ρ', rfl⟩
  · exact Or.inr (Or.inl ⟨ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨ρ', rfl⟩)

theorem pairwise_replace {L₁ L₂ M : List Label} {a : Label}
    (h : (L₁ ++ [a] ++ L₂).Pairwise (fun a b => rank a.1 ≤ rank b.1))
    (hM : ∀ b ∈ M, b.1 = a.1) :
    (L₁ ++ M ++ L₂).Pairwise (fun a b => rank a.1 ≤ rank b.1) := by
  rw [List.pairwise_append, List.pairwise_append] at h ⊢
  obtain ⟨⟨h1, -, h3⟩, h4, h5⟩ := h
  refine ⟨⟨h1, ?_, ?_⟩, h4, ?_⟩
  · exact List.pairwise_of_forall_mem_list (fun x hx y hy => by rw [hM x hx, hM y hy])
  · intro x hx y hy
    rw [hM y hy]
    exact h3 x hx a (List.mem_singleton_self a)
  · intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact h5 x (List.mem_append_left _ hx) y hy
    · rw [hM x hx]
      exact h5 a (List.mem_append_right _ (List.mem_singleton_self a)) y hy

theorem inv_of_forest {L : List Label} (hF : Forest L) : Inv L := by
  induction hF with
  | init =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> simp_all [DShape]
    · intro r η
      cases r
      · exact ⟨(.A, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.B, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.C, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.D, [], true), by simp, rfl, by simp [cone_nil]⟩
    · decide
  | expandPos L₁ L₂ r w _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl | rfl | rfl) | hl
      · exact ih.shape l (by simp [hl]) hD
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).1
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).2.1
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).2.2
      · exact ih.shape l (by simp [hl]) hD
    · intro r' η
      obtain ⟨l, hl, hr, hη⟩ := ih.cover r' η
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl) | hl
      · exact ⟨l, by simp [hl], hr, hη⟩
      · obtain ⟨ρ, rfl⟩ := hη
        rcases cone_cases_pos ρ with h | h | h
        · exact ⟨(r, w ++ [false, false], true), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [false, true], false), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true], true), by simp, hr, append_mem_cone_append w h⟩
      · exact ⟨l, by simp [hl], hr, hη⟩
    · exact pairwise_replace ih.order (by simp)
  | expandNeg L₁ L₂ r w _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl | rfl | rfl) | hl
      · exact ih.shape l (by simp [hl]) hD
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).1
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).2.1
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).2.2
      · exact ih.shape l (by simp [hl]) hD
    · intro r' η
      obtain ⟨l, hl, hr, hη⟩ := ih.cover r' η
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl) | hl
      · exact ⟨l, by simp [hl], hr, hη⟩
      · obtain ⟨ρ, rfl⟩ := hη
        rcases cone_cases_neg ρ with h | h | h
        · exact ⟨(r, w ++ [false], false), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true, false], true), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true, true], false), by simp, hr, append_mem_cone_append w h⟩
      · exact ⟨l, by simp [hl], hr, hη⟩
    · exact pairwise_replace ih.order (by simp)

/-! ## 5. Regions of labels -/

theorem psi_D_eq : psi .D = ⇑(act (W0.take 3)).symm := rfl

theorem psi_D_injective : Function.Injective (psi .D) := by
  rw [psi_D_eq]; exact Equiv.injective _

theorem psi_D_surjective : Function.Surjective (psi .D) := by
  rw [psi_D_eq]; exact Equiv.surjective _

theorem region_D_nil (c : Bool) : region (.D, [], c) = Set.univ := by
  show psi .D '' cone [] = Set.univ
  rw [cone_nil, Set.image_univ, psi_D_surjective.range_eq]

theorem psi_D_00_append {w : Seq} (v : Seq) (η : Str) :
    psi .D (([false, false] ++ w ++ v) ++ₛ η) = [false, false] ++ₛ yFun true (w ++ₛ (v ++ₛ η)) := by
  rw [Stream'.append_append_stream, Stream'.append_append_stream, psi_D_00]

theorem yFun_inv (c : Bool) (ζ : Str) : yFun c (yFun (!c) ζ) = ζ := by
  cases c
  · exact yFun_false_true ζ
  · exact yFun_true_false ζ

/-- Every region is everything, or lies in `[00]`, `[01]` or `[1]`. -/
theorem region_cls1 {L : List Label} (hI : Inv L) {l : Label} (hl : l ∈ L) :
    region l = Set.univ ∨ region l ⊆ cone [false, false] ∨ region l ⊆ cone [false, true] ∨
      region l ⊆ cone [true] := by
  obtain ⟨r, w, c⟩ := l
  cases r with
  | A => exact Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | B => exact Or.inr (Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _)))
  | C => exact Or.inr (Or.inr (Or.inr (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _)))
  | D =>
    rcases hI.shape _ hl rfl with ⟨h, -⟩ | ⟨w', h, -⟩ | ⟨w', h⟩ | ⟨w', h⟩ <;>
      simp only at h <;> subst h
    · exact Or.inl (region_D_nil c)
    · refine Or.inr (Or.inl ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, false] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_00]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr (Or.inl ?_))
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_01]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr (Or.inr ?_))
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_1]
      exact append_mem_cone _ _

/-- Every region is a cone, or lies in `[01]` or `[1]`. -/
theorem region_cls2 {L : List Label} (hI : Inv L) {l : Label} (hl : l ∈ L) :
    (∃ p, region l = cone p) ∨ region l ⊆ cone [false, true] ∨ region l ⊆ cone [true] := by
  obtain ⟨r, w, c⟩ := l
  cases r with
  | A => exact Or.inl ⟨_, image_append_cone [false, false] w⟩
  | B => exact Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | C => exact Or.inr (Or.inr (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | D =>
    rcases hI.shape _ hl rfl with ⟨h, -⟩ | ⟨w', h, hadv⟩ | ⟨w', h⟩ | ⟨w', h⟩ <;>
      simp only at h <;> subst h
    · exact Or.inl ⟨[], (region_D_nil c).trans cone_nil.symm⟩
    · obtain ⟨o, ho⟩ := hadv
      refine Or.inl ⟨[false, false] ++ o, ?_⟩
      ext ξ
      constructor
      · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
        show psi .D (([false, false] ++ w') ++ₛ η) ∈ _
        rw [Stream'.append_append_stream, psi_D_00, ho, ← Stream'.append_append_stream]
        exact append_mem_cone _ _
      · rintro ⟨ζ, rfl⟩
        refine ⟨([false, false] ++ w') ++ₛ yFun (!c) ζ, ⟨_, rfl⟩, ?_⟩
        show psi .D (([false, false] ++ w') ++ₛ yFun (!c) ζ) = _
        rw [Stream'.append_append_stream, psi_D_00, ho, yFun_inv,
          ← Stream'.append_append_stream]
    · refine Or.inr (Or.inl ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_01]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_1]
      exact append_mem_cone _ _

theorem region_D_00_sub {w : Seq} {c : Bool} :
    region (.D, [false, false] ++ w, c) ⊆ cone [false, false] := by
  rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
  show psi .D (([false, false] ++ w) ++ₛ η) ∈ _
  rw [Stream'.append_append_stream, psi_D_00]
  exact append_mem_cone _ _

theorem cover_root {L : List Label} (hI : Inv L) (r : Root) (ρ : Str) :
    ∃ k, ∃ hk : k < L.length, L[k].1 = r ∧ psi r ρ ∈ region L[k] := by
  obtain ⟨l, hl, hr, hρ⟩ := hI.cover r ρ
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hl
  exact ⟨k, hk, hr, ρ, hρ, by rw [hr]⟩

/-- The A-regions cover `[00]`. -/
theorem a_cover {L : List Label} (hI : Inv L) {ξ : Str} (hξ : ξ ∈ cone [false, false]) :
    ∃ k, ∃ hk : k < L.length, L[k].1 = .A ∧ ξ ∈ region L[k] := by
  obtain ⟨ρ, rfl⟩ := hξ
  exact cover_root hI .A ρ

/-- The A-, B- and C-regions cover everything. -/
theorem abc_cover {L : List Label} (hI : Inv L) (ξ : Str) :
    ∃ k, ∃ hk : k < L.length, L[k].1 ≠ .D ∧ ξ ∈ region L[k] := by
  rcases cone_cases_pos ξ with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .A ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .B ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .C ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩

/-- A-labels come before D-labels. -/
theorem lt_of_A_D {L : List Label} (hI : Inv L) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (hA : L[i].1 = .A) (hD : L[j].1 = .D) : i < j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact h
  · rw [hA] at hD; exact absurd hD (by decide)
  · have := List.pairwise_iff_getElem.1 hI.order j i hj hi h
    rw [hA, hD] at this
    simp [rank] at this

/-! ## 6. Reading `Good` along a standard form -/

/-- The subscript of a generator. -/
def gsub : Gen → Seq
  | .x s => s
  | .y s => s

theorem good_xword_append : ∀ {Ξ : Word}, (∀ p ∈ Ξ, ∃ s, p.1 = .x s) →
    ∀ (f : Equiv.Perm Str) (Υ : Word) (L : List Label),
      Good f (Ξ ++ Υ) L ↔ Good (act Ξ * f) Υ L
  | [], _, f, Υ, L => by simp [act]
  | (g0, n) :: Ξ, hX, f, Υ, L => by
    obtain ⟨s, hs⟩ := hX (g0, n) List.mem_cons_self
    simp only at hs
    subst hs
    rw [List.cons_append]
    show Good (genP (.x s) ^ n * f) (Ξ ++ Υ) L ↔ _
    rw [good_xword_append (fun p hp => hX p (List.mem_cons_of_mem _ hp))]
    simp only [act, mul_assoc]

theorem good_yword : ∀ {g : Equiv.Perm Str} {Υ : Word} {L : List Label},
    (∀ p ∈ Υ, ∃ s, p.1 = .y s) → Good g Υ L →
    L.length = Υ.length ∧ ∀ k (hk : k < L.length), ∃ t,
      Υ[k]? = some (.y t, if L[k].2.2 then 1 else -1) ∧
      ∀ η, (act (Υ.take k) * g) (psi L[k].1 (L[k].2.1 ++ₛ η)) = t ++ₛ η
  | g, [], L, _, h => by
    have : L = [] := h
    subst this
    simp
  | g, (g0, e) :: Υ, L, hY, h => by
    obtain ⟨s, hs⟩ := hY (g0, e) List.mem_cons_self
    simp only at hs
    subst hs
    match L, h with
    | [], h => exact h.elim
    | (r, w, c) :: L', h =>
      obtain ⟨he, hc, h'⟩ := h
      obtain ⟨hlen, hk⟩ := good_yword (fun p hp => hY p (List.mem_cons_of_mem _ hp)) h'
      refine ⟨by simp [hlen], ?_⟩
      intro k hk'
      cases k with
      | zero =>
        refine ⟨s, by simp [he], fun η => ?_⟩
        simpa [act] using hc η
      | succ k =>
        obtain ⟨t, ht1, ht2⟩ := hk k (by simpa using hk')
        refine ⟨t, by simpa using ht1, fun η => ?_⟩
        rw [List.take_succ_cons, act, mul_assoc]
        exact ht2 η

/-- `y_s^m` preserves `[u]` when `s` is not a proper prefix of `u`. -/
theorem genP_y_zpow_mem_cone_iff {s u : Seq} (h : ¬ s <+: u ∨ s = u) (m : ℤ) (ξ : Str) :
    (genP (.y s) ^ m) ξ ∈ cone u ↔ ξ ∈ cone u := by
  rcases h with h | rfl
  · by_cases hξ : ξ ∈ cone s
    · have h2 := (genP_y_zpow_mem_iff s m ξ).2 hξ
      have key : ∀ ζ ∈ cone s, ζ ∈ cone u ↔ u <+: s := fun ζ hζ =>
        ⟨fun hu => (compat_of_mem_cone hu hζ).resolve_right h, fun hus => cone_mono hus hζ⟩
      rw [key _ h2, key _ hξ]
    · rw [genP_y_zpow_of_not_mem s m ξ hξ]
  · exact genP_y_zpow_mem_iff s m ξ

theorem act_mem_cone_iff {u : Seq} : ∀ {P : Word},
    (∀ p ∈ P, ∃ s, p.1 = .y s ∧ (¬ s <+: u ∨ s = u)) → ∀ ξ, act P ξ ∈ cone u ↔ ξ ∈ cone u
  | [], _, ξ => by simp [act]
  | (g0, m) :: P, hP, ξ => by
    obtain ⟨s, hs, hsu⟩ := hP (g0, m) List.mem_cons_self
    simp only at hs
    subst hs
    rw [act, Equiv.Perm.mul_apply, act_mem_cone_iff (fun p hp => hP p (List.mem_cons_of_mem _ hp)),
      genP_y_zpow_mem_cone_iff hsu]

/-- From the chart and the support fact: the image of `[w u]` is `g⁻¹[t u]`. -/
theorem image_eq_preimage {f g : Equiv.Perm Str} {r : Root} {w t : Seq}
    (hchart : ∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) (u : Seq)
    (hfg : ∀ ξ, f ξ ∈ cone (t ++ u) ↔ g ξ ∈ cone (t ++ u)) :
    psi r '' cone (w ++ u) = g ⁻¹' cone (t ++ u) := by
  ext ξ
  rw [Set.mem_preimage, ← hfg]
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    refine ⟨η, ?_⟩
    show (t ++ u) ++ₛ η = f (psi r ((w ++ u) ++ₛ η))
    rw [Stream'.append_append_stream, Stream'.append_append_stream, hchart]
  · rintro ⟨η, hη⟩
    refine ⟨(w ++ u) ++ₛ η, ⟨η, rfl⟩, f.injective ?_⟩
    rw [Stream'.append_append_stream, hchart, ← Stream'.append_append_stream]
    exact hη

/-! ## 7. The non-cone lemma for a twisted set -/

theorem cons_inj {a b : Bool} {α β : Str} (h : Stream'.cons a α = Stream'.cons b β) :
    a = b ∧ α = β :=
  ⟨by simpa using congrArg Stream'.head h, by simpa using congrArg Stream'.tail h⟩

/-- `{q (([¬c] η).y^c)}` is not a cone: (NC) of RESULT.md, after the prefix `q`. -/
theorem twist_ne_cone (q : Seq) (c : Bool) (S : Set Str)
    (hS : ∀ ξ, ξ ∈ S ↔ ∃ η, ξ = q ++ₛ yFun c (Stream'.cons (!c) η)) (p : Seq) : S ≠ cone p := by
  let z := Stream'.const false
  cases c
  · -- `[1].y⁻¹ = [01] ∪ [1]`
    refine ne_cone (q := q) (a := false) (α := Stream'.cons true (yFun true z)) (β := yFun false z)
      (γ := Stream'.cons false (Stream'.cons false z)) ?_ ?_ ?_ p
    · exact (hS _).2 ⟨Stream'.cons false z, congrArg (q ++ₛ ·) (yFun_false_10 z).symm⟩
    · exact (hS _).2 ⟨Stream'.cons true z, congrArg (q ++ₛ ·) (yFun_false_11 z).symm⟩
    · rw [hS]
      rintro ⟨η, hη⟩
      have h := append_left_cancel hη
      obtain ⟨b, η', rfl⟩ : ∃ b η', η = Stream'.cons b η' := ⟨_, _, (Stream'.eta η).symm⟩
      cases b
      · have h2 := yFun_false_10 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_false, h2] at h
        exact absurd (cons_inj (cons_inj h).2).1 (by decide)
      · have h2 := yFun_false_11 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_false, h2] at h
        exact absurd (cons_inj h).1 (by decide)
  · -- `[0].y = [0] ∪ [10]`
    refine ne_cone (q := q) (a := false) (α := yFun true z) (β := Stream'.cons false (yFun false z))
      (γ := Stream'.cons true (Stream'.cons true z)) ?_ ?_ ?_ p
    · exact (hS _).2 ⟨Stream'.cons false z, congrArg (q ++ₛ ·) (yFun_true_00 z).symm⟩
    · exact (hS _).2 ⟨Stream'.cons true z, congrArg (q ++ₛ ·) (yFun_true_01 z).symm⟩
    · rw [hS]
      rintro ⟨η, hη⟩
      have h := append_left_cancel hη
      obtain ⟨b, η', rfl⟩ : ∃ b η', η = Stream'.cons b η' := ⟨_, _, (Stream'.eta η).symm⟩
      cases b
      · have h2 := yFun_true_00 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_true, h2] at h
        exact absurd (cons_inj h).1 (by decide)
      · have h2 := yFun_true_01 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_true, h2] at h
        exact absurd (cons_inj (cons_inj h).2).1 (by decide)

theorem not_mem_cone_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : ξ ∉ cone q := fun hq =>
  (compat_of_mem_cone hp hq).elim hpq hqp

/-! ## 8. The two phases -/

/-- What the main proof extracts from a frozen standard form `Ξ Υ`: `g` is the value of `Ξ`,
`t k` the subscript of the `k`-th `y`-letter, `Occ`, `Pos`, `Neg` the occurrence predicates. -/
structure Setting (g : Equiv.Perm Str) (L : List Label) (t : ℕ → Seq)
    (Occ Pos Neg : Seq → Prop) : Prop where
  inv : Inv L
  reg0 : ∀ k (hk : k < L.length), region L[k] = g ⁻¹' cone (t k)
  reg1 : ∀ k (hk : k < L.length) (z : Bool),
    psi L[k].1 '' cone (L[k].2.1 ++ [z]) = g ⁻¹' cone (t k ++ [z])
  ord : ∀ i j, i < j → j < L.length → ¬ t i <+: t j
  occ : ∀ s, Occ s ↔ ∃ k, k < L.length ∧ t k = s
  pos : ∀ k (hk : k < L.length), L[k].2.2 = true → Pos (t k)
  neg : ∀ k (hk : k < L.length), L[k].2.2 = false → Neg (t k)
  se : ∀ s, Occ s → ¬ (∃ u, s <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: s) →
    (Pos s → Occ (s ++ [false])) ∧ (Neg s → Occ (s ++ [true]))

theorem Setting.inj {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) (h : t i = t j) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd (by rw [h]) (H.ord i j hij hj)
  · rfl
  · exact absurd (by rw [h]) (H.ord j i hij hi)

/-- Phase 1: the root of `D` is a leaf. -/
theorem phase1 {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {kD : ℕ}
    (hkD : kD < L.length) (hL : L[kD] = (.D, [], true)) : False := by
  have htD : t kD = [] := by
    have h0 := H.reg0 kD hkD
    rw [hL, region_D_nil] at h0
    apply eq_nil_of_cone_eq_univ
    ext ξ
    simp only [Set.mem_univ, iff_true]
    have : g.symm ξ ∈ g ⁻¹' cone (t kD) := h0 ▸ Set.mem_univ _
    simpa using this
  have hne : ¬ ∃ u, [] <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: [] := by
    rintro ⟨u, -, hu⟩
    obtain ⟨k, hk, hkD', hmem⟩ := abc_cover H.inv (g.symm (u ++ₛ Stream'.const false))
    rw [H.reg0 k hk] at hmem
    simp only [Set.mem_preimage, Equiv.apply_symm_apply] at hmem
    have h1 := hu (t k) (not_incompatible_of_mem_cone hmem (append_mem_cone _ _))
      ((H.occ _).2 ⟨k, hk, rfl⟩)
    have h2 : t k = t kD := by rw [htD]; exact List.prefix_nil.1 h1
    have := H.inj hk hkD h2
    subst this
    rw [hL] at hkD'
    exact hkD' rfl
  have hocc : Occ [] := (H.occ _).2 ⟨kD, hkD, htD⟩
  have hpos : Pos [] := htD ▸ H.pos kD hkD (by rw [hL])
  obtain ⟨k', hk', htk'⟩ := (H.occ _).1 ((H.se [] hocc hne).1 hpos)
  have h1 := H.reg1 kD hkD false
  rw [hL, htD] at h1
  have h2 := H.reg0 k' hk'
  rw [htk', ← h1] at h2
  simp only [List.nil_append] at h2
  -- `ψ_D([0]) = [0]` meets `[00]` and `[01]` and misses `[1]`
  have m00 : [false, false] ++ₛ yFun true (Stream'.const false) ∈ region L[k'] := by
    rw [h2]
    exact ⟨[false, false] ++ₛ Stream'.const false, ⟨[false] ++ₛ Stream'.const false, rfl⟩,
      psi_D_00 _⟩
  have m01 : [false, true] ++ₛ yFun true (Stream'.const false) ∈ region L[k'] := by
    rw [h2]
    exact ⟨[false, true] ++ₛ Stream'.const false, ⟨[true] ++ₛ Stream'.const false, rfl⟩,
      psi_D_01 _⟩
  rcases region_cls1 H.inv (List.getElem_mem hk') with h | h | h | h
  · have : psi .D ([true] ++ₛ Stream'.const false) ∈ region L[k'] := h ▸ Set.mem_univ _
    rw [h2] at this
    obtain ⟨x, hx, hxe⟩ := this
    rw [psi_D_injective hxe] at hx
    exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) hx
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m01)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m00)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m00)

/-- Phase 2: some D-leaf lies in the `00` subtree. -/
theorem phase2 {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {kD : ℕ}
    (hkD : kD < L.length) {w : Seq} {c : Bool} (hL : L[kD] = (.D, [false, false] ++ w, c))
    (hadv : ADV true w c) : False := by
  have h0 := H.reg0 kD hkD
  rw [hL] at h0
  -- the subscript of `d` is not exposed: the A-letters cover its support
  have hne : ¬ ∃ u, t kD <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: t kD := by
    rintro ⟨u, hu1, hu⟩
    have hgξ : g (g.symm (u ++ₛ Stream'.const false)) ∈ cone u := by
      rw [Equiv.apply_symm_apply]; exact append_mem_cone _ _
    have hξD : g.symm (u ++ₛ Stream'.const false) ∈ region (.D, [false, false] ++ w, c) := by
      rw [h0]; exact cone_mono hu1 hgξ
    obtain ⟨ka, hka, hkaA, hmem⟩ := a_cover H.inv (region_D_00_sub hξD)
    rw [H.reg0 ka hka] at hmem
    have h1 := hu (t ka) (not_incompatible_of_mem_cone hmem hgξ) ((H.occ _).2 ⟨ka, hka, rfl⟩)
    exact H.ord ka kD (lt_of_A_D H.inv hka hkD hkaA (by rw [hL])) hkD h1
  have hocc : Occ (t kD) := (H.occ _).2 ⟨kD, hkD, rfl⟩
  have hreq : Occ (t kD ++ [!c]) := by
    obtain ⟨hP, hN⟩ := H.se _ hocc hne
    cases c
    · exact hN (H.neg kD hkD (by rw [hL]))
    · exact hP (H.pos kD hkD (by rw [hL]))
  obtain ⟨k', hk', htk'⟩ := (H.occ _).1 hreq
  have h1 := H.reg1 kD hkD (!c)
  rw [hL] at h1
  have h2 := H.reg0 k' hk'
  rw [htk', ← h1] at h2
  -- the required letter's support is `χ_d([¬c]) = 00 o ([¬c].y^c)`
  obtain ⟨o, ho⟩ := hadv
  have hS : ∀ ξ, ξ ∈ region L[k'] ↔
      ∃ η, ξ = ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) η) := by
    intro ξ
    rw [h2]
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
      refine ⟨η, ?_⟩
      show psi .D (([false, false] ++ w ++ [!c]) ++ₛ η) = _
      rw [psi_D_00_append, ho, Stream'.append_append_stream]
      rfl
    · rintro ⟨η, rfl⟩
      refine ⟨([false, false] ++ w ++ [!c]) ++ₛ η, ⟨η, rfl⟩, ?_⟩
      rw [psi_D_00_append, ho, Stream'.append_append_stream]
      rfl
  have hmem : ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) (Stream'.const false)) ∈
      region L[k'] := (hS _).2 ⟨_, rfl⟩
  have hmem00 : ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) (Stream'.const false)) ∈
      cone [false, false] := cone_mono (List.prefix_append _ _) (append_mem_cone _ _)
  rcases region_cls2 H.inv (List.getElem_mem hk') with ⟨p, hp⟩ | h | h
  · exact twist_ne_cone _ c _ hS p hp
  · exact not_mem_cone_of_mem_cone hmem00 (by decide) (by decide) (h hmem)
  · exact not_mem_cone_of_mem_cone hmem00 (by decide) (by decide) (h hmem)

theorem setting_false {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) : False := by
  obtain ⟨l, hl, hlD, hlη⟩ := H.inv.cover .D ([false, false] ++ₛ Stream'.const false)
  obtain ⟨kD, hkD, rfl⟩ := List.mem_iff_getElem.1 hl
  have hshape := H.inv.shape _ hl hlD
  rcases hL : L[kD] with ⟨r, w, c⟩
  rw [hL] at hshape hlη hlD
  simp only at hlD hlη hshape
  subst hlD
  rcases hshape with ⟨rfl, rfl⟩ | ⟨w', rfl, hadv⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact phase1 H hkD hL
  · exact phase2 H hkD hL hadv
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide)
      (cone_mono (List.prefix_append _ _) hlη)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide)
      (cone_mono (List.prefix_append _ _) hlη)

/-! ## 9. The theorem -/

theorem not_sufficientlyExpanded_of_frozen {V : Word} (hV : Frozen V) (hS : IsStandardForm V) :
    ¬ SufficientlyExpanded V := by
  intro hSE
  obtain ⟨L, hF, hG⟩ := hV
  obtain ⟨-, ⟨Ξ, Υ, rfl, hX, hY⟩, hSF⟩ := hS
  have hG' : Good (act Ξ) Υ L := by
    have := (good_xword_append hX.2 1 Υ L).1 hG
    rwa [mul_one] at this
  obtain ⟨hlen, hst⟩ := good_yword hY.2 hG'
  -- the subscript of the `k`-th `y`-letter
  let t : ℕ → Seq := fun k => gsub ((Υ[k]?).getD (.x [], 0)).1
  have hΥ : ∀ k (hk : k < L.length), Υ[k]? = some (.y (t k), if L[k].2.2 then 1 else -1) := by
    intro k hk
    obtain ⟨t0, h1, -⟩ := hst k hk
    simp only [t, h1]
    rfl
  have hchart : ∀ k (hk : k < L.length) η,
      (act (Υ.take k) * act Ξ) (psi L[k].1 (L[k].2.1 ++ₛ η)) = t k ++ₛ η := by
    intro k hk η
    obtain ⟨t0, h1, h2⟩ := hst k hk
    have : t k = t0 := by simp only [t, h1]; rfl
    rw [this]
    exact h2 η
  -- the standard-form order: an earlier subscript is never a prefix of a later one
  have hord : ∀ i j, i < j → j < L.length → ¬ t i <+: t j := by
    intro i j hij hj hp
    have hi : i < L.length := by omega
    have ei : (Ξ ++ Υ)[Ξ.length + i]? =
        some (.y (t i), if L[i].2.2 then 1 else -1) := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hΥ i hi
    have ej : (Ξ ++ Υ)[Ξ.length + j]? =
        some (.y (t j), if L[j].2.2 then 1 else -1) := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hΥ j hj
    rw [List.getElem?_eq_some_iff] at ei ej
    obtain ⟨hi', ei⟩ := ei
    obtain ⟨hj', ej⟩ := ej
    have := hSF _ _ hi' hj' _ _ _ _ ei ej hp
    omega
  -- the support fact (g)
  have hsupp : ∀ k (hk : k < L.length) (u : Seq), (u = t k ∨ ∃ z, u = t k ++ [z]) →
      ∀ ξ, (act (Υ.take k) * act Ξ) ξ ∈ cone u ↔ act Ξ ξ ∈ cone u := by
    intro k hk u hu ξ
    rw [Equiv.Perm.mul_apply]
    apply act_mem_cone_iff
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have hik : i < k := by simp at hi; omega
    have hiL : i < L.length := by omega
    have ei := hΥ i hiL
    rw [List.getElem?_eq_some_iff] at ei
    obtain ⟨hi', ei⟩ := ei
    refine ⟨t i, by rw [List.getElem_take, ei], ?_⟩
    have hno := hord i k hik hk
    rcases hu with rfl | ⟨z, rfl⟩
    · exact Or.inl hno
    · by_cases h : t i <+: t k ++ [z]
      · rcases List.prefix_concat_iff.1 h with h | h
        · exact Or.inr h
        · exact absurd h hno
      · exact Or.inl h
  refine setting_false (g := act Ξ) (L := L) (t := t) (Occ := YOccurs (Ξ ++ Υ))
    (Pos := YOccursPos (Ξ ++ Υ)) (Neg := YOccursNeg (Ξ ++ Υ)) ⟨inv_of_forest hF, ?_, ?_, hord,
      ?_, ?_, ?_, hSE⟩
  · intro k hk
    have := image_eq_preimage (hchart k hk) [] (by simpa using hsupp k hk (t k) (Or.inl rfl))
    simp only [List.append_nil] at this
    exact this
  · intro k hk z
    exact image_eq_preimage (hchart k hk) [z] (hsupp k hk _ (Or.inr ⟨z, rfl⟩))
  · intro s
    constructor
    · rintro ⟨n, hn⟩
      rcases List.mem_append.1 hn with h | h
      · obtain ⟨s', hs'⟩ := hX.2 _ h
        simp at hs'
      · obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 h
        have hkL : k < L.length := hlen ▸ hk
        have := hΥ k hkL
        rw [List.getElem?_eq_getElem hk, hke] at this
        simp only [Option.some.injEq, Prod.mk.injEq, Gen.y.injEq] at this
        exact ⟨k, hkL, this.1.symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, List.mem_append_right _ (List.mem_of_getElem? (hΥ k hk))⟩
  · intro k hk hc
    have := hΥ k hk
    rw [hc] at this
    exact ⟨1, one_pos, List.mem_append_right _ (List.mem_of_getElem? this)⟩
  · intro k hk hc
    have := hΥ k hk
    rw [hc] at this
    exact ⟨-1, by norm_num, List.mem_append_right _ (List.mem_of_getElem? this)⟩

end LM56.PartF
