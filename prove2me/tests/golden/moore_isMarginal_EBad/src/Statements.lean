import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

namespace MooreFoelner

open Classical CannonFloydParry

theorem exists_const_forall_isFolnerSet_towerExp_le_card (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) :
    ∃ C : ℝ, 1 < C ∧ ∀ (n : ℕ) (A : Finset MooreF),
      IsFolnerSet Γ A (C ^ (-(n : ℤ))) → ThompsonAmenability.towerExp n 0 ≤ A.card := by
  sorry

theorem not_eventually_folnerFunction_le_towerExp (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) (p : ℕ) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, folnerFunction Γ n ≤ (ThompsonAmenability.towerExp p n : ℕ∞) := by
  sorry

theorem isTree_iff (T : Finset Seq) :
    IsTree T ↔ T.Nonempty ∧ (∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v) ∧
      ∀ u : Seq, (∃ t ∈ T, (u ++ [false]) <+: t) ↔ (∃ t ∈ T, (u ++ [true]) <+: t) := by
  sorry

theorem isTree_treeAct_and_isPartialAction :
    (∀ (T T' : Finset Seq) (f : MooreF), IsTree T → treeAct T f = some T' → IsTree T') ∧
      IsPartialAction treeAct := by
  sorry

theorem existsUnique_isReducedDiagram_diagramEquiv (L R : Finset Seq) (h : IsTreeDiagram L R) :
    ∃! D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 ∧ DiagramEquiv L R D.1 D.2 := by
  sorry

theorem isReducedDiagram_iff (S T : Finset Seq) (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔
      ¬ ∃ (i : ℕ) (hi : i + 1 < (sorted S).length) (hi' : i + 1 < (sorted T).length),
        ((sorted S).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted T).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted S).get ⟨i + 1, hi⟩).getLast? = some true ∧
        ((sorted T).get ⟨i + 1, hi'⟩).getLast? = some true := by
  sorry

theorem bijOn_Lf_Rf_and_diagramMul :
    (∀ D D' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram (diagramMul D D').1 (diagramMul D D').2 ∧
          ∀ x, diagramMap (diagramMul D D').1 (diagramMul D D').2 x =
            diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x)) ∧
    (∀ D D' D'' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram D''.1 D''.2 →
        diagramMul (diagramMul D D') D'' = diagramMul D (diagramMul D' D'')) ∧
    IsReducedDiagram trivialTree trivialTree ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        diagramMul (trivialTree, trivialTree) D = D ∧ diagramMul D (trivialTree, trivialTree) = D) ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        IsReducedDiagram D.2 D.1 ∧ diagramMul D (D.2, D.1) = (trivialTree, trivialTree) ∧
          diagramMul (D.2, D.1) D = (trivialTree, trivialTree)) ∧
    Set.BijOn (fun f : MooreF => (Lf (toMap f), Rf (toMap f))) Set.univ
        {D : Finset Seq × Finset Seq | IsReducedDiagram D.1 D.2} ∧
      (∀ f : MooreF, Describes (Lf (toMap f)) (Rf (toMap f)) (toMap f)) ∧
      ∀ f g : MooreF, (Lf (toMap (f * g)), Rf (toMap (f * g))) =
        diagramMul (Lf (toMap f), Rf (toMap f)) (Lf (toMap g), Rf (toMap g)) := by
  sorry

theorem closure_x0_x1_eq_top : Subgroup.closure ({x0, x1} : Set MooreF) = ⊤ := by
  sorry

theorem isReducedDiagram_treeAct (f g : MooreF) (S T T' : Finset Seq)
    (h : IsReducedDiagram S T) (hg : Describes S T (toMap g)) (hf : ActsProperlyOn f T)
    (hT' : treeAct T f = some T') :
    IsReducedDiagram S T' ∧ Describes S T' (toMap (g * f)) := by
  sorry

theorem exists_const_isFolnerSet_of_isFolnerSet (Γ' : Finset MooreF)
    (hgen : Subgroup.closure (Γ' : Set MooreF) = ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset MooreF) (ε : ℝ), IsFolnerSet Γ' A ε → IsFolnerSet gens A (K * ε) := by
  sorry

theorem isWeightedFolner_mapDomain {G S T : Type*} [Group G] (actS : S → G → Option S)
    (actT : T → G → Option T) (hS : IsPartialAction actS) (hT : IsPartialAction actT)
    (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤)
    (μ : S →₀ ℝ) (ε : ℝ) (hμ : IsWeightedFolner actS Γ μ ε) (h : S → T)
    (hh : ∀ γ ∈ Γ, ∀ s, 0 < μ s + valAt actS μ s γ →
      ∃ y, actS s γ = some y ∧ actT (h s) γ = some (h y)) :
    IsWeightedFolner actT Γ (μ.mapDomain h) ε := by
  sorry

theorem finsum_abs_valAt_sub_lt {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (g : G) (hg : g ≠ 1) :
    ∑ᶠ s, |valAt act μ s g - μ s| < 2 * ε * wordLength Γ g * mass μ Set.univ := by
  sorry

theorem isMarginal_union_subset_image {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) :
    (∀ s : Finset (Set S), (∀ E ∈ s, IsMarginal act E) → IsMarginal act (⋃₀ (s : Set (Set S)))) ∧
    (∀ E E' : Set S, E' ⊆ E → IsMarginal act E → IsMarginal act E') ∧
    (∀ (E : Set S) (g : G), Marginalizes act g⁻¹ (E \ image act E g) E) ∧
    (∀ (E : Set S) (g : G), IsMarginal act E → IsMarginal act (image act E g)) := by
  sorry

theorem mass_lt_of_marginalizes {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (E : Set S) (g : G) (hg : g ≠ 1)
    (hE : Marginalizes act g E (↑μ.support)ᶜ) :
    mass μ E < wordLength Γ g * ε * mass μ Set.univ := by
  sorry

theorem exists_const_mass_lt_of_isMarginal {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S) (hE : IsMarginal act E) :
    ∃ C : ℝ, ∀ (ε : ℝ), 0 < ε → ∀ μ : S →₀ ℝ, IsWeightedFolner act Γ μ ε →
      mass μ E < C * ε * mass μ Set.univ := by
  sorry

theorem isWeightedFolner_of_le {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε δ : ℝ) (μ ν : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (hν : ∀ s, 0 ≤ ν s) (hle : ∀ s, ν s ≤ μ s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hmass : mass ν Set.univ ≥ (1 - δ) * mass μ Set.univ) :
    IsWeightedFolner act Γ ν ((ε + 2 * Γ.card * δ) / (1 - δ)) := by
  sorry

theorem exists_const_isWeightedFolner_restrict_compl {G S : Type*} [Group G]
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S)
    (hE : IsMarginal act E) (hne : (Eᶜ).Nonempty) :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : S →₀ ℝ), IsWeightedFolner act Γ μ ε → C * ε ≤ 1 →
      IsWeightedFolner act Γ (restrict μ Eᶜ) (C * ε) ∧ (restrict μ Eᶜ).support.Nonempty := by
  sorry

theorem exists_isConnectedComponent_isWeightedFolner {G S : Type*} [Group G]
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε)
    (μ : S →₀ ℝ) (hμ : IsWeightedFolner act Γ μ ε) :
    ∃ A : Set S, IsConnectedComponent act Γ A ↑μ.support ∧
      IsWeightedFolner act Γ (restrict μ A) ε := by
  sorry

theorem exists_isConnected_isFolnerSet_one_mem {G : Type*} [Group G] (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ)
    (A : Finset G) (hA : IsFolnerSet Γ A ε) :
    ∃ B : Finset G, IsFolnerSet Γ B ε ∧ IsConnected rightMul Γ ↑B ∧ (1 : G) ∈ B ∧
      B.card ≤ A.card := by
  sorry

theorem isMarginal_not_extended_Rf (u : Seq) :
    IsMarginal (rightMul : MooreF → MooreF → Option MooreF)
      {f | ¬ ∃ r ∈ Rf (toMap f), u <+: r} := by
  sorry

theorem exists_const_isWeightedFolner_trees :
    ∃ C : ℝ, ∀ (ε : ℝ) (A : Finset MooreF), IsFolnerSet gens A ε →
      ∃ μ : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens μ (C * ε) ∧
        ↑μ.support ⊆ {T | ∃ f ∈ A, T = Rf (toMap f)} := by
  sorry

theorem exists_max_deltaConditions (T : Finset Seq) (hT : IsTree T)
    (h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) :
    ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U := by
  sorry

theorem two_zpow_card_delta_sub_two_lt_card (T : Finset Seq) (hT : IsTree T) :
    (2 : ℝ) ^ (((delta T).card : ℤ) - 2) < T.card := by
  sorry

theorem treeAct_delta (g : MooreF) (T : Finset Seq) (hT : IsTree T)
    (hg : ActsProperlyOn g (delta T)) :
    ∃ T', treeAct T g = some T' ∧ IsTree T' ∧ treeAct (delta T) g = some (delta T') := by
  sorry

theorem isMarginal_EBad : IsMarginal treeAct EBad := by
  sorry

theorem treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes :
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TPlus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TPlus T')) ∧
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TMinus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TMinus T')) ∧
    ∀ A : Set (Finset Seq), A ⊆ {T | IsTree T} \ EStar → IsConnected treeAct gens A →
      (∀ T ∈ A, TwoTimes T) ∨ ∀ T ∈ A, HalfTimes T := by
  sorry

theorem isMarginal_EStar : IsMarginal treeAct EStar := by
  sorry

theorem isMarginal_not_actsProperlyOn_delta :
    IsMarginal treeAct {T | IsTree T ∧ ¬ ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  sorry

theorem exists_const_isWeightedFolner_delta :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : Finset Seq →₀ ℝ), (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → C * ε ≤ 1 →
      ∃ ν : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens ν (C * ε) ∧
        ↑ν.support ⊆ {U | ∃ T, 0 < μ T ∧ U = delta T ∧ delta T ≠ trivialTree ∧
          ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  sorry

theorem exists_const_isFolnerSet_exists_towerExp_le_card_Rf :
    ∃ K : ℝ, 1 < K ∧ ∀ (n : ℕ) (A : Finset MooreF), IsFolnerSet gens A (K ^ (-(n : ℤ))) →
      ∃ f ∈ A, ThompsonAmenability.towerExp n 0 ≤ (Lf (toMap f)).card ∧
        ThompsonAmenability.towerExp n 0 ≤ (Rf (toMap f)).card := by
  sorry

theorem card_Rf_sub_two_le_three_mul_wordLength (f : MooreF) :
    ((Rf (toMap f)).card : ℝ) - 2 ≤ 3 * wordLength gens f := by
  sorry

end MooreFoelner
