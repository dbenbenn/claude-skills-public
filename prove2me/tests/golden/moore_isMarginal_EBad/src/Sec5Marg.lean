import Solutions.Golden.moore_isMarginal_EBad.Statements

/-!
# Moore 2013, §5 (pp. 14–18): the marginal sets of Lemmas 5.7, 5.10, 5.12, Lemma 5.9 and Lemma 5.13

Development for the prover group `Sec5Marg`.

* The reduced tree diagrams of `x₀`, `x₁`, `a`, `b`, `c`, `d` are identified with the diagrams
  that define them (via milestones #4 and #5 and an explicit check that the dyadic intervals of the
  domain tree tile `[0,1]`), which gives the action of each element on finite sequences.
* Lemma 5.12 uses, in place of Moore's `g = (U, R)` (whose diagram is not reduced: its last two
  leaves form a common caret), the element `elemG` with reduced diagram
  `U' = {length-4 sequences} \ {1110, 1111} ∪ {111}` → right comb with 15 leaves; trees with the
  leaf `111` are excluded through the sets where `x₁⁻¹` and `x₁⁻²` are undefined. `E**` is
  taken with `i ≤ 13` (Moore: `i ≤ 16`), which is what the 14 interior leaves of `U` need.
* Lemma 5.9, last clause: trees with `|T/01| = 0` lie in `ℰ` but satisfy `(2×)`, so `ℰ ⊄ ℰ*`;
  the proof checks that one generator step from a `(−)` tree never reaches such a tree.
* Moore's "`x₀` marginalizes `E₅` off `E₄ ∪ E`" is used in the form "`x₀` marginalizes `E₅ \ E₄`
  off `E₄ ∪ E`" (Definition 3.6 starts at `i = 0`); likewise for `E₇`.
-/

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Sorting -/

theorem mergeSort_congr {α : Type*} {r s : α → α → Bool} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b = s a b) →
      l.mergeSort r = l.mergeSort s
  | [], _, _ => by simp
  | [x], _, _ => by simp
  | a :: b :: l, hnd, h => by
    simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
    have h1 := hnd.sublist (List.take_sublist (((a :: b :: l).length + 1) / 2) (a :: b :: l))
    have h2 := hnd.sublist (List.drop_sublist (((a :: b :: l).length + 1) / 2) (a :: b :: l))
    rw [mergeSort_congr h1 (fun x hx y hy hxy => h x (List.mem_of_mem_take hx) y
      (List.mem_of_mem_take hy) hxy)]
    rw [mergeSort_congr h2 (fun x hx y hy hxy => h x (List.mem_of_mem_drop hx) y
      (List.mem_of_mem_drop hy) hxy)]
    have key : ∀ (xs ys : List α), (∀ x ∈ xs, ∀ y ∈ ys, r x y = s x y) →
        xs.merge ys r = xs.merge ys s := by
      intro xs ys hxy
      have := List.map_merge (f := id) (r := r) (s := s) (l := xs) (l' := ys) hxy
      simpa using this
    apply key
    intro x hx y hy
    rw [List.mem_mergeSort] at hx hy
    apply h x (List.mem_of_mem_take hx) y (List.mem_of_mem_drop hy)
    rintro rfl
    have := List.disjoint_take_drop hnd (le_refl (((a :: b :: l).length + 1) / 2))
    exact this hx hy
  termination_by l => l.length

theorem lexLt_iff (u v : Seq) : LexLt u v ↔ u < v := (List.lt_iff_lex_lt u v).symm

theorem lexLt_irrefl (u : Seq) : ¬ LexLt u u := by rw [lexLt_iff]; exact lt_irrefl u
theorem lexLt_trans {u v w : Seq} : LexLt u v → LexLt v w → LexLt u w := by
  simp only [lexLt_iff]; exact lt_trans
theorem lexLt_asymm {u v : Seq} : LexLt u v → ¬ LexLt v u := by
  simp only [lexLt_iff]; exact fun h h' => lt_asymm h h'
theorem lexLt_trichotomous (u v : Seq) : LexLt u v ∨ u = v ∨ LexLt v u := by
  simp only [lexLt_iff]; exact lt_trichotomy u v

theorem sorted_eq (T : Finset Seq) (l : List Seq) (hl : l.Pairwise LexLt) (hT : l.toFinset = T) :
    sorted T = l := by
  have hnd : T.toList.Nodup := Finset.nodup_toList T
  unfold sorted
  rw [mergeSort_congr (s := fun u v => decide (LexLt u v ∨ u = v)) hnd (by
    intro a _ b _ hab
    simp [hab])]
  have hp := List.pairwise_mergeSort (le := fun u v => decide (LexLt u v ∨ u = v))
    (by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      rcases hab with hab | rfl
      · rcases hbc with hbc | rfl
        · exact Or.inl (lexLt_trans hab hbc)
        · exact Or.inl hab
      · exact hbc)
    (by
      intro a b
      rcases lexLt_trichotomous a b with h | h | h <;> simp [h]) T.toList
  have hperm := List.mergeSort_perm T.toList (fun u v => decide (LexLt u v ∨ u = v))
  have hnd2 := hperm.nodup_iff.mpr hnd
  have hp2 : (T.toList.mergeSort (fun u v => decide (LexLt u v ∨ u = v))).Pairwise LexLt := by
    have := hp.and hnd2
    refine this.imp ?_
    rintro a b ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 h2
  apply List.Perm.eq_of_pairwise (le := LexLt) _ hp2 hl
  · refine hperm.trans ?_
    rw [← hT]
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) _ (by simp)
    exact hl.imp (fun h h' => by subst h'; exact lexLt_irrefl _ h)
  · intro a b _ _ h1 h2
    exact absurd h2 (lexLt_asymm h1)

theorem length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  unfold sorted; simp

theorem mem_sorted (T : Finset Seq) (u : Seq) : u ∈ sorted T ↔ u ∈ T := by
  unfold sorted; simp

/-! ### Initial parts and trees -/

/-- The extension of a finite sequence by zeros. -/
def ext0 (u : Seq) : ℕ → Bool := fun n => u.getD n false

theorem isInitialPart_ext0_of_prefix {u v : Seq} (h : u <+: v) : IsInitialPart u (ext0 v) := by
  intro i hi
  obtain ⟨w, rfl⟩ := h
  simp [ext0, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem isInitialPart_ext0 (u : Seq) : IsInitialPart u (ext0 u) :=
  isInitialPart_ext0_of_prefix (List.prefix_refl u)

theorem prefix_of_isInitialPart {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) (hle : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp only [List.getElem_take]
    have := hu n h1
    have h' := hv n (by omega)
    simp only [List.get_eq_getElem] at this h'
    rw [this, h']

theorem isInitialPart_of_prefix {u v : Seq} {x : ℕ → Bool} (h : u <+: v)
    (hv : IsInitialPart v x) : IsInitialPart u x := by
  intro i hi
  obtain ⟨w, rfl⟩ := h
  have := hv i (by simp; omega)
  simp only [List.get_eq_getElem, List.getElem_append_left hi] at this ⊢
  exact this

theorem IsTree.exists_mem {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨h1, h2⟩, _⟩ := hT x
  exact ⟨t, h1, h2⟩

theorem IsTree.eq_of_prefix {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T)
    (hv : v ∈ T) (h : u <+: v) : u = v := by
  obtain ⟨t, _, ht⟩ := hT (ext0 v)
  have h1 := ht u ⟨hu, isInitialPart_ext0_of_prefix h⟩
  have h2 := ht v ⟨hv, isInitialPart_ext0 v⟩
  rw [h1, h2]

/-- A list of sequences no two of which are comparable under `<+:`. -/
def Antichain (l : List Seq) : Prop := ∀ u ∈ l, ∀ v ∈ l, u <+: v → u = v

/-- If every leaf of the tree `T` extends an element of the antichain `l`, then every element of
`l` is extended by a leaf of `T`. -/
theorem IsTree.exists_extends {T : Finset Seq} (hT : IsTree T) {l : List Seq} (hl : Antichain l)
    (hdom : ∀ t ∈ T, ∃ u ∈ l, u <+: t) {w : Seq} (hw : w ∈ l) : ∃ t ∈ T, w <+: t := by
  obtain ⟨t, htT, ht⟩ := IsTree.exists_mem hT (ext0 w)
  obtain ⟨u, hul, hut⟩ := hdom t htT
  have hu := isInitialPart_of_prefix hut ht
  have hw' := isInitialPart_ext0 w
  rcases le_total u.length w.length with hle | hle
  · have := hl u hul w hw (prefix_of_isInitialPart hu hw' hle)
    subst this; exact ⟨t, htT, hut⟩
  · have := hl w hw u hul (prefix_of_isInitialPart hw' hu hle)
    subst this; exact ⟨t, htT, hut⟩

/-! ### Building concrete trees -/

/-- `l` lists the leaves of a tree in increasing lexicographic order. -/
def Good (l : List Seq) : Prop := l.Pairwise LexLt ∧ IsTree l.toFinset

/-- The tree with left subtree `l₁` and right subtree `l₂`. -/
def joinL (l₁ l₂ : List Seq) : List Seq := l₁.map (false :: ·) ++ l₂.map (true :: ·)

theorem good_leaf : Good [[]] := by
  refine ⟨by simp, ?_⟩
  intro x
  refine ⟨[], ⟨by simp, fun i hi => by simp at hi⟩, ?_⟩
  intro t ⟨ht, _⟩
  simpa using ht

theorem lexLt_cons_cons (a : Bool) (u v : Seq) : LexLt (a :: u) (a :: v) ↔ LexLt u v := by
  unfold LexLt
  constructor
  · intro h
    cases h with
    | cons h => exact h
    | rel h => exact absurd h (lt_irrefl a)
  · intro h; exact List.Lex.cons h

theorem isInitialPart_cons (b : Bool) (u : Seq) (x : ℕ → Bool) :
    IsInitialPart (b :: u) x ↔ x 0 = b ∧ IsInitialPart u (fun n => x (n+1)) := by
  constructor
  · intro h
    refine ⟨(h 0 (by simp)).symm, fun i hi => ?_⟩
    have := h (i+1) (by simp; omega)
    simpa using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0.symm
    | succ i =>
      have := h i (by simp at hi; omega)
      simpa using this

theorem good_join {l₁ l₂ : List Seq} (h₁ : Good l₁) (h₂ : Good l₂) : Good (joinL l₁ l₂) := by
  refine ⟨?_, ?_⟩
  · unfold joinL
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact h₁.1.imp (fun h => (lexLt_cons_cons _ _ _).mpr h)
    · rw [List.pairwise_map]
      exact h₂.1.imp (fun h => (lexLt_cons_cons _ _ _).mpr h)
    · intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨u, _, rfl⟩ := ha
      obtain ⟨v, _, rfl⟩ := hb
      exact List.Lex.rel (by decide)
  · intro x
    have hmem : ∀ t, t ∈ (joinL l₁ l₂).toFinset ↔
        (∃ u ∈ l₁, t = false :: u) ∨ (∃ u ∈ l₂, t = true :: u) := by
      intro t; simp [joinL, eq_comm]
    cases hx : x 0
    · obtain ⟨t1, ⟨ht1, hi1⟩, hu1⟩ := h₁.2 (fun n => x (n+1))
      refine ⟨false :: t1, ⟨(hmem _).mpr (Or.inl ⟨t1, by simpa using ht1, rfl⟩),
        (isInitialPart_cons _ _ _).mpr ⟨hx, hi1⟩⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      rcases (hmem t).mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [isInitialPart_cons] at hit
        rw [hu1 u ⟨by simpa using hu, hit.2⟩]
      · rw [isInitialPart_cons, hx] at hit
        exact absurd hit.1 (by decide)
    · obtain ⟨t1, ⟨ht1, hi1⟩, hu1⟩ := h₂.2 (fun n => x (n+1))
      refine ⟨true :: t1, ⟨(hmem _).mpr (Or.inr ⟨t1, by simpa using ht1, rfl⟩),
        (isInitialPart_cons _ _ _).mpr ⟨hx, hi1⟩⟩, ?_⟩
      rintro t ⟨ht, hit⟩
      rcases (hmem t).mp ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [isInitialPart_cons, hx] at hit
        exact absurd hit.1 (by decide)
      · rw [isInitialPart_cons] at hit
        rw [hu1 u ⟨by simpa using hu, hit.2⟩]

theorem Good.nodup {l : List Seq} (h : Good l) : l.Nodup :=
  h.1.imp (fun h h' => by subst h'; exact lexLt_irrefl _ h)

theorem Good.antichain {l : List Seq} (h : Good l) : Antichain l := by
  intro u hu v hv huv
  exact IsTree.eq_of_prefix h.2 (by simpa using hu) (by simpa using hv) huv

theorem Good.sorted {l : List Seq} (h : Good l) : MooreFoelner.sorted l.toFinset = l :=
  sorted_eq _ l h.1 rfl

/-! ### Dyadic values and coverage -/

theorem seqVal_nil : seqVal [] = 0 := by simp [seqVal]

theorem seqVal_cons (b : Bool) (u : Seq) :
    seqVal (b :: u) = (if b then 1/2 else 0) + seqVal u / 2 := by
  unfold seqVal
  erw [Fin.sum_univ_succ (n := u.length)]
  simp only [List.length_cons, Fin.val_zero, zero_add, pow_one, List.get_eq_getElem,
    Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

/-- The dyadic intervals of the elements of `l`, in order, tile `[a, 1]`. -/
def Covers : List Seq → ℝ → Prop
  | [], a => a = 1
  | u :: l, a => seqVal u = a ∧ Covers l (a + (1/2 : ℝ) ^ u.length)

theorem covers_exists : ∀ (l : List Seq) (a x : ℝ), Covers l a → a ≤ x → x ≤ 1 → l ≠ [] →
    ∃ i, ∃ h : i < l.length, seqVal l[i] ≤ x ∧ x ≤ seqVal l[i] + (1/2 : ℝ) ^ l[i].length
  | [], _, _, _, _, _, h => absurd rfl h
  | u :: l, a, x, hc, hax, hx1, _ => by
    obtain ⟨hu, hl⟩ := hc
    by_cases hx : x ≤ a + (1/2 : ℝ) ^ u.length
    · refine ⟨0, by simp, ?_, ?_⟩
      · simp only [List.getElem_cons_zero]; rw [hu]; exact hax
      · simp only [List.getElem_cons_zero]; rw [hu]; exact hx
    · push Not at hx
      cases l with
      | nil => simp only [Covers] at hl; linarith
      | cons v l =>
        obtain ⟨i, hi, h1, h2⟩ := covers_exists (v :: l) _ x hl hx.le hx1 (by simp)
        exact ⟨i + 1, by simp at hi ⊢; omega, by simpa using h1, by simpa using h2⟩

theorem describes_unique {L R : Finset Seq} (hcov : Covers (sorted L) 0) (hne : sorted L ≠ [])
    {f g : UI ≃o UI} (hf : Describes L R f) (hg : Describes L R g) : f = g := by
  apply DFunLike.ext f g
  intro x
  apply Subtype.ext
  obtain ⟨i, hi, h1, h2⟩ := covers_exists (sorted L) 0 x hcov x.2.1 x.2.2 hne
  have hR : i < (sorted R).length := by
    rw [length_sorted, ← hf.1.2.2, ← length_sorted]; exact hi
  rw [hf.2 i hi hR x h1 h2, hg.2 i hi hR x h1 h2]

/-! ### Reduced diagrams -/

/-- No common caret, as a Boolean check on the sorted leaf lists. -/
def noCaret : List Seq → List Seq → Bool
  | a :: a' :: l, b :: b' :: l' =>
    !(a.getLast? == some false && b.getLast? == some false && a'.getLast? == some true &&
      b'.getLast? == some true) && noCaret (a' :: l) (b' :: l')
  | _, _ => true

theorem noCaret_spec : ∀ (l l' : List Seq), noCaret l l' = true →
    ¬ ∃ (i : ℕ) (hi : i + 1 < l.length) (hi' : i + 1 < l'.length),
      l[i].getLast? = some false ∧ l'[i].getLast? = some false ∧
      l[i+1].getLast? = some true ∧ l'[i+1].getLast? = some true
  | a :: a' :: l, b :: b' :: l', h => by
    simp only [noCaret, Bool.and_eq_true, Bool.not_eq_true'] at h
    rintro ⟨i, hi, hi', h1, h2, h3, h4⟩
    cases i with
    | zero =>
      simp at h1 h2 h3 h4
      simp [h1, h2, h3, h4] at h
    | succ i =>
      apply noCaret_spec (a' :: l) (b' :: l') h.2
      exact ⟨i, by simp at hi ⊢; omega, by simp at hi' ⊢; omega, by simpa using h1,
        by simpa using h2, by simpa using h3, by simpa using h4⟩
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | _ :: _ :: _, [], _ => by simp
  | _ :: _ :: _, [_], _ => by simp

theorem isReduced_of {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) :
    IsReducedDiagram lL.toFinset lR.toFinset := by
  have htd : IsTreeDiagram lL.toFinset lR.toFinset := by
    refine ⟨hL.2, hR.2, ?_⟩
    rw [List.toFinset_card_of_nodup hL.nodup, List.toFinset_card_of_nodup hR.nodup, hlen]
  rw [isReducedDiagram_iff _ _ htd]
  simp only [List.get_eq_getElem]
  simp only [hL.sorted, hR.sorted]
  exact noCaret_spec _ _ hnc

theorem LR_ofDiagram {L R : Finset Seq} (hred : IsReducedDiagram L R)
    (hcov : Covers (sorted L) 0) (hne : sorted L ≠ []) :
    Lf (toMap (ofDiagram L R)) = L ∧ Rf (toMap (ofDiagram L R)) = R := by
  obtain ⟨-, -, -, -, -, hbij, hdesc, -⟩ := bijOn_Lf_Rf_and_diagramMul
  obtain ⟨g, -, hg⟩ := hbij.surjOn (show (L, R) ∈ {D : Finset Seq × Finset Seq |
    IsReducedDiagram D.1 D.2} from hred)
  simp only [Prod.mk.injEq] at hg
  have hdg : Describes L R (toMap g) := by
    have := hdesc g; rw [hg.1, hg.2] at this; exact this
  have hex : ∃ f : F, Describes L R (f : UI ≃o UI) := ⟨MulOpposite.unop g, hdg⟩
  have hspec := Classical.epsilon_spec hex
  have : toMap (ofDiagram L R) = toMap g := describes_unique hcov hne hspec hdg
  rw [this]; exact hg

/-! ### The action of a diagram on finite sequences -/

/-- The body of `diagramAct`, as a function of the two sorted lists. -/
noncomputable def dAct (S T : List Seq) (t : Seq) : Option Seq :=
  match (List.finRange S.length).find? (fun i => decide (S.get i <+: t)) with
  | some i => (T[i.1]?).map (· ++ t.drop (S.get i).length)
  | none => none

theorem diagramAct_eq_dAct (L R : Finset Seq) (t : Seq) :
    diagramAct L R t = dAct (sorted L) (sorted R) t := rfl

theorem dAct_spec (S T : List Seq) (hlen : S.length = T.length) (hanti : Antichain S)
    (hnd : S.Nodup) (t t' : Seq) :
    dAct S T t = some t' ↔ ∃ p ∈ S.zip T, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s := by
  unfold dAct
  constructor
  · intro h
    split at h
    · rename_i i hi
      have hpi := List.find?_some hi
      simp only [decide_eq_true_eq, List.get_eq_getElem] at hpi
      have hiT : i.1 < T.length := hlen ▸ i.2
      simp only [List.getElem?_eq_getElem hiT, Option.map_some, Option.some.injEq] at h
      refine ⟨(S[i.1], T[i.1]'hiT), ?_, t.drop (S[i.1]).length, ?_, ?_⟩
      · rw [List.mem_iff_getElem]
        exact ⟨i.1, by simp only [List.length_zip, lt_min_iff]; exact ⟨i.2, hiT⟩, by simp⟩
      · obtain ⟨w, hw⟩ := hpi
        subst hw; simp
      · rw [← h]; simp
    · simp at h
  · rintro ⟨p, hp, s, rfl, rfl⟩
    rw [List.mem_iff_getElem] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    simp only [List.length_zip, lt_min_iff] at hi
    simp only [List.getElem_zip]
    have hex : ∃ j ∈ List.finRange S.length, decide (S.get j <+: S[i] ++ s) = true :=
      ⟨⟨i, hi.1⟩, by simp, by simp⟩
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
    rw [hj]
    have hpj := List.find?_some hj
    simp only [decide_eq_true_eq, List.get_eq_getElem] at hpj
    have hij : S[j.1] = S[i] := by
      rcases List.prefix_or_prefix_of_prefix hpj (List.prefix_append S[i] s) with h | h
      · exact hanti _ (List.getElem_mem _) _ (List.getElem_mem _) h
      · exact (hanti _ (List.getElem_mem _) _ (List.getElem_mem _) h).symm
    have hji : j.1 = i := (List.Nodup.getElem_inj_iff hnd).mp hij
    have hiT : j.1 < T.length := hlen ▸ j.2
    simp only [List.get_eq_getElem, List.getElem?_eq_getElem hiT, Option.map_some]
    simp only [List.drop_left, hji]

theorem seqAct_ofDiagram {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) (hcov : Covers lL 0)
    (hne : lL ≠ []) (t t' : Seq) :
    seqAct t (ofDiagram lL.toFinset lR.toFinset) = some t' ↔
      ∃ p ∈ lL.zip lR, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s := by
  have hred := isReduced_of hL hR hlen hnc
  obtain ⟨h1, h2⟩ := LR_ofDiagram hred (by rw [hL.sorted]; exact hcov) (by rw [hL.sorted]; exact hne)
  unfold seqAct
  rw [h1, h2, diagramAct_eq_dAct, hL.sorted, hR.sorted]
  exact dAct_spec lL lR hlen hL.antichain hL.nodup t t'

/-! ### The action on finite sets of sequences -/

theorem treeAct_some_iff (T T' : Finset Seq) (f : MooreF) :
    treeAct T f = some T' ↔ (∀ t ∈ T, ∃ t', seqAct t f = some t') ∧
      ∀ t', t' ∈ T' ↔ ∃ t ∈ T, seqAct t f = some t' := by
  unfold treeAct
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨fun t ht => Option.isSome_iff_exists.mp (h t ht), fun t' => ?_⟩
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by simp [h']⟩
    · rintro ⟨-, h2⟩
      ext t'
      rw [h2]
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp⟩
      · rintro ⟨t, ht, h'⟩; exact ⟨t, ht, by simp [h']⟩
  · simp only [false_iff, not_and]
    intro h1
    exact absurd (fun t ht => by obtain ⟨t', ht'⟩ := h1 t ht; simp [ht']) h

theorem treeAct_none_iff (T : Finset Seq) (f : MooreF) :
    treeAct T f = none ↔ ∃ t ∈ T, seqAct t f = none := by
  unfold treeAct
  split_ifs with h
  · simp only [false_iff, not_exists, not_and]
    intro t ht h'
    have := h t ht; rw [h'] at this; simp at this
  · simp only [true_iff]
    push Not at h
    obtain ⟨t, ht, h'⟩ := h
    exact ⟨t, ht, by simpa using h'⟩

theorem treeAct_isSome_iff (T : Finset Seq) (f : MooreF) :
    (∃ T', treeAct T f = some T') ↔ ∀ t ∈ T, ∃ t', seqAct t f = some t' := by
  constructor
  · rintro ⟨T', h⟩; exact ((treeAct_some_iff T T' f).mp h).1
  · intro h
    cases h' : treeAct T f with
    | some T' => exact ⟨T', rfl⟩
    | none =>
      obtain ⟨t, ht, h''⟩ := (treeAct_none_iff T f).mp h'
      obtain ⟨t', ht'⟩ := h t ht
      rw [h''] at ht'; exact absurd ht' (by simp)

theorem seqAct_iff_treeAct (t t' : Seq) (f : MooreF) :
    seqAct t f = some t' ↔ treeAct {t} f = some {t'} := by
  rw [treeAct_some_iff]
  simp only [Finset.mem_singleton, forall_eq, exists_eq_left]
  constructor
  · intro h; exact ⟨⟨t', h⟩, fun y => by rw [h]; simp [eq_comm]⟩
  · rintro ⟨-, h⟩; exact (h t').mp rfl

theorem hPA : IsPartialAction treeAct := isTree_treeAct_and_isPartialAction.2

theorem isTree_of_treeAct {T T' : Finset Seq} {f : MooreF} (hT : IsTree T)
    (h : treeAct T f = some T') : IsTree T' :=
  isTree_treeAct_and_isPartialAction.1 T T' f hT h

theorem seqAct_inv (t t' : Seq) (f : MooreF) :
    seqAct t f = some t' ↔ seqAct t' f⁻¹ = some t := by
  rw [seqAct_iff_treeAct, seqAct_iff_treeAct]
  exact hPA.inv f _ _

theorem seqAct_mul {t t' t'' : Seq} {f g : MooreF} (h1 : seqAct t f = some t')
    (h2 : seqAct t' g = some t'') : seqAct t (f * g) = some t'' := by
  rw [seqAct_iff_treeAct] at *
  exact hPA.mul f g _ _ _ h1 h2

theorem seqAct_inj {t₁ t₂ t' : Seq} {f : MooreF} (h1 : seqAct t₁ f = some t')
    (h2 : seqAct t₂ f = some t') : t₁ = t₂ := by
  rw [seqAct_inv] at h1 h2
  rw [h1] at h2; exact Option.some.inj h2

theorem card_quot (T : Finset Seq) (u : Seq) :
    (quot T u).card = (T.filter (u <+: ·)).card := by
  unfold quot
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  obtain ⟨a', rfl⟩ := ha.2
  obtain ⟨b', rfl⟩ := hb.2
  simp only [List.drop_left] at hab
  rw [hab]

theorem card_filter_treeAct {T T' : Finset Seq} {f : MooreF} (h : treeAct T f = some T')
    (P Q : Seq → Prop) (hPQ : ∀ t ∈ T, ∀ t', seqAct t f = some t' → (P t ↔ Q t')) :
    (T'.filter Q).card = (T.filter P).card := by
  obtain ⟨hdef, hmem⟩ := (treeAct_some_iff T T' f).mp h
  have hφ : ∀ t ∈ T, seqAct t f = some ((seqAct t f).getD []) := by
    intro t ht
    obtain ⟨t', ht'⟩ := hdef t ht
    rw [ht']; rfl
  have : T'.filter Q = (T.filter P).image (fun t => (seqAct t f).getD []) := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨ht', hq⟩
      obtain ⟨t, ht, hs⟩ := (hmem t').mp ht'
      refine ⟨t, ⟨ht, (hPQ t ht t' hs).mpr hq⟩, ?_⟩
      rw [hs]; rfl
    · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
      exact ⟨(hmem _).mpr ⟨t, ht, hφ t ht⟩, (hPQ t ht _ (hφ t ht)).mp hp⟩
  rw [this]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
  have h1 := hφ a ha.1
  have h2 := hφ b hb.1
  simp only at hab
  rw [hab] at h1
  exact seqAct_inj h1 h2

theorem card_quot_treeAct {T T' : Finset Seq} {f : MooreF} (h : treeAct T f = some T')
    (u v : Seq) (huv : ∀ t ∈ T, ∀ t', seqAct t f = some t' → (u <+: t ↔ v <+: t')) :
    (quot T' v).card = (quot T u).card := by
  rw [card_quot, card_quot]
  convert card_filter_treeAct h _ _ huv using 2 <;> ext <;> simp

/-! ### Marginal sets -/

section marginal
variable {G S : Type*} [Group G] {act : S → G → Option S}

theorem isMarginal_empty : IsMarginal act ∅ := ⟨0, IsKMarginal.zero⟩

theorem isMarginal_of_marginalizes {E I : Set S} {g : G} (hI : IsMarginal act I)
    (hg : Marginalizes act g E I) : IsMarginal act E := by
  obtain ⟨k, hk⟩ := hI
  have := IsKMarginal.succ (l := 1) (fun _ => E) (fun _ => I) (fun _ => g) (fun _ => hk)
    (fun _ => hg)
  rw [Set.iUnion_const] at this
  exact ⟨k + 1, this⟩

theorem isMarginal_union (hact : IsPartialAction act) {E F : Set S} (hE : IsMarginal act E)
    (hF : IsMarginal act F) : IsMarginal act (E ∪ F) := by
  have := (isMarginal_union_subset_image act hact).1 {E, F} (by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl <;> assumption)
  simpa using this

theorem isMarginal_subset (hact : IsPartialAction act) {E E' : Set S} (h : E' ⊆ E)
    (hE : IsMarginal act E) : IsMarginal act E' :=
  (isMarginal_union_subset_image act hact).2.1 E E' h hE

theorem isMarginal_image (hact : IsPartialAction act) {E : Set S} (g : G)
    (hE : IsMarginal act E) : IsMarginal act (image act E g) :=
  (isMarginal_union_subset_image act hact).2.2.2 E g hE

theorem act_step (hact : IsPartialAction act) {x y z : S} {g : G} {i : ℕ}
    (h1 : act x (g ^ i) = some y) (h2 : act x (g ^ (i + 1)) = some z) : act y g = some z := by
  have h3 := (hact.inv _ _ _).mp h1
  have := hact.mul _ _ _ _ _ h3 h2
  rwa [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul] at this

/-- A set `E` is marginalized by `g` off `I` when one step of `g` from `E` or from an auxiliary
set `P` (outside `I`) lands in `P ∪ I`, and `E` is disjoint from `P ∪ I`. -/
theorem marginalizes_of_step (hact : IsPartialAction act) {g : G} {E I P : Set S}
    (hstep : ∀ x, (x ∈ E ∨ x ∈ P) → x ∉ I → ∀ y, act x g = some y → y ∈ P ∨ y ∈ I)
    (hdisj : ∀ x ∈ E, x ∉ P ∧ x ∉ I) : Marginalizes act g E I := by
  intro x hx k hk ⟨y, hyE, hy⟩
  by_contra hcon
  push Not at hcon
  have hdefd : ∀ i ≤ k, ∃ z, act x (g ^ i) = some z := by
    intro i hi
    rcases lt_or_eq_of_le hi with hi | rfl
    · have := (hcon i hi).1
      unfold actPow at this
      exact Option.ne_none_iff_exists'.mp this
    · exact ⟨y, hy⟩
  have key : ∀ i, 1 ≤ i → i ≤ k → ∃ z, act x (g ^ i) = some z ∧ (z ∈ P ∨ z ∈ I) := by
    intro i hi1 hik
    induction i with
    | zero => omega
    | succ i ih =>
      obtain ⟨w, hw⟩ := hdefd (i + 1) hik
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have hx0 : x ∉ I := by
          intro hxI
          exact (hcon 0 hk).2 x hxI (by simp [actPow, hact.one])
        simp only [zero_add, pow_one] at hw ⊢
        exact ⟨w, hw, hstep x (Or.inl hx) hx0 w hw⟩
      · obtain ⟨z, hz, hzP⟩ := ih hipos (by omega)
        have hzI : z ∉ I := fun hzI => (hcon i (by omega)).2 z hzI hz
        have hzP' : z ∈ P := hzP.resolve_right hzI
        refine ⟨w, hw, hstep z (Or.inr hzP') hzI w (act_step hact hz hw)⟩
  obtain ⟨z, hz, hzP⟩ := key k hk le_rfl
  unfold actPow at hy
  rw [hy] at hz
  cases hz
  rcases hzP with h | h
  · exact (hdisj y hyE).1 h
  · exact (hdisj y hyE).2 h

theorem isMarginal_undefined (g : G) : IsMarginal act {x | act x g = none} := by
  apply isMarginal_of_marginalizes (g := g) isMarginal_empty
  intro x hx k hk ⟨y, _, hy⟩
  refine ⟨1, ?_, Or.inl ?_⟩
  · rcases Nat.lt_or_ge 1 k with h | h
    · exact h
    · have : k = 1 := by omega
      subst this
      simp only [Set.mem_ofPred_eq] at hx
      unfold actPow at hy; rw [pow_one, hx] at hy; cases hy
  · unfold actPow; rw [pow_one]; exact hx

end marginal

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Concrete elements -/

/-- `t ↦ t'` under an element whose reduced diagram is listed by `l`. -/
def ActsBy (e : MooreF) (l : List (Seq × Seq)) : Prop :=
  ∀ t t', seqAct t e = some t' ↔ ∃ p ∈ l, ∃ s, t = p.1 ++ s ∧ t' = p.2 ++ s

theorem actsBy_ofDiagram {lL lR : List Seq} (hL : Good lL) (hR : Good lR)
    (hlen : lL.length = lR.length) (hnc : noCaret lL lR = true) (hcov : Covers lL 0)
    (hne : lL ≠ []) : ActsBy (ofDiagram lL.toFinset lR.toFinset) (lL.zip lR) :=
  seqAct_ofDiagram hL hR hlen hnc hcov hne

theorem ActsBy.rel {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {P Q : Seq → Prop}
    (h : ∀ p ∈ l, ∀ s, (P (p.1 ++ s) ↔ Q (p.2 ++ s))) {t t' : Seq}
    (ht : seqAct t e = some t') : P t ↔ Q t' := by
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he t t').mp ht
  exact h p hp s

theorem ActsBy.rel_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {P Q : Seq → Prop}
    (h : ∀ p ∈ l, ∀ s, (P (p.2 ++ s) ↔ Q (p.1 ++ s))) {t t' : Seq}
    (ht : seqAct t e⁻¹ = some t') : P t ↔ Q t' := by
  rw [← seqAct_inv] at ht
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he t' t).mp ht
  exact h p hp s

theorem ActsBy.dom {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ t', seqAct t e = some t') : ∃ p ∈ l, p.1 <+: t := by
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he _ t').mp ht'
  exact ⟨p, hp, List.prefix_append _ _⟩

theorem ActsBy.dom_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ t', seqAct t e⁻¹ = some t') : ∃ p ∈ l, p.2 <+: t := by
  obtain ⟨t', ht'⟩ := ht
  rw [← seqAct_inv] at ht'
  obtain ⟨p, hp, s, rfl, rfl⟩ := (he t' _).mp ht'
  exact ⟨p, hp, List.prefix_append _ _⟩

theorem ActsBy.def {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ p ∈ l, p.1 <+: t) : ∃ t', seqAct t e = some t' := by
  obtain ⟨p, hp, s, rfl⟩ := ht
  exact ⟨p.2 ++ s, (he _ _).mpr ⟨p, hp, s, rfl, rfl⟩⟩

theorem ActsBy.def_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (ht : ∃ p ∈ l, p.2 <+: t) : ∃ t', seqAct t e⁻¹ = some t' := by
  obtain ⟨p, hp, s, rfl⟩ := ht
  exact ⟨p.1 ++ s, (seqAct_inv _ _ _).mp ((he _ _).mpr ⟨p, hp, s, rfl, rfl⟩)⟩

/-- In a tree on which `e` acts, every left leaf of `e` is extended. -/
theorem ActsBy.exists_extends {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    (hanti : Antichain (l.map Prod.fst)) {T T' : Finset Seq} (hT : IsTree T)
    (hTT : treeAct T e = some T') {w : Seq} (hw : w ∈ l.map Prod.fst) : ∃ t ∈ T, w <+: t := by
  apply IsTree.exists_extends hT hanti _ hw
  intro t ht
  obtain ⟨p, hp, hpt⟩ := he.dom (((treeAct_some_iff T T' e).mp hTT).1 t ht)
  exact ⟨p.1, List.mem_map_of_mem hp, hpt⟩

theorem ActsBy.exists_extends_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    (hanti : Antichain (l.map Prod.snd)) {T T' : Finset Seq} (hT : IsTree T)
    (hTT : treeAct T e⁻¹ = some T') {w : Seq} (hw : w ∈ l.map Prod.snd) : ∃ t ∈ T, w <+: t := by
  apply IsTree.exists_extends hT hanti _ hw
  intro t ht
  obtain ⟨p, hp, hpt⟩ := he.dom_inv (((treeAct_some_iff T T' _).mp hTT).1 t ht)
  exact ⟨p.2, List.mem_map_of_mem hp, hpt⟩

/-- Small trees. -/
def lf : List Seq := [[]]
def full1 : List Seq := joinL lf lf
def full2 : List Seq := joinL full1 full1
def full3 : List Seq := joinL full2 full2
def full4 : List Seq := joinL full3 full3

theorem good_full1 : Good full1 := good_join good_leaf good_leaf
theorem good_full2 : Good full2 := good_join good_full1 good_full1
theorem good_full3 : Good full3 := good_join good_full2 good_full2
theorem good_full4 : Good full4 := good_join good_full3 good_full3

/-! #### `x₀` -/

def x0L : List Seq := joinL (joinL lf lf) lf
def x0R : List Seq := joinL lf (joinL lf lf)

theorem x0_eq : x0 = ofDiagram x0L.toFinset x0R.toFinset := by
  unfold x0; congr 1

theorem actsBy_x0 : ActsBy x0 (x0L.zip x0R) := by
  rw [x0_eq]
  exact actsBy_ofDiagram (good_join (good_join good_leaf good_leaf) good_leaf)
    (good_join good_leaf (good_join good_leaf good_leaf)) rfl (by decide)
    (by simp [x0L, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### `x₁` -/

def x1L : List Seq := joinL lf (joinL (joinL lf lf) lf)
def x1R : List Seq := joinL lf (joinL lf (joinL lf lf))

theorem x1_eq : x1 = ofDiagram x1L.toFinset x1R.toFinset := by
  unfold x1; congr 1

theorem actsBy_x1 : ActsBy x1 (x1L.zip x1R) := by
  rw [x1_eq]
  exact actsBy_ofDiagram (good_join good_leaf (good_join (good_join good_leaf good_leaf) good_leaf))
    (good_join good_leaf (good_join good_leaf (good_join good_leaf good_leaf))) rfl (by decide)
    (by simp [x1L, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### `a`, `b` (Lemma 5.7) -/

def aL : List Seq := joinL (joinL (joinL lf (joinL lf lf)) lf) (joinL (joinL lf lf) lf)
def aR : List Seq := joinL (joinL (joinL lf lf) (joinL (joinL lf lf) lf)) (joinL lf lf)

theorem a_eq : elemA = ofDiagram aL.toFinset aR.toFinset := by
  unfold elemA; congr 1

theorem good_aL : Good aL :=
  good_join (good_join (good_join good_leaf (good_join good_leaf good_leaf)) good_leaf)
    (good_join (good_join good_leaf good_leaf) good_leaf)

theorem actsBy_a : ActsBy elemA (aL.zip aR) := by
  rw [a_eq]
  exact actsBy_ofDiagram good_aL
    (good_join (good_join (good_join good_leaf good_leaf)
      (good_join (good_join good_leaf good_leaf) good_leaf)) (good_join good_leaf good_leaf))
    rfl (by decide)
    (by simp [aL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

def bL : List Seq := joinL (joinL (joinL lf (joinL lf lf)) lf) (joinL lf lf)
def bR : List Seq := joinL (joinL (joinL lf lf) lf) (joinL (joinL lf lf) lf)

theorem b_eq : elemB = ofDiagram bL.toFinset bR.toFinset := by
  unfold elemB; congr 1

theorem good_bL : Good bL :=
  good_join (good_join (good_join good_leaf (good_join good_leaf good_leaf)) good_leaf)
    (good_join good_leaf good_leaf)

theorem actsBy_b : ActsBy elemB (bL.zip bR) := by
  rw [b_eq]
  exact actsBy_ofDiagram good_bL
    (good_join (good_join (good_join good_leaf good_leaf) good_leaf)
      (good_join (good_join good_leaf good_leaf) good_leaf))
    rfl (by decide)
    (by simp [bL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### `c`, `d` (Lemma 5.10) -/

def cL : List Seq := joinL (joinL lf lf) (joinL lf lf)
def cR : List Seq := joinL lf (joinL (joinL lf lf) lf)

theorem c_eq : elemC = ofDiagram cL.toFinset cR.toFinset := by
  unfold elemC; congr 1

theorem good_cL : Good cL := good_join (good_join good_leaf good_leaf) (good_join good_leaf good_leaf)

theorem actsBy_c : ActsBy elemC (cL.zip cR) := by
  rw [c_eq]
  exact actsBy_ofDiagram good_cL
    (good_join good_leaf (good_join (good_join good_leaf good_leaf) good_leaf))
    rfl (by decide)
    (by simp [cL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

def dL : List Seq := joinL (joinL (joinL lf lf) lf) lf
def dR : List Seq := joinL (joinL lf (joinL lf lf)) lf

theorem d_eq : elemD = ofDiagram dL.toFinset dR.toFinset := by
  unfold elemD; congr 1

theorem good_dL : Good dL := good_join (good_join (good_join good_leaf good_leaf) good_leaf) good_leaf

theorem actsBy_d : ActsBy elemD (dL.zip dR) := by
  rw [d_eq]
  exact actsBy_ofDiagram good_dL
    (good_join (good_join good_leaf (good_join good_leaf good_leaf)) good_leaf)
    rfl (by decide)
    (by simp [dL, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num) (by decide)

/-! #### The element `g` of Lemma 5.12 -/

/-- The right comb with `n + 1` leaves. -/
def comb : ℕ → List Seq
  | 0 => lf
  | n + 1 => joinL lf (comb n)

theorem good_comb : ∀ n, Good (comb n)
  | 0 => good_leaf
  | n + 1 => good_join good_leaf (good_comb n)

def gL : List Seq := joinL full3 (joinL full2 (joinL full1 lf))
def gR : List Seq := comb 14

theorem good_gL : Good gL :=
  good_join good_full3 (good_join good_full2 (good_join good_full1 good_leaf))

noncomputable def elemG : MooreF := ofDiagram gL.toFinset gR.toFinset

theorem actsBy_g : ActsBy elemG (gL.zip gR) :=
  actsBy_ofDiagram good_gL (good_comb 14) rfl (by decide)
    (by simp [gL, full3, full2, full1, joinL, lf, Covers, seqVal_cons, seqVal_nil]; norm_num)
    (by decide)

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Counting leaves -/

/-- `|T/u|`, as the number of leaves of `T` extending `u`. -/
noncomputable def qc (T : Finset Seq) (u : Seq) : ℕ := (T.filter (u <+: ·)).card

/-- `|T/001|`. -/
noncomputable abbrev A1 (T : Finset Seq) : ℕ := qc T [false, false, true]
/-- `|T/01|`. -/
noncomputable abbrev A2 (T : Finset Seq) : ℕ := qc T [false, true]
/-- `|T/10|`. -/
noncomputable abbrev A3 (T : Finset Seq) : ℕ := qc T [true, false]

theorem quot_card (T : Finset Seq) (u : Seq) : (quot T u).card = qc T u := card_quot T u

theorem bits_001 : bits "001" = [false, false, true] := rfl
theorem bits_01 : bits "01" = [false, true] := rfl
theorem bits_10 : bits "10" = [true, false] := rfl

theorem tPlus_iff (T : Finset Seq) : TPlus T ↔ A1 T < A2 T ∧ A2 T < A3 T := by
  simp only [TPlus, quot_card, bits_001, bits_01, bits_10]

theorem tMinus_iff (T : Finset Seq) : TMinus T ↔ A2 T < A1 T ∧ A3 T < A2 T := by
  simp only [TMinus, quot_card, bits_001, bits_01, bits_10, gt_iff_lt]

theorem twoTimes_iff (T : Finset Seq) : TwoTimes T ↔ 2 * A1 T ≤ A2 T ∧ 2 * A2 T ≤ A3 T := by
  simp only [TwoTimes, quot_card, bits_001, bits_01, bits_10]

theorem halfTimes_iff (T : Finset Seq) : HalfTimes T ↔ 2 * A2 T ≤ A1 T ∧ 2 * A3 T ≤ A2 T := by
  simp only [HalfTimes, quot_card, bits_001, bits_01, bits_10, ge_iff_le]

theorem mem_EBad (T : Finset Seq) : T ∈ EBad ↔ IsTree T ∧ ¬ TPlus T ∧ ¬ TMinus T := Iff.rfl

theorem mem_EStar (T : Finset Seq) : T ∈ EStar ↔ IsTree T ∧ ¬ TwoTimes T ∧ ¬ HalfTimes T :=
  Iff.rfl

theorem card_filter_le_of {T : Finset Seq} {P Q : Seq → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} (h : ∀ t ∈ T, P t → Q t) :
    (T.filter P).card ≤ (T.filter Q).card := by
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, h t ht.1 ht.2⟩

theorem card_filter_lt_of {T : Finset Seq} {P Q : Seq → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} (h : ∀ t ∈ T, P t → Q t)
    (hex : ∃ t ∈ T, Q t ∧ ¬ P t) : (T.filter P).card < (T.filter Q).card := by
  apply Finset.card_lt_card
  refine ⟨fun t ht => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, h t ht.1 ht.2⟩
  · obtain ⟨t, ht, hq, hp⟩ := hex
    have := hsub (Finset.mem_filter.mpr ⟨ht, hq⟩)
    exact hp (Finset.mem_filter.mp this).2

theorem card_filter_or {T : Finset Seq} {P Q : Seq → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} {_ : DecidablePred (fun t => P t ∨ Q t)}
    (h : ∀ t ∈ T, ¬ (P t ∧ Q t)) :
    (T.filter (fun t => P t ∨ Q t)).card = (T.filter P).card + (T.filter Q).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro t ht hp hq
    exact h t ht ⟨hp, hq⟩

theorem prefix_cases {u v t : Seq} (hu : u <+: t) (hv : v <+: t) : u <+: v ∨ v <+: u :=
  List.prefix_or_prefix_of_prefix hu hv

/-! ### Effect of the elements on the counts -/

theorem ActsBy.qc_eq {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {T T' : Finset Seq}
    (h : treeAct T e = some T') (u v : Seq)
    (hl : ∀ p ∈ l, ∀ s, (u <+: p.1 ++ s ↔ v <+: p.2 ++ s)) : qc T' v = qc T u :=
  by unfold qc; convert card_filter_treeAct h (u <+: ·) (v <+: ·) (fun _ _ _ ht => he.rel hl ht)
       using 2 <;> ext <;> simp

theorem ActsBy.qc_eq_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    {T T' : Finset Seq} (h : treeAct T e⁻¹ = some T') (u v : Seq)
    (hl : ∀ p ∈ l, ∀ s, (u <+: p.2 ++ s ↔ v <+: p.1 ++ s)) : qc T' v = qc T u :=
  by unfold qc; convert card_filter_treeAct h (u <+: ·) (v <+: ·) (fun _ _ _ ht => he.rel_inv hl ht)
       using 2 <;> ext <;> simp

theorem ActsBy.qc_eq_filter {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l)
    {T T' : Finset Seq} (h : treeAct T e = some T') (P : Seq → Prop) (v : Seq)
    (hl : ∀ p ∈ l, ∀ s, (P (p.1 ++ s) ↔ v <+: p.2 ++ s)) : qc T' v = (T.filter P).card :=
  by unfold qc; convert card_filter_treeAct h P (v <+: ·) (fun _ _ _ ht => he.rel hl ht)
       using 2; ext; simp

section counts0
variable {T T' : Finset Seq}

theorem x0_counts (h : treeAct T x0 = some T') : A2 T' = A1 T ∧ A3 T' = A2 T :=
  ⟨actsBy_x0.qc_eq h _ _ (by simp [x0L, x0R, joinL, lf]),
    actsBy_x0.qc_eq h _ _ (by simp [x0L, x0R, joinL, lf])⟩

theorem x0inv_counts (h : treeAct T x0⁻¹ = some T') : A1 T' = A2 T ∧ A2 T' = A3 T :=
  ⟨actsBy_x0.qc_eq_inv h _ _ (by simp [x0L, x0R, joinL, lf]),
    actsBy_x0.qc_eq_inv h _ _ (by simp [x0L, x0R, joinL, lf])⟩

theorem x1_counts (h : treeAct T x1 = some T') : A1 T' = A1 T ∧ A2 T' = A2 T :=
  ⟨actsBy_x1.qc_eq h _ _ (by simp [x1L, x1R, joinL, lf]),
    actsBy_x1.qc_eq h _ _ (by simp [x1L, x1R, joinL, lf])⟩

theorem x1inv_counts (h : treeAct T x1⁻¹ = some T') : A1 T' = A1 T ∧ A2 T' = A2 T :=
  ⟨actsBy_x1.qc_eq_inv h _ _ (by simp [x1L, x1R, joinL, lf]),
    actsBy_x1.qc_eq_inv h _ _ (by simp [x1L, x1R, joinL, lf])⟩

end counts0

theorem ActsBy.ext_of {e : MooreF} {lL lR : List Seq} (he : ActsBy e (lL.zip lR)) (hL : Good lL)
    (hlen : lL.length = lR.length) {T T' : Finset Seq} (hT : IsTree T)
    (h : treeAct T e = some T') {w : Seq} (hw : w ∈ lL) : ∃ t ∈ T, w <+: t := by
  have hm : (lL.zip lR).map Prod.fst = lL := List.map_fst_zip (by omega)
  exact he.exists_extends (by rw [hm]; exact hL.antichain) hT h (by rw [hm]; exact hw)

theorem ActsBy.ext_of_inv {e : MooreF} {lL lR : List Seq} (he : ActsBy e (lL.zip lR))
    (hR : Good lR) (hlen : lL.length = lR.length) {T T' : Finset Seq} (hT : IsTree T)
    (h : treeAct T e⁻¹ = some T') {w : Seq} (hw : w ∈ lR) : ∃ t ∈ T, w <+: t := by
  have hm : (lL.zip lR).map Prod.snd = lR := List.map_snd_zip (by omega)
  exact he.exists_extends_inv (by rw [hm]; exact hR.antichain) hT h (by rw [hm]; exact hw)

theorem not_both_prefix {u v t : Seq} (hu : u <+: t) (hv : v <+: t) (h : u.length = v.length)
    (hne : u ≠ v) : False := by
  rcases prefix_cases hu hv with h' | h'
  · exact hne (h'.eq_of_length h)
  · exact hne (h'.eq_of_length h.symm).symm

theorem good_x0R : Good x0R := good_join good_leaf (good_join good_leaf good_leaf)

section counts
variable {T T' : Finset Seq}

theorem a_counts (hT : IsTree T) (h : treeAct T elemA = some T') :
    A1 T' < A1 T ∧ A2 T < A2 T' ∧ A3 T' < A3 T := by
  obtain ⟨t1, ht1, h1⟩ := actsBy_a.ext_of good_aL rfl hT h (w := [false, false, true, true])
    (by simp [aL, joinL, lf])
  obtain ⟨t2, ht2, h2⟩ := actsBy_a.ext_of good_aL rfl hT h (w := [true, false, false])
    (by simp [aL, joinL, lf])
  refine ⟨?_, ?_, ?_⟩
  · show qc T' [false, false, true] < qc T [false, false, true]
    rw [actsBy_a.qc_eq h [false, false, true, false] _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t1, ht1, List.IsPrefix.trans (by simp) h1,
        fun h' => not_both_prefix h' h1 rfl (by simp)⟩
  · show qc T [false, true] < qc T' [false, true]
    rw [actsBy_a.qc_eq_filter h (fun t => [false, false, true, true] <+: t ∨ [false, true] <+: t ∨
      [true, false, false] <+: t) _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact Or.inr (Or.inl ht)
    · exact ⟨t1, ht1, Or.inl h1, fun h' => not_both_prefix (u := [false, true])
        (v := [false, false]) h' (List.IsPrefix.trans (by simp) h1) rfl (by simp)⟩
  · show qc T' [true, false] < qc T [true, false]
    rw [actsBy_a.qc_eq h [true, false, true] _ (by simp [aL, aR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t2, ht2, List.IsPrefix.trans (by simp) h2,
        fun h' => not_both_prefix h' h2 rfl (by simp)⟩

theorem b_counts (hT : IsTree T) (h : treeAct T elemB = some T') :
    A1 T' < A1 T ∧ A2 T' < A1 T ∧ A2 T ≤ A3 T' ∧ A3 T < A3 T' := by
  obtain ⟨t1, ht1, h1⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, false, true, true])
    (by simp [bL, joinL, lf])
  obtain ⟨t2, ht2, h2⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, false, true, false])
    (by simp [bL, joinL, lf])
  obtain ⟨t3, ht3, h3⟩ := actsBy_b.ext_of good_bL rfl hT h (w := [false, true])
    (by simp [bL, joinL, lf])
  have e3 := actsBy_b.qc_eq_filter h (fun t => [false, true] <+: t ∨ [true, false] <+: t)
    [true, false] (by simp [bL, bR, joinL, lf])
  refine ⟨?_, ?_, ?_, ?_⟩
  · show qc T' [false, false, true] < qc T [false, false, true]
    rw [actsBy_b.qc_eq h [false, false, true, false] _ (by simp [bL, bR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t1, ht1, List.IsPrefix.trans (by simp) h1,
        fun h' => not_both_prefix h' h1 rfl (by simp)⟩
  · show qc T' [false, true] < qc T [false, false, true]
    rw [actsBy_b.qc_eq h [false, false, true, true] _ (by simp [bL, bR, joinL, lf])]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact List.IsPrefix.trans (by simp) ht
    · exact ⟨t2, ht2, List.IsPrefix.trans (by simp) h2,
        fun h' => not_both_prefix h' h2 rfl (by simp)⟩
  · show qc T [false, true] ≤ qc T' [true, false]
    rw [e3]
    simp only [qc]
    apply card_filter_le_of
    intro t _ ht; exact Or.inl ht
  · show qc T [true, false] < qc T' [true, false]
    rw [e3]
    simp only [qc]
    apply card_filter_lt_of
    · intro t _ ht; exact Or.inr ht
    · exact ⟨t3, ht3, Or.inl h3, fun h' => not_both_prefix h' h3 rfl (by simp)⟩

end counts

/-! ### Lemma 5.7 -/

/-- `𝒯⁻`. -/
def SMinus : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A3 T < A2 T}
/-- `E_max = E_a ∪ E_b`. -/
def Emax : Set (Finset Seq) := {T | IsTree T ∧ A1 T ≤ A2 T ∧ A3 T ≤ A2 T}
def Eb : Set (Finset Seq) := {T | IsTree T ∧ A1 T < A2 T ∧ A3 T < A2 T}
def Ea : Set (Finset Seq) := Emax \ Eb
def SR : Set (Finset Seq) := {T | IsTree T ∧ A1 T < A3 T ∧ A2 T < A3 T}
def E1 : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A2 T = A3 T}
def E2 : Set (Finset Seq) := {T | IsTree T ∧ A2 T < A1 T ∧ A2 T < A3 T}
def E3 : Set (Finset Seq) := {T | IsTree T ∧ A1 T = A2 T ∧ A2 T < A3 T}

theorem marg_Ea : Marginalizes treeAct elemA Ea ∅ := by
  apply marginalizes_of_step hPA (P := Eb)
  · intro x hx _ y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx
      · exact hx.1.1
      · exact hx.1
    have hxm : A1 x ≤ A2 x ∧ A3 x ≤ A2 x := by
      rcases hx with hx | hx
      · exact hx.1.2
      · exact ⟨hx.2.1.le, hx.2.2.le⟩
    obtain ⟨c1, c2, c3⟩ := a_counts hxT hy
    left
    exact ⟨isTree_of_treeAct hxT hy, by omega, by omega⟩
  · intro x hx
    exact ⟨hx.2, fun h => h⟩

theorem marg_Eb : Marginalizes treeAct elemB Eb ∅ := by
  apply marginalizes_of_step hPA (P := SR)
  · intro x hx _ y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx
      · exact hx.1
      · exact hx.1
    obtain ⟨c1, c2, c3, c4⟩ := b_counts hxT hy
    left
    refine ⟨isTree_of_treeAct hxT hy, ?_, ?_⟩
    · rcases hx with hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
    · rcases hx with hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
  · intro x hx
    refine ⟨fun h => ?_, fun h => h⟩
    have := hx.2; have := h.2; omega

theorem marg_E12 : Marginalizes treeAct x0 (E1 ∪ E2) Emax := by
  apply marginalizes_of_step hPA (P := SMinus)
  · intro x hx hxI y hy
    have hxT : IsTree x := by
      rcases hx with (hx | hx) | hx
      · exact hx.1
      · exact hx.1
      · exact hx.1
    have hx' : A2 x < A1 x := by
      rcases hx with (hx | hx) | hx
      · exact hx.2.1
      · exact hx.2.1
      · exact hx.2.1
    obtain ⟨c1, c2⟩ := x0_counts hy
    have hyT := isTree_of_treeAct hxT hy
    by_cases hc : A2 y < A1 y
    · left; exact ⟨hyT, hc, by omega⟩
    · right; exact ⟨hyT, by omega, by omega⟩
  · intro x hx
    rcases hx with hx | hx
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega

theorem marg_E3 : Marginalizes treeAct x0 E3 Emax := by
  apply marginalizes_of_step hPA (P := SMinus ∪ E1)
  · intro x hx hxI y hy
    have hxT : IsTree x := by
      rcases hx with hx | hx | hx
      · exact hx.1
      · exact hx.1
      · exact hx.1
    have hx' : A2 x ≤ A1 x := by
      rcases hx with hx | hx | hx
      · have := hx.2; omega
      · have := hx.2; omega
      · have := hx.2; omega
    obtain ⟨c1, c2⟩ := x0_counts hy
    have hyT := isTree_of_treeAct hxT hy
    have hle : A3 y ≤ A2 y := by omega
    by_cases hc : A2 y < A1 y
    · left
      rcases lt_or_eq_of_le hle with h' | h'
      · left; exact ⟨hyT, hc, h'⟩
      · right; exact ⟨hyT, hc, h'.symm⟩
    · right; exact ⟨hyT, by omega, hle⟩
  · intro x hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · have := hx.2; have := h.2; omega
      · have := hx.2; have := h.2; omega
    · have := hx.2; have := h.2; omega

theorem EBad_subset : EBad ⊆ Ea ∪ Eb ∪ (E1 ∪ E2) ∪ E3 := by
  intro T hT
  rw [mem_EBad, tPlus_iff, tMinus_iff] at hT
  obtain ⟨hT, h1, h2⟩ := hT
  by_cases hm : A1 T ≤ A2 T ∧ A3 T ≤ A2 T
  · by_cases hb : A1 T < A2 T ∧ A3 T < A2 T
    · left; left; right; exact ⟨hT, hb⟩
    · left; left; left; exact ⟨⟨hT, hm⟩, fun h => hb h.2⟩
  · rcases Nat.lt_or_ge (A2 T) (A1 T) with ha | ha
    · rcases Nat.lt_or_ge (A2 T) (A3 T) with hc | hc
      · left; right; right; exact ⟨hT, ha, hc⟩
      · rcases lt_or_eq_of_le hc with hc | hc
        · exact absurd ⟨ha, hc⟩ h2
        · left; right; left; exact ⟨hT, ha, hc.symm⟩
    · rcases lt_or_eq_of_le ha with ha | ha
      · have hc : A2 T < A3 T := by omega
        exact absurd ⟨ha, hc⟩ h1
      · right; exact ⟨hT, ha, by omega⟩

theorem isMarginal_EBad' : IsMarginal treeAct EBad := by
  have hEa := isMarginal_of_marginalizes isMarginal_empty marg_Ea
  have hEb := isMarginal_of_marginalizes isMarginal_empty marg_Eb
  have hEmax : IsMarginal treeAct Emax := by
    apply isMarginal_subset hPA _ (isMarginal_union hPA hEa hEb)
    intro T hT
    by_cases hb : T ∈ Eb
    · exact Or.inr hb
    · exact Or.inl ⟨hT, hb⟩
  have hE12 := isMarginal_of_marginalizes hEmax marg_E12
  have hE3 := isMarginal_of_marginalizes hEmax marg_E3
  exact isMarginal_subset hPA EBad_subset
    (isMarginal_union hPA (isMarginal_union hPA (isMarginal_union hPA hEa hEb) hE12) hE3)

/-! ### Lemma 5.9 -/

theorem mem_gens {γ : MooreF} : γ ∈ gens ↔ γ = x0 ∨ γ = x1 ∨ γ = x0⁻¹ ∨ γ = x1⁻¹ := by
  simp [gens]

theorem inv_mem_gens {γ : MooreF} (h : γ ∈ gens) : γ⁻¹ ∈ gens := by
  rw [mem_gens] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem plus_step (T : Finset Seq) (γ : MooreF) (hT : IsTree T) (hp : TPlus T) (hγ : γ ∈ gens) :
    treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TPlus T') := by
  rcases h : treeAct T γ with _ | T'
  · exact Or.inl rfl
  right
  refine ⟨T', rfl, ?_⟩
  have hT' := isTree_of_treeAct hT h
  by_cases hp' : TPlus T'
  · exact Or.inr hp'
  left
  refine ⟨hT', hp', fun hm => ?_⟩
  rw [tPlus_iff] at hp
  rw [tMinus_iff] at hm
  rw [mem_gens] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · have := x0_counts h; omega
  · have := x1_counts h; omega
  · have := x0inv_counts h; omega
  · have := x1inv_counts h; omega

theorem minus_step (T : Finset Seq) (γ : MooreF) (hT : IsTree T) (hp : TMinus T) (hγ : γ ∈ gens) :
    treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TMinus T') := by
  rcases h : treeAct T γ with _ | T'
  · exact Or.inl rfl
  right
  refine ⟨T', rfl, ?_⟩
  have hT' := isTree_of_treeAct hT h
  by_cases hp' : TMinus T'
  · exact Or.inr hp'
  left
  refine ⟨hT', fun hm => ?_, hp'⟩
  rw [tMinus_iff] at hp
  rw [tPlus_iff] at hm
  rw [mem_gens] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · have := x0_counts h; omega
  · have := x1_counts h; omega
  · have := x0inv_counts h; omega
  · have := x1inv_counts h; omega

theorem qc_pos {T : Finset Seq} {u t : Seq} (ht : t ∈ T) (h : u <+: t) : 0 < qc T u := by
  unfold qc
  apply Finset.card_pos.mpr
  exact ⟨t, Finset.mem_filter.mpr ⟨ht, h⟩⟩

theorem exists_of_qc_pos {T : Finset Seq} {u : Seq} (h : 0 < qc T u) : ∃ t ∈ T, u <+: t := by
  unfold qc at h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h
  exact ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-- For a tree, `|T/01| = 0` forces `|T/001| = 0`. -/
theorem A1_eq_zero {T : Finset Seq} (hT : IsTree T) (h : A2 T = 0) : A1 T = 0 := by
  by_contra hne
  obtain ⟨t, ht, htp⟩ := exists_of_qc_pos (Nat.pos_of_ne_zero hne)
  obtain ⟨t', ht', hi⟩ := IsTree.exists_mem hT (ext0 [false, true])
  by_cases hl : 2 ≤ t'.length
  · have := prefix_of_isInitialPart (isInitialPart_ext0 [false, true]) hi (by simpa using hl)
    have := qc_pos ht' this
    simp only [A2] at h; omega
  · have h1 : t' <+: [false, true] :=
      prefix_of_isInitialPart hi (isInitialPart_ext0 [false, true]) (by simp; omega)
    have h2 : t' <+: [false, false, true] := by
      match t', h1, hl with
      | [], _, _ => simp
      | [b], h1, _ =>
        simp only [List.cons_prefix_cons] at h1
        rw [h1.1]; simp
      | _ :: _ :: _, _, hl => simp at hl
    have := IsTree.eq_of_prefix hT ht' ht (h2.trans htp)
    subst this
    have := htp.length_le
    simp at this; omega

theorem minus_step' {T T' : Finset Seq} {γ : MooreF} (hT : IsTree T) (hm : TMinus T)
    (hγ : γ ∈ gens) (h : treeAct T γ = some T') (hT'E : T' ∉ EStar) : TMinus T' := by
  rcases minus_step T γ hT hm hγ with h' | ⟨T'', h', hT''⟩
  · rw [h] at h'; cases h'
  rw [h] at h'
  cases h'
  rcases hT'' with hE | hT''
  swap
  · exact hT''
  exfalso
  rw [mem_EBad, tPlus_iff, tMinus_iff] at hE
  rw [mem_EStar, twoTimes_iff, halfTimes_iff] at hT'E
  rw [tMinus_iff] at hm
  have hpos : 0 < A2 T' := by
    rw [mem_gens] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · have := x0_counts h; omega
    · have := x1_counts h; omega
    · have := x0inv_counts h
      obtain ⟨t, ht, htp⟩ := actsBy_x0.ext_of_inv good_x0R rfl hT h (w := [true, false])
        (by simp [x0R, joinL, lf])
      have : 0 < A3 T := qc_pos ht htp
      omega
    · have := x1inv_counts h; omega
  obtain ⟨hT', h1, h2⟩ := hE
  have h3 : (2 * A1 T' ≤ A2 T' ∧ 2 * A2 T' ≤ A3 T') ∨ (2 * A2 T' ≤ A1 T' ∧ 2 * A3 T' ≤ A2 T') := by
    by_contra hc
    exact hT'E ⟨hT', fun h3 => hc (Or.inl h3), fun h4 => hc (Or.inr h4)⟩
  omega

theorem twoTimes_or_halfTimes (A : Set (Finset Seq)) (hA : A ⊆ {T | IsTree T} \ EStar)
    (hc : IsConnected treeAct gens A) : (∀ T ∈ A, TwoTimes T) ∨ ∀ T ∈ A, HalfTimes T := by
  have notE : ∀ T ∈ A, TwoTimes T ∨ HalfTimes T := by
    intro T hT
    have := hA hT
    by_contra hc
    push Not at hc
    exact this.2 ⟨this.1, hc.1, hc.2⟩
  have key1 : ∀ T ∈ A, TMinus T → HalfTimes T := by
    intro T hT hm
    rcases notE T hT with h | h
    · rw [tMinus_iff] at hm; rw [twoTimes_iff] at h; omega
    · exact h
  have key2 : ∀ T ∈ A, ¬ TMinus T → TwoTimes T := by
    intro T hT hm
    rcases notE T hT with h | h
    · exact h
    · by_contra h2
      have htree : IsTree T := (hA hT).1
      rw [twoTimes_iff] at h2
      rw [halfTimes_iff] at h
      rw [tMinus_iff] at hm
      by_cases h0 : A2 T = 0
      · have := A1_eq_zero htree h0; omega
      · omega
  have hstep : ∀ T ∈ A, ∀ T' ∈ A, ∀ γ ∈ gens, treeAct T γ = some T' → TMinus T → TMinus T' :=
    fun T hT T' hT' γ hγ h hm => minus_step' (hA hT).1 hm hγ h (hA hT').2
  have hpath : ∀ T ∈ A, ∀ T' ∈ A, TMinus T → TMinus T' := by
    intro T hT T' hT' hm
    obtain ⟨l, p, hp0, hpl, hpA, hpe⟩ := hc T hT T' hT'
    have : ∀ i (hi : i ≤ l), TMinus (p ⟨i, by omega⟩) := by
      intro i hi
      induction i with
      | zero => rw [show (⟨0, _⟩ : Fin (l + 1)) = 0 from rfl, hp0]; exact hm
      | succ i ih =>
        obtain ⟨γ, hγ, he⟩ := hpe ⟨i, by omega⟩
        exact hstep _ (hpA _) _ (hpA _) γ hγ he (ih (by omega))
    have := this l le_rfl
    rwa [show (⟨l, by omega⟩ : Fin (l + 1)) = Fin.last l from rfl, hpl] at this
  by_cases hex : ∃ T ∈ A, TMinus T
  · right
    obtain ⟨T, hT, hm⟩ := hex
    exact fun T' hT' => key1 T' hT' (hpath T hT T' hT' hm)
  · left
    push Not at hex
    exact fun T hT => key2 T hT (hex T hT)

/-! ### Lemma 5.10 -/

section counts2
variable {T T' : Finset Seq}

theorem c_counts (h : treeAct T elemC = some T') : A2 T' = A1 T ∧ A3 T' = A2 T + A3 T := by
  constructor
  · exact actsBy_c.qc_eq h [false, false, true] _ (by simp [cL, cR, joinL, lf])
  · show qc T' [true, false] = qc T [false, true] + qc T [true, false]
    rw [actsBy_c.qc_eq_filter h (fun t => [false, true] <+: t ∨ [true, false] <+: t) _
      (by simp [cL, cR, joinL, lf])]
    simp only [qc]
    apply card_filter_or
    intro t _ ⟨h1, h2⟩
    exact not_both_prefix h1 h2 rfl (by simp)

theorem d_counts (h : treeAct T elemD = some T') : A2 T' = A1 T + A2 T ∧ A3 T' = A3 T := by
  constructor
  · show qc T' [false, true] = qc T [false, false, true] + qc T [false, true]
    rw [actsBy_d.qc_eq_filter h (fun t => [false, false, true] <+: t ∨ [false, true] <+: t) _
      (by simp [dL, dR, joinL, lf])]
    simp only [qc]
    apply card_filter_or
    intro t _ ⟨h1, h2⟩
    exact not_both_prefix ((List.prefix_append [false, false] [true]).trans h1) h2 rfl
      (by simp)
  · exact actsBy_d.qc_eq h [true, false] _ (by simp [dL, dR, joinL, lf])

end counts2

def SX : Set (Finset Seq) := {T | IsTree T ∧ TPlus T ∧ 2 * A2 T ≤ A3 T}
def E4 : Set (Finset Seq) := {T | IsTree T ∧ TPlus T ∧ A3 T < 2 * A2 T}
def E5 : Set (Finset Seq) := {T | IsTree T ∧ TPlus T ∧ A2 T < 2 * A1 T}
def SY : Set (Finset Seq) := {T | IsTree T ∧ TMinus T ∧ 2 * A3 T ≤ A2 T}
def E6 : Set (Finset Seq) := {T | IsTree T ∧ TMinus T ∧ A2 T < 2 * A3 T}
def E7 : Set (Finset Seq) := {T | IsTree T ∧ TMinus T ∧ A1 T < 2 * A2 T}

theorem plus_or_minus_of_not_EBad {T : Finset Seq} (hT : IsTree T) (h : T ∉ EBad) :
    TPlus T ∨ TMinus T := by
  by_contra hc
  push Not at hc
  exact h ⟨hT, hc.1, hc.2⟩

theorem marg_E4 : Marginalizes treeAct elemC E4 EBad := by
  apply marginalizes_of_step hPA (P := SX)
  · intro x hx hxI y hy
    have hxT : IsTree x ∧ TPlus x := by
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.1⟩
      · exact ⟨hx.1, hx.2.1⟩
    have hyT := isTree_of_treeAct hxT.1 hy
    have hc := c_counts hy
    have hp := hxT.2
    rw [tPlus_iff] at hp
    by_cases hyE : y ∈ EBad
    · exact Or.inr hyE
    left
    rcases plus_or_minus_of_not_EBad hyT hyE with h | h
    · refine ⟨hyT, h, ?_⟩
      omega
    · rw [tMinus_iff] at h; omega
  · intro x hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hx.2.2; have := h.2.2; omega
    · exact h.2.1 hx.2.1

theorem marg_E5 : Marginalizes treeAct x0 (E5 \ E4) (E4 ∪ EBad) := by
  apply marginalizes_of_step hPA (P := ∅)
  · intro x hx hxI y hy
    have hx' : x ∈ E5 \ E4 := by
      rcases hx with hx | hx
      · exact hx
      · exact absurd hx (Set.notMem_empty x)
    obtain ⟨⟨hxT, hxp, hx5⟩, -⟩ := hx'
    have hyT := isTree_of_treeAct hxT hy
    have hc := x0_counts hy
    rw [tPlus_iff] at hxp
    right
    by_cases hyE : y ∈ EBad
    · exact Or.inr hyE
    left
    rcases plus_or_minus_of_not_EBad hyT hyE with h | h
    · exact ⟨hyT, h, by omega⟩
    · rw [tMinus_iff] at h; omega
  · intro x hx
    refine ⟨Set.notMem_empty x, fun h => ?_⟩
    rcases h with h | h
    · exact hx.2 h
    · exact h.2.1 hx.1.2.1

theorem marg_E6 : Marginalizes treeAct elemD E6 EBad := by
  apply marginalizes_of_step hPA (P := SY)
  · intro x hx hxI y hy
    have hxT : IsTree x ∧ TMinus x := by
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.1⟩
      · exact ⟨hx.1, hx.2.1⟩
    have hyT := isTree_of_treeAct hxT.1 hy
    have hc := d_counts hy
    have hp := hxT.2
    rw [tMinus_iff] at hp
    by_cases hyE : y ∈ EBad
    · exact Or.inr hyE
    left
    rcases plus_or_minus_of_not_EBad hyT hyE with h | h
    · rw [tPlus_iff] at h; omega
    · refine ⟨hyT, h, ?_⟩
      omega
  · intro x hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := hx.2.2; have := h.2.2; omega
    · exact h.2.2 hx.2.1

theorem marg_E7 : Marginalizes treeAct x0 (E7 \ E6) (E6 ∪ EBad) := by
  apply marginalizes_of_step hPA (P := ∅)
  · intro x hx hxI y hy
    have hx' : x ∈ E7 \ E6 := by
      rcases hx with hx | hx
      · exact hx
      · exact absurd hx (Set.notMem_empty x)
    obtain ⟨⟨hxT, hxp, hx7⟩, -⟩ := hx'
    have hyT := isTree_of_treeAct hxT hy
    have hc := x0_counts hy
    rw [tMinus_iff] at hxp
    right
    by_cases hyE : y ∈ EBad
    · exact Or.inr hyE
    left
    rcases plus_or_minus_of_not_EBad hyT hyE with h | h
    · rw [tPlus_iff] at h; omega
    · exact ⟨hyT, h, by omega⟩
  · intro x hx
    refine ⟨Set.notMem_empty x, fun h => ?_⟩
    rcases h with h | h
    · exact hx.2 h
    · exact h.2.2 hx.1.2.1

theorem EStar_subset : EStar ⊆ EBad ∪ E4 ∪ (E5 \ E4) ∪ E6 ∪ (E7 \ E6) := by
  intro T hT
  rw [mem_EStar, twoTimes_iff, halfTimes_iff] at hT
  obtain ⟨hT, h1, h2⟩ := hT
  by_cases hE : T ∈ EBad
  · left; left; left; left; exact hE
  rcases plus_or_minus_of_not_EBad hT hE with h | h
  · have h' := h
    rw [tPlus_iff] at h'
    by_cases h4 : A3 T < 2 * A2 T
    · left; left; left; right; exact ⟨hT, h, h4⟩
    · left; left; right; exact ⟨⟨hT, h, by omega⟩, fun h5 => h4 h5.2.2⟩
  · have h' := h
    rw [tMinus_iff] at h'
    by_cases h6 : A2 T < 2 * A3 T
    · left; right; exact ⟨hT, h, h6⟩
    · right; exact ⟨⟨hT, h, by omega⟩, fun h7 => h6 h7.2.2⟩

theorem isMarginal_EStar' : IsMarginal treeAct EStar := by
  have hE := isMarginal_EBad
  have h4 := isMarginal_of_marginalizes hE marg_E4
  have h5 := isMarginal_of_marginalizes (isMarginal_union hPA h4 hE) marg_E5
  have h6 := isMarginal_of_marginalizes hE marg_E6
  have h7 := isMarginal_of_marginalizes (isMarginal_union hPA h6 hE) marg_E7
  exact isMarginal_subset hPA EStar_subset (isMarginal_union hPA (isMarginal_union hPA
    (isMarginal_union hPA (isMarginal_union hPA hE h4) h5) h6) h7)

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg

open Classical CannonFloydParry MooreFoelner

/-! ### Lemma 5.12 -/

/-- `1^m 0`. -/
def rc (m : ℕ) : Seq := List.replicate m true ++ [false]

theorem rc_succ (m : ℕ) : rc (m + 1) = true :: rc m := by simp [rc, List.replicate_succ]

theorem rc_one : rc 1 = [true, false] := rfl

theorem length_full4 : full4.length = 16 := by simp [full4, full3, full2, full1, joinL, lf]

theorem g_rel {T T' : Finset Seq} (h : treeAct T elemG = some T') (j : ℕ) (hj : j ≤ 14) :
    qc T' (rc j) = qc T (full4[j]'(by rw [length_full4]; omega)) := by
  interval_cases j <;>
  exact actsBy_g.qc_eq h _ _ (by simp [gL, gR, comb, full4, full3, full2, full1, joinL, lf, rc])

theorem x0inv_rc {S S' : Finset Seq} (h : treeAct S x0⁻¹ = some S') (k : ℕ) :
    qc S' (rc (k + 1)) = qc S (rc (k + 2)) := by
  rw [rc_succ (k + 1), rc_succ k]
  exact actsBy_x0.qc_eq_inv h _ _ (by simp [x0L, x0R, joinL, lf])

theorem iter_counts {N : ℕ} {T' : Finset Seq} {S : ℕ → Finset Seq}
    (hS : ∀ i, i ≤ N → treeAct T' (x0⁻¹ ^ i) = some (S i)) :
    ∀ i, i ≤ N → ∀ k, qc (S i) (rc (k + 1)) = qc T' (rc (k + 1 + i)) := by
  intro i hi
  induction i with
  | zero =>
    intro k
    have h0 := hS 0 (Nat.zero_le _)
    rw [pow_zero, hPA.one] at h0
    cases h0
    rfl
  | succ i ih =>
    intro k
    have hstep := act_step hPA (hS i (by omega)) (hS (i + 1) hi)
    rw [x0inv_rc hstep k, ih (by omega) (k + 1)]
    congr 2; omega

theorem iter_A {N : ℕ} {T' : Finset Seq} {S : ℕ → Finset Seq}
    (hS : ∀ i, i ≤ N → treeAct T' (x0⁻¹ ^ i) = some (S i)) (i : ℕ) (hi1 : 1 ≤ i) (hiN : i ≤ N) :
    A2 (S i) = qc T' (rc i) ∧ A3 (S i) = qc T' (rc (i + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hstep := act_step hPA (hS j (by omega)) (hS (j + 1) hiN)
  have h1 := (x0inv_counts hstep).2
  have h2 := iter_counts hS j (by omega) 0
  have h3 := iter_counts hS (j + 1) hiN 0
  simp only [A2, A3] at h1 ⊢
  rw [← rc_one] at h1 ⊢
  rw [h1, h2, h3]
  constructor <;> congr 2 <;> omega

theorem chain_up (c : ℕ → ℕ) (h : ∀ m, 1 ≤ m → m ≤ 13 → 2 * c m ≤ c (m + 1)) :
    ∀ a b, 1 ≤ a → a < b → b ≤ 14 → 2 * c a ≤ c b := by
  intro a b ha hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h' | h'
    · have := ih h' (by omega)
      have := h b (by omega) (by omega)
      omega
    · have : a = b := by omega
      subst this
      exact h a ha (by omega)

theorem chain_down (c : ℕ → ℕ) (h : ∀ m, 1 ≤ m → m ≤ 13 → 2 * c (m + 1) ≤ c m) :
    ∀ a b, 1 ≤ a → a < b → b ≤ 14 → 2 * c b ≤ c a := by
  intro a b ha hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with h' | h'
    · have := ih h' (by omega)
      have := h b (by omega) (by omega)
      omega
    · have : a = b := by omega
      subst this
      exact h a ha (by omega)

/-- The candidate tree `U` of Lemma 5.12: all sixteen sequences of length 4. -/
noncomputable def U4 : Finset Seq := full4.toFinset

theorem sorted_U4 : sorted U4 = full4 := good_full4.sorted

theorem interior_U4 : interior U4 = (full4.drop 1).dropLast := by
  rw [interior, sorted_U4]

theorem length_interior_U4 : (interior U4).length = 14 := by
  rw [interior_U4]; simp [length_full4]

theorem interior_U4_get (i : ℕ) (hi : i < (interior U4).length) :
    (interior U4)[i] = full4[i + 1]'(by rw [length_interior_U4] at hi; rw [length_full4]; omega) := by
  simp only [interior_U4, List.getElem_dropLast, List.getElem_drop]
  congr 1; omega

theorem mem_full4 (u : Seq) : u ∈ full4 ↔ u.length = 4 := by
  constructor
  · intro h; simp [full4, full3, full2, full1, joinL, lf] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> rfl
  · intro h
    match u, h with
    | [a, b, c, d], _ =>
      cases a <;> cases b <;> cases c <;> cases d <;> simp [full4, full3, full2, full1, joinL, lf]

/-- Leaves of length at least four make `U` dominated. -/
theorem dominated_U4 {T : Finset Seq} (hT : IsTree T) (hlen : ∀ t ∈ T, 4 ≤ t.length) :
    Dominated U4 T := by
  intro u hu
  have hu4 : u.length = 4 := (mem_full4 u).mp (by simpa [U4] using hu)
  obtain ⟨t, ht, hi⟩ := IsTree.exists_mem hT (ext0 u)
  exact ⟨t, ht, prefix_of_isInitialPart (isInitialPart_ext0 u) hi (by rw [hu4]; exact hlen t ht)⟩

theorem deltaConditions_U4 (T : Finset Seq)
    (h2 : (∀ i j (hi : i < (interior U4).length) (hj : j < (interior U4).length), i < j →
      2 * (quot T ((interior U4).get ⟨i, hi⟩)).card ≤ (quot T ((interior U4).get ⟨j, hj⟩)).card) ∨
    (∀ i j (hi : i < (interior U4).length) (hj : j < (interior U4).length), i < j →
      2 * (quot T ((interior U4).get ⟨j, hj⟩)).card ≤ (quot T ((interior U4).get ⟨i, hi⟩)).card)) :
    DeltaConditions T U4 := by
  refine ⟨⟨[false, true, false, false], ?_, ?_⟩, ⟨[true, false, false, false], ?_, ?_⟩, h2, ?_, ?_⟩
  · simp [U4, full4, full3, full2, full1, joinL, lf]
  · simp [bits]
  · simp [U4, full4, full3, full2, full1, joinL, lf]
  · simp [bits]
  · rw [interior_U4]; simp [full4, full3, full2, full1, joinL, lf]
  · rw [interior_U4]; simp [full4, full3, full2, full1, joinL, lf]

theorem isTree_U4 : IsTree U4 := good_full4.2

theorem delta_spec {T : Finset Seq} (hT : IsTree T) (hU : Dominated U4 T)
    (hc : DeltaConditions T U4) : IsTree (delta T) ∧ Dominated U4 (delta T) := by
  have h := exists_max_deltaConditions T hT ⟨U4, isTree_U4, hU, hc⟩
  unfold delta
  rw [dif_pos h]
  have spec := Classical.choose_spec h
  exact ⟨spec.1, spec.2.2.2 U4 isTree_U4 hU hc⟩

theorem len_of_dominated {D : Finset Seq} (hD : IsTree D) (hU : Dominated U4 D) :
    ∀ v ∈ D, 4 ≤ v.length := by
  intro v hv
  by_contra hlt
  push Not at hlt
  have hu : v ++ List.replicate (4 - v.length) false ∈ U4 := by
    simp only [U4, List.mem_toFinset, mem_full4, List.length_append, List.length_replicate]
    omega
  obtain ⟨w, hw, huw⟩ := hU _ hu
  have hvw : v <+: w := (List.prefix_append _ _).trans huw
  have := IsTree.eq_of_prefix hD hv hw hvw
  subst this
  have := huw.length_le
  simp at this; omega

theorem actsProperly_of {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (h : ∃ p ∈ l, p.1 <+: t ∧ p.1.length < t.length) : ActsProperly e t := by
  obtain ⟨p, hp, ⟨s, rfl⟩, hlen⟩ := h
  have hs : s ≠ [] := by rintro rfl; simp at hlen
  refine ⟨p.2 ++ s, (he _ _).mpr ⟨p, hp, s, rfl, rfl⟩, ?_⟩
  rw [List.getLast?_append_of_ne_nil _ hs, List.getLast?_append_of_ne_nil _ hs]

theorem actsProperly_of_inv {e : MooreF} {l : List (Seq × Seq)} (he : ActsBy e l) {t : Seq}
    (h : ∃ p ∈ l, p.2 <+: t ∧ p.2.length < t.length) : ActsProperly e⁻¹ t := by
  obtain ⟨p, hp, ⟨s, rfl⟩, hlen⟩ := h
  have hs : s ≠ [] := by rintro rfl; simp at hlen
  refine ⟨p.1 ++ s, (seqAct_inv _ _ _).mp ((he _ _).mpr ⟨p, hp, s, rfl, rfl⟩), ?_⟩
  rw [List.getLast?_append_of_ne_nil _ hs, List.getLast?_append_of_ne_nil _ hs]

theorem actsProperly_gens {γ : MooreF} (hγ : γ ∈ gens) {t : Seq} (ht : 4 ≤ t.length) :
    ActsProperly γ t := by
  obtain ⟨a, b, c, d, r, rfl⟩ : ∃ a b c d r, t = a :: b :: c :: d :: r := by
    match t, ht with
    | a :: b :: c :: d :: r, _ => exact ⟨a, b, c, d, r, rfl⟩
  rw [mem_gens] at hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · apply actsProperly_of actsBy_x0
    cases a <;> cases b <;> simp [x0L, x0R, joinL, lf]
  · apply actsProperly_of actsBy_x1
    cases a <;> cases b <;> cases c <;> simp [x1L, x1R, joinL, lf]
  · apply actsProperly_of_inv actsBy_x0
    cases a <;> cases b <;> simp [x0L, x0R, joinL, lf]
  · apply actsProperly_of_inv actsBy_x1
    cases a <;> cases b <;> cases c <;> simp [x1L, x1R, joinL, lf]

theorem len_ge_four {T T1 T2 T' : Finset Seq} (hg : treeAct T elemG = some T')
    (h1 : treeAct T x1⁻¹ = some T1) (h2 : treeAct T (x1⁻¹ ^ 2) = some T2) :
    ∀ t ∈ T, 4 ≤ t.length := by
  intro t ht
  obtain ⟨p, hp, hpt⟩ := actsBy_g.dom (((treeAct_some_iff _ _ _).mp hg).1 t ht)
  have hp1 : p.1 ∈ gL := (List.of_mem_zip hp).1
  by_contra hlt
  push Not at hlt
  have hp3 : p.1 = [true, true, true] := by
    have hle := hpt.length_le
    simp [gL, full3, full2, full1, joinL, lf] at hp1
    rcases hp1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp [h] at hle ⊢ <;> omega
  have htt : t = [true, true, true] := by
    rw [hp3] at hpt
    exact (hpt.eq_of_length (by have := hpt.length_le; simp at this ⊢; omega)).symm
  subst htt
  have hstep : treeAct T1 x1⁻¹ = some T2 := act_step hPA (by rw [pow_one]; exact h1) h2
  have hs : seqAct [true, true, true] x1⁻¹ = some [true, true] := by
    rw [← seqAct_inv]
    exact (actsBy_x1 _ _).mpr ⟨([true, true], [true, true, true]),
      by simp [x1L, x1R, joinL, lf], [], by simp, by simp⟩
  have hmem : [true, true] ∈ T1 := (((treeAct_some_iff _ _ _).mp h1).2 _).mpr ⟨_, ht, hs⟩
  obtain ⟨q, hq, hqt⟩ := actsBy_x1.dom_inv (((treeAct_some_iff _ _ _).mp hstep).1 _ hmem)
  simp [x1L, x1R, joinL, lf] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp at hqt

/-- The pieces of `E**`. -/
def Bad (i : ℕ) : Set (Finset Seq) :=
  {T | treeAct T (x0⁻¹ ^ i) = none} ∪ image treeAct EStar (x0⁻¹ ^ i)⁻¹

/-- `E**` (proof of Lemma 5.12), with `i ≤ N`. -/
def EStar2 (N : ℕ) : Set (Finset Seq) := {T | ∃ i ≤ N, T ∈ Bad i}

theorem isMarginal_Bad (i : ℕ) : IsMarginal treeAct (Bad i) :=
  isMarginal_union hPA (isMarginal_undefined _) (isMarginal_image hPA _ isMarginal_EStar)

theorem isMarginal_EStar2 (N : ℕ) : IsMarginal treeAct (EStar2 N) := by
  induction N with
  | zero =>
    apply isMarginal_subset hPA _ (isMarginal_Bad 0)
    rintro T ⟨i, hi, hT⟩
    rwa [show i = 0 by omega] at hT
  | succ N ih =>
    apply isMarginal_subset hPA _ (isMarginal_union hPA ih (isMarginal_Bad (N + 1)))
    rintro T ⟨i, hi, hT⟩
    rcases Nat.lt_or_ge i (N + 1) with h | h
    · exact Or.inl ⟨i, by omega, hT⟩
    · rw [show i = N + 1 by omega] at hT
      exact Or.inr hT

theorem isConnected_chain {S : ℕ → Finset Seq} {N : ℕ}
    (hstep : ∀ i < N, treeAct (S i) x0⁻¹ = some (S (i + 1))) :
    IsConnected treeAct gens {X | ∃ i ≤ N, X = S i} := by
  rintro X ⟨i, hi, rfl⟩ Y ⟨j, hj, rfl⟩
  rcases le_total i j with hij | hij
  · refine ⟨j - i, fun k => S (i + k.1), by simp, ?_, fun k => ⟨i + k.1, by omega, rfl⟩,
      fun k => ⟨x0⁻¹, by simp [gens], ?_⟩⟩
    · simp only [Fin.val_last]; congr 1; omega
    · simp only [Fin.val_castSucc, Fin.val_succ]
      rw [← add_assoc]
      exact hstep _ (by omega)
  · refine ⟨i - j, fun k => S (i - k.1), by simp, ?_, fun k => ⟨i - k.1, by omega, rfl⟩,
      fun k => ⟨x0, by simp [gens], ?_⟩⟩
    · simp only [Fin.val_last]; congr 1; omega
    · simp only [Fin.val_castSucc, Fin.val_succ]
      have := hstep (i - (k.1 + 1)) (by omega)
      rw [show i - (k.1 + 1) + 1 = i - k.1 by omega] at this
      have := (hPA.inv _ _ _).mp this
      rwa [inv_inv] at this

/-- If `T' ∉ E**`, then the counts along `1ⁱ0` in `T'` form a doubling chain. -/
theorem chain_of_not_EStar2 {T' : Finset Seq} (hT' : IsTree T') (h : T' ∉ EStar2 13) :
    (∀ m, 1 ≤ m → m ≤ 13 → 2 * qc T' (rc m) ≤ qc T' (rc (m + 1))) ∨
    (∀ m, 1 ≤ m → m ≤ 13 → 2 * qc T' (rc (m + 1)) ≤ qc T' (rc m)) := by
  have hdef : ∀ i ≤ 13, ∃ X, treeAct T' (x0⁻¹ ^ i) = some X ∧ X ∉ EStar := by
    intro i hi
    rcases hX : treeAct T' (x0⁻¹ ^ i) with _ | X
    · exact absurd ⟨i, hi, Or.inl hX⟩ h
    · refine ⟨X, rfl, fun hXE => h ⟨i, hi, Or.inr ⟨X, hXE, ?_⟩⟩⟩
      exact (hPA.inv _ _ _).mp hX
  let S : ℕ → Finset Seq := fun i => (treeAct T' (x0⁻¹ ^ i)).getD ∅
  have hS : ∀ i ≤ 13, treeAct T' (x0⁻¹ ^ i) = some (S i) := by
    intro i hi
    obtain ⟨X, hX, -⟩ := hdef i hi
    simp only [S, hX]; rfl
  have hSE : ∀ i ≤ 13, S i ∉ EStar := by
    intro i hi
    obtain ⟨X, hX, hXE⟩ := hdef i hi
    rw [hS i hi] at hX; cases hX; exact hXE
  have hstep : ∀ i < 13, treeAct (S i) x0⁻¹ = some (S (i + 1)) :=
    fun i hi => act_step hPA (hS i hi.le) (hS (i + 1) hi)
  have hA : {X | ∃ i ≤ 13, X = S i} ⊆ {T | IsTree T} \ EStar := by
    rintro X ⟨i, hi, rfl⟩
    exact ⟨isTree_of_treeAct hT' (hS i hi), hSE i hi⟩
  rcases treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes.2.2 _ hA (isConnected_chain hstep) with
    h2 | h2
  · left
    intro m hm1 hm2
    have := (twoTimes_iff _).mp (h2 _ ⟨m, hm2, rfl⟩)
    obtain ⟨e1, e2⟩ := iter_A hS m hm1 hm2
    omega
  · right
    intro m hm1 hm2
    have := (halfTimes_iff _).mp (h2 _ ⟨m, hm2, rfl⟩)
    obtain ⟨e1, e2⟩ := iter_A hS m hm1 hm2
    omega

theorem quot_interior {T T' : Finset Seq} (hg : treeAct T elemG = some T') (i : ℕ)
    (hi : i < (interior U4).length) :
    (quot T ((interior U4).get ⟨i, hi⟩)).card = qc T' (rc (i + 1)) := by
  rw [quot_card, List.get_eq_getElem, interior_U4_get,
    g_rel hg (i + 1) (by rw [length_interior_U4] at hi; omega)]

theorem actsProperlyOn_delta {T T1 T2 T' : Finset Seq} (hT : IsTree T)
    (hg : treeAct T elemG = some T') (h1 : treeAct T x1⁻¹ = some T1)
    (h2 : treeAct T (x1⁻¹ ^ 2) = some T2) (hT' : T' ∉ EStar2 13) :
    ∀ γ ∈ gens, ActsProperlyOn γ (delta T) := by
  have hlen := len_ge_four hg h1 h2
  have hdom := dominated_U4 hT hlen
  have hcond : DeltaConditions T U4 := by
    apply deltaConditions_U4
    rcases chain_of_not_EStar2 (isTree_of_treeAct hT hg) hT' with hc | hc
    · left
      intro i j hi hj hij
      rw [quot_interior hg, quot_interior hg]
      rw [length_interior_U4] at hi hj
      exact chain_up (fun m => qc T' (rc m)) hc (i + 1) (j + 1) (by omega) (by omega) (by omega)
    · right
      intro i j hi hj hij
      rw [quot_interior hg, quot_interior hg]
      rw [length_interior_U4] at hi hj
      exact chain_down (fun m => qc T' (rc m)) hc (i + 1) (j + 1) (by omega) (by omega) (by omega)
  obtain ⟨hD, hDU⟩ := delta_spec hT hdom hcond
  intro γ hγ t ht
  exact actsProperly_gens hγ (len_of_dominated hD hDU t ht)

theorem isMarginal_bad_delta :
    IsMarginal treeAct {T | IsTree T ∧ ¬ ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  apply isMarginal_subset hPA (E := {T | treeAct T elemG = none} ∪ {T | treeAct T x1⁻¹ = none} ∪
    {T | treeAct T (x1⁻¹ ^ 2) = none} ∪ image treeAct (EStar2 13) elemG⁻¹)
  · rintro T ⟨hT, hnot⟩
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨⟨hg, hx1⟩, hx2⟩, himg⟩ := hc
    obtain ⟨T', hT'⟩ := Option.ne_none_iff_exists'.mp hg
    obtain ⟨T1, hT1⟩ := Option.ne_none_iff_exists'.mp hx1
    obtain ⟨T2, hT2⟩ := Option.ne_none_iff_exists'.mp hx2
    apply hnot
    apply actsProperlyOn_delta hT hT' hT1 hT2
    intro hE
    exact himg ⟨T', hE, (hPA.inv _ _ _).mp hT'⟩
  · exact isMarginal_union hPA (isMarginal_union hPA (isMarginal_union hPA
      (isMarginal_undefined _) (isMarginal_undefined _)) (isMarginal_undefined _))
      (isMarginal_image hPA _ (isMarginal_EStar2 13))

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner.Dev.Sec5Marg
open Classical CannonFloydParry MooreFoelner

theorem closure_gens : Subgroup.closure (gens : Set MooreF) = ⊤ := by
  rw [eq_top_iff, ← closure_x0_x1_eq_top]
  apply Subgroup.closure_mono
  intro γ hγ
  rcases hγ with rfl | rfl <;> simp [gens]

theorem not_isTree_empty : ¬ IsTree ∅ := by
  intro h
  obtain ⟨t, ⟨ht, _⟩, _⟩ := h (fun _ => false)
  simp at ht

theorem not_actsProperlyOn_trivial : ¬ ActsProperlyOn x0 trivialTree := by
  intro h
  obtain ⟨t', ht', -⟩ := h [] (by simp [trivialTree])
  obtain ⟨p, hp, s, hps, -⟩ := (actsBy_x0 _ _).mp ht'
  simp [x0L, x0R, joinL, lf] at hp
  rcases hp with rfl | rfl | rfl <;> simp at hps

theorem delta_main : ∃ C : ℝ, ∀ (ε : ℝ) (μ : Finset Seq →₀ ℝ), (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → C * ε ≤ 1 →
      ∃ ν : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens ν (C * ε) ∧
        ↑ν.support ⊆ {U | ∃ T, 0 < μ T ∧ U = delta T ∧ delta T ≠ trivialTree ∧
          ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  set M : Set (Finset Seq) := {T | IsTree T ∧ ¬ ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} with hMdef
  have hM : IsMarginal treeAct M := isMarginal_not_actsProperlyOn_delta
  have hne : (Mᶜ).Nonempty := ⟨∅, fun h => not_isTree_empty h.1⟩
  obtain ⟨C, hC⟩ := exists_const_isWeightedFolner_restrict_compl treeAct hPA gens
    (fun γ hγ => inv_mem_gens hγ) closure_gens M hM hne
  refine ⟨C, fun ε μ hμT hμ hCε => ?_⟩
  obtain ⟨hres, -⟩ := hC ε μ hμ hCε
  have hgood : ∀ T, restrict μ Mᶜ T ≠ 0 →
      0 < μ T ∧ IsTree T ∧ ∀ γ ∈ gens, ActsProperlyOn γ (delta T) := by
    intro T hT
    simp only [restrict, Finsupp.filter_apply] at hT
    split_ifs at hT with hTM
    · have hpos : 0 < μ T := lt_of_le_of_ne (hμ.1 T) (Ne.symm hT)
      have hTT : IsTree T := hμT T (Finsupp.mem_support_iff.mpr hT)
      refine ⟨hpos, hTT, ?_⟩
      by_contra hc
      exact hTM ⟨hTT, hc⟩
    · exact absurd rfl hT
  refine ⟨(restrict μ Mᶜ).mapDomain delta, ?_, ?_⟩
  · apply isWeightedFolner_mapDomain treeAct treeAct hPA hPA gens (fun γ hγ => inv_mem_gens hγ)
      closure_gens _ (C * ε) hres delta
    intro γ hγ s hs
    by_cases h0 : restrict μ Mᶜ s = 0
    · rw [h0, zero_add] at hs
      unfold valAt at hs
      rcases hsy : treeAct s γ with _ | y
      · rw [hsy] at hs; simp at hs
      · rw [hsy] at hs
        obtain ⟨-, hyT, hyP⟩ := hgood y hs.ne'
        obtain ⟨T'', h1, -, h2⟩ := treeAct_delta γ⁻¹ y hyT (hyP γ⁻¹ (inv_mem_gens hγ))
        have : treeAct y γ⁻¹ = some s := (hPA.inv _ _ _).mp hsy
        rw [this] at h1; cases h1
        refine ⟨y, rfl, ?_⟩
        have := (hPA.inv _ _ _).mp h2
        rwa [inv_inv] at this
    · obtain ⟨-, hsT, hsP⟩ := hgood s h0
      obtain ⟨T', h1, -, h2⟩ := treeAct_delta γ s hsT (hsP γ hγ)
      exact ⟨T', h1, h2⟩
  · intro U hU
    have := Finsupp.mapDomain_support hU
    rw [Finset.mem_image] at this
    obtain ⟨T, hT, rfl⟩ := this
    obtain ⟨hpos, -, hP⟩ := hgood T (Finsupp.mem_support_iff.mp hT)
    refine ⟨T, hpos, rfl, ?_, hP⟩
    intro htriv
    have := hP x0 (by simp [gens])
    rw [htriv] at this
    exact not_actsProperlyOn_trivial this

end MooreFoelner.Dev.Sec5Marg

namespace MooreFoelner

open Classical CannonFloydParry

theorem chk_isMarginal_EBad : IsMarginal treeAct EBad := Dev.Sec5Marg.isMarginal_EBad'

theorem chk_treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes :
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TPlus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TPlus T')) ∧
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TMinus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TMinus T')) ∧
    ∀ A : Set (Finset Seq), A ⊆ {T | IsTree T} \ EStar → IsConnected treeAct gens A →
      (∀ T ∈ A, TwoTimes T) ∨ ∀ T ∈ A, HalfTimes T :=
  ⟨Dev.Sec5Marg.plus_step, Dev.Sec5Marg.minus_step, Dev.Sec5Marg.twoTimes_or_halfTimes⟩

theorem chk_isMarginal_EStar : IsMarginal treeAct EStar := Dev.Sec5Marg.isMarginal_EStar'

theorem chk_isMarginal_not_actsProperlyOn_delta :
    IsMarginal treeAct {T | IsTree T ∧ ¬ ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} :=
  Dev.Sec5Marg.isMarginal_bad_delta

theorem chk_exists_const_isWeightedFolner_delta :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : Finset Seq →₀ ℝ), (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → C * ε ≤ 1 →
      ∃ ν : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens ν (C * ε) ∧
        ↑ν.support ⊆ {U | ∃ T, 0 < μ T ∧ U = delta T ∧ delta T ≠ trivialTree ∧
          ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} :=
  Dev.Sec5Marg.delta_main

end MooreFoelner
