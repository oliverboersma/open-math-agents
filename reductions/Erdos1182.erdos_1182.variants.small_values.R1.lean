import FormalConjectures.ErdosProblems.«1182»

/-! Reduction of the small values table. The tree Ramsey and F lower-bound lemmas below are adapted from @Genbox, PR #104. The n = 2 computations are discharged here; the remaining finite graph classifications are hypotheses. -/

open SimpleGraph

lemma OMA.tree_copy_of_degree {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Type) [Fintype U] (T : SimpleGraph U)
    (hT : T.IsTree) (hd : ∀ v, Fintype.card U - 1 ≤ H.degree v) : T ⊑ H := by
  classical
  have hall (k : ℕ) : ∀ (A : Type) [Fintype A] (G : SimpleGraph A),
      Fintype.card A = k → G.IsTree → (∀ v, k - 1 ≤ H.degree v) → G ⊑ H := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A _ G hcard hG hdeg
      by_cases hk : k ≤ 1
      · let : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (hcard.trans_le hk)
        obtain ⟨w⟩ := ‹Nonempty V›
        refine ⟨⟨⟨fun _ => w, ?_⟩, ?_⟩⟩
        · intro a b hab
          exact (hab.ne (Subsingleton.elim a b)).elim
        · intro a b _
          exact Subsingleton.elim a b
      have hk' : 1 < k := by omega
      let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hk')
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      let S : Set A := {v}ᶜ
      have hS : (G.induce S).IsTree :=
        ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce S⟩
      have hS_card : Fintype.card S = k - 1 := by
        change Fintype.card (({v} : Set A)ᶜ : Set A) = k - 1
        rw [Fintype.card_compl_set, hcard]
        simp
      obtain ⟨f⟩ := ih (Fintype.card S) (by omega) S (G.induce S) rfl hS
        (fun w => (Nat.sub_le _ _).trans (hS_card.symm ▸ hdeg w))
      let u' : S := ⟨u, hu.ne.symm⟩
      let used : Finset V := Finset.univ.image (fun a : S => f a)
      have hused : used.card = Fintype.card S := by
        calc
          used.card = (Finset.univ : Finset S).card :=
            Finset.card_image_of_injective _ f.injective
          _ = _ := Finset.card_univ
      have hcenter : f u' ∈ used := Finset.mem_image.mpr ⟨u', Finset.mem_univ _, rfl⟩
      let N := H.neighborFinset (f u')
      have hN : N.card = H.degree (f u') := H.card_neighborFinset_eq_degree _
      have hNself : f u' ∉ N := H.notMem_neighborFinset_self _
      have hlarge : used.card < (insert (f u') N).card := by
        rw [Finset.card_insert_of_notMem hNself, hused, hS_card, hN]
        exact Nat.lt_succ_of_le (hdeg _)
      obtain ⟨w, hw, hnew⟩ := Finset.exists_mem_notMem_of_card_lt_card hlarge
      have hwN : w ∈ N := (Finset.mem_insert.mp hw).resolve_left
        (fun h => hnew (h.symm ▸ hcenter))
      have hwadj : H.Adj (f u') w := (H.mem_neighborFinset _ _).mp hwN
      let g (a : A) : V := if ha : a = v then w else f ⟨a, ha⟩
      have gv : g v = w := by simp [g]
      have gn (a : A) (ha : a ≠ v) : g a = f ⟨a, ha⟩ := by simp [g, ha]
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro a b hab
        by_cases ha : a = v
        · subst a
          have hbu : b = u := huniq b hab
          rw [hbu, gv, gn u hu.ne.symm]
          exact hwadj.symm
        · by_cases hb : b = v
          · subst b
            have hau : a = u := huniq a hab.symm
            rw [hau, gn u hu.ne.symm, gv]
            exact hwadj
          · rw [gn a ha, gn b hb]
            exact f.toHom.map_adj (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      · intro a b heq
        change g a = g b at heq
        by_cases ha : a = v
        · by_cases hb : b = v
          · exact ha.trans hb.symm
          · subst a
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _,
              by simpa only [gv, gn b hb] using heq.symm⟩
        · by_cases hb : b = v
          · subst b
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _,
              by simpa only [gv, gn a ha] using heq⟩
          · rw [gn a ha, gn b hb] at heq
            exact congrArg Subtype.val (f.injective heq)
  exact hall (Fintype.card U) U T rfl hT hd

lemma OMA.tree_ramsey_upper (n : ℕ) (hn : 2 ≤ n) {T : SimpleGraph (Fin n)}
    (hT : T.IsTree) (C : SimpleGraph (Fin (2 * n - 1))) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ := by
  classical
  by_cases htri : (⊤ : SimpleGraph (Fin 3)) ⊑ C
  · exact Or.inl htri
  right
  have hcf : C.CliqueFree 3 := by
    by_contra hc
    exact htri (by simpa only [completeGraph_eq_top] using
      (not_cliqueFree_iff_top_isContained 3).mp hc)
  by_cases hdegree : ∀ v, n - 1 ≤ Cᶜ.degree v
  · have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
    exact OMA.tree_copy_of_degree Cᶜ (Fin n) T hT (by simpa using hdegree)
  push Not at hdegree
  obtain ⟨v, hv⟩ := hdegree
  let S := C.neighborFinset v
  have hcard : n ≤ Fintype.card S := by
    have h := C.degree_compl v
    rw [Fintype.card_fin] at h
    rw [Fintype.card_coe, C.card_neighborFinset_eq_degree]
    omega
  have hclique : Cᶜ.IsClique (S : Set (Fin (2 * n - 1))) := by
    rw [isClique_compl]
    simpa only [S, coe_neighborFinset] using isIndepSet_neighborSet_of_triangleFree C hcf v
  let f : Fin n ↪ S := (Fin.castLEEmb hcard).trans (Fintype.equivFin S).symm.toEmbedding
  refine ⟨⟨⟨fun a => (f a).val, ?_⟩, ?_⟩⟩
  · intro a b hab
    exact hclique (f a).property (f b).property
      (fun he => hab.ne (f.injective (Subtype.ext he)))
  · intro a b he
    exact f.injective (Subtype.ext he)

lemma OMA.tree_ramsey_lower_witness (n N : ℕ) (hn : 2 ≤ n) (hN : N < 2 * n - 1)
    (T : SimpleGraph (Fin n)) (hT : T.Connected) :
    ∃ C : SimpleGraph (Fin N), ¬ ((⊤ : SimpleGraph (Fin 3)) ⊑ C) ∧ ¬ (T ⊑ Cᶜ) := by
  classical
  let color (v : Fin N) : Bool := decide (v.val < n - 1)
  let C : SimpleGraph (Fin N) := (⊤ : SimpleGraph Bool).comap color
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have hinj : Function.Injective (fun i : Fin 3 => color (f i)) := by
      intro i j he
      by_contra hij
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj i j := hij
      have himg : C.Adj (f i) (f j) := f.toHom.map_adj hadj
      exact himg he
    have hcard := Fintype.card_le_of_injective _ hinj
    norm_num at hcard
  · rintro ⟨f⟩
    have hlab (i j : Fin n) : color (f i) = color (f j) := by
      obtain ⟨w⟩ := hT.preconnected i j
      induction w with
      | nil => rfl
      | cons h _ ih =>
        exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
    have hclass (i j : Fin n) : ((f i).val < n - 1) ↔ ((f j).val < n - 1) :=
      decide_eq_decide.mp (hlab i j)
    let g (i : Fin n) : Fin (n - 1) :=
      ⟨if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1), by
        have hi := (f i).isLt
        split <;> omega⟩
    have hg : Function.Injective g := by
      intro i j he
      have heq := congrArg Fin.val he
      change (if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1)) =
        (if (f j).val < n - 1 then (f j).val else (f j).val - (n - 1)) at heq
      apply f.injective
      change f i = f j
      apply Fin.ext
      by_cases hi : (f i).val < n - 1
      · simpa only [if_pos hi, if_pos ((hclass i j).mp hi)] using heq
      · have hj : ¬ (f j).val < n - 1 := fun h => hi ((hclass i j).mpr h)
        simp only [if_neg hi, if_neg hj] at heq
        omega
    have hcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hcard
    omega

lemma OMA.tree_triangle_good (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : Erdos1182.IsTriangleGood T := by
  unfold Erdos1182.IsTriangleGood graphRamsey
  let good : Set ℕ := {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ}
  change sInf good = 2 * n - 1
  have h : 2 * n - 1 ∈ good := OMA.tree_ramsey_upper n hn (T := T) hT
  apply le_antisymm (Nat.sInf_le h)
  refine le_csInf ⟨2 * n - 1, h⟩ ?_
  intro N hN
  by_contra! hlt
  obtain ⟨C, hC1, hC2⟩ := OMA.tree_ramsey_lower_witness n N hn hlt T hT.connected
  change ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ at hN
  exact (hN C).elim hC1 hC2

theorem OMA.f_ge_pred : type_of% @Erdos1182.erdos_1182.variants.F_ge_pred := by
  classical
  intro n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply Erdos1182.le_F
  · have htop := (connected_top (V := Fin n)).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at htop
    have hcard : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
      rw [Set.ncard_eq_toFinset_card']
      change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2
      rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    change n ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard + 1 at htop
    rw [hcard] at htop
    omega
  · intro T hconn hbound
    have hmin := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hmin
    apply OMA.tree_triangle_good n hn T
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_fin, Nat.card_coe_set_eq]
    omega
lemma OMA.F_two : Erdos1182.F 2 = 1 := by
  apply le_antisymm
  · unfold Erdos1182.F
    apply csSup_le'
    intro q hq
    simpa using hq.1
  · have h := OMA.f_ge_pred (n := 2) (by omega)
    simpa using h

lemma OMA.f_two : Erdos1182.f 2 = 1 := by
  classical
  apply le_antisymm
  · unfold Erdos1182.f
    apply csSup_le'
    intro q hq
    obtain ⟨G, hconn, heq, hgood⟩ := hq
    rw [← heq]
    have h := (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))
    rw [Fintype.card_fin] at h
    rw [Set.ncard_eq_toFinset_card']
    change G.edgeFinset.card ≤ 1
    simpa using h
  · unfold Erdos1182.f
    apply le_csSup
    · exact ⟨1, by
        intro q hq
        obtain ⟨G, _, heq, _⟩ := hq
        rw [← heq]
        have h := (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))
        rw [Fintype.card_fin] at h
        rw [Set.ncard_eq_toFinset_card']
        change G.edgeFinset.card ≤ 1
        simpa using h⟩
    · refine ⟨(⊤ : SimpleGraph (Fin 2)), connected_top, ?_, ?_⟩
      · rw [Set.ncard_eq_toFinset_card']
        change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1
        rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
        decide
      · apply OMA.tree_triangle_good 2 (by omega)
        apply isTree_iff_connected_and_card.mpr
        constructor
        · exact connected_top
        · rw [Nat.card_fin, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
          change 2 = (⊤ : SimpleGraph (Fin 2)).edgeFinset.card + 1
          rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
          decide


namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1

/-- The upper bound at three vertices and the other small values of F. -/
def H1 : Prop :=
  Erdos1182.F 3 ≤ 2 ∧ Erdos1182.F 4 = 5 ∧ Erdos1182.F 5 = 7 ∧
  Erdos1182.F 6 = 8 ∧ Erdos1182.F 7 = 11 ∧ Erdos1182.F 8 = 11 ∧
  Erdos1182.F 9 = 16 ∧ Erdos1182.F 10 = 18 ∧ Erdos1182.F 11 = 23 ∧ Erdos1182.F 12 = 23

/-- The small values of f for graphs on at least three vertices. -/
def H2 : Prop :=
  Erdos1182.f 3 = 2 ∧ Erdos1182.f 4 = 5 ∧ Erdos1182.f 5 = 8 ∧
  Erdos1182.f 6 = 12 ∧ Erdos1182.f 7 = 16 ∧ Erdos1182.f 8 = 20 ∧
  Erdos1182.f 9 = 27 ∧ Erdos1182.f 10 = 33 ∧ Erdos1182.f 11 = 41 ∧ Erdos1182.f 12 = 49

theorem main : H1 → H2 → type_of% @Erdos1182.erdos_1182.variants.small_values := by
  intro h1 h2
  rcases h1 with ⟨h3, hrest⟩
  have hlower : 2 ≤ Erdos1182.F 3 := by
    have h := OMA.f_ge_pred (n := 3) (by omega)
    simpa using h
  exact ⟨⟨OMA.F_two, le_antisymm h3 hlower, hrest⟩, ⟨OMA.f_two, h2⟩⟩

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1
