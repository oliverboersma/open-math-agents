import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1
import Mathlib

/-! The table of Brandt, Brinkmann and Harmuth (1998, Table 2) is an
extremum over connected graphs. For the lower certificates one need only
test complements of maximal triangle-free hosts. For the upper certificates
one need only exclude connected graphs with exactly one edge above the
tabulated number: a spanning tree extends to any intermediate edge count. -/
namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1

open SimpleGraph Erdos1182

/-- Dense witnesses embedded in every complement of a maximal triangle-free host. -/
def H1 : Prop := ∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard = q ∧
    ∀ C : SimpleGraph (Fin (2*n-1)), Maximal (fun B => B.CliqueFree 3) C → G ⊑ Cᶜ

/-- A triangle-free blocking host at the first forbidden edge count. -/
def H2 : Prop := ∀ k : Fin 9,
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard=q+1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ

lemma good_iff {n : ℕ} (hn : 2≤n) {G : SimpleGraph (Fin n)} (hc : G.Connected) :
    IsTriangleGood G ↔ ∀ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 → G ⊑ Cᶜ := by
  classical
  let S : Set ℕ := {m | ∀ C : SimpleGraph (Fin m), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ G ⊑ Cᶜ}
  change sInf S = 2*n-1 ↔ _
  constructor
  · intro h C ht
    have hne : S.Nonempty := by
      by_contra hs
      rw [Set.not_nonempty_iff_eq_empty.mp hs, Nat.sInf_empty] at h
      omega
    have hmem := Nat.sInf_mem hne
    rw [h] at hmem
    exact (hmem C).resolve_left (by simpa only [← completeGraph_eq_top,
      ← not_cliqueFree_iff_top_isContained] using not_not_intro ht)
  · intro h
    have hm : 2*n-1 ∈ S := by
      intro C
      by_cases ht : C.CliqueFree 3
      · exact Or.inr (h C ht)
      · exact Or.inl (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp ht)
    apply le_antisymm (Nat.sInf_le hm)
    apply le_csInf ⟨_,hm⟩
    intro m hmem
    by_contra! hlt
    obtain ⟨C, ht, hg⟩ := OMA.tree_ramsey_lower_witness n m hn hlt G hc
    exact (hmem C).elim ht hg

lemma intermediate {n q : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (hq : n-1≤q) (hm : q≤G.edgeSet.ncard) :
    ∃ B : SimpleGraph (Fin n), B≤G ∧ B.Connected ∧ B.edgeSet.ncard=q := by
  classical
  obtain ⟨T, hTG, ht⟩ := hc.exists_isTree_le
  have tcard := ht.card_edgeFinset
  rw [Fintype.card_fin] at tcard
  have hcard (D : SimpleGraph (Fin n)) : D.edgeSet.ncard = D.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  obtain ⟨W, hTW, hWG, hw⟩ := Finset.exists_subsuperset_card_eq (edgeFinset_mono hTG)
    (show T.edgeFinset.card≤q by omega) (by simpa only [hcard] using hm)
  let B := fromEdgeSet (W : Set (Sym2 (Fin n)))
  have wG : (W : Set (Sym2 (Fin n))) ⊆ G.edgeSet := fun e he => by
    have := hWG he
    simpa using this
  have eB : B.edgeSet = (W : Set (Sym2 (Fin n))) := by
    rw [show B.edgeSet = _ from edgeSet_fromEdgeSet (W : Set (Sym2 (Fin n)))]
    ext e
    exact ⟨And.left,fun he => ⟨he,G.not_isDiag_of_mem_edgeSet (wG he)⟩⟩
  have hTB : T ≤ B := by
    apply edgeSet_subset_edgeSet.mp
    rw [eB]
    intro e he
    exact hTW (by simpa using he)
  refine ⟨B, edgeSet_subset_edgeSet.mp (eB ▸ wG), ht.connected.mono hTB, ?_⟩
  simpa [eB] using hw

lemma table_entry (hlo : H1) (hhi : H2) (k : Fin 9) :
    f (k.val+4) = (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k := by
  classical
  let n := k.val+4
  let q := (![5,8,12,16,20,27,33,41,49] : Fin 9 → ℕ) k
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hq : n-1≤q+1 := by fin_cases k <;> decide
  obtain ⟨G,hc,he,hg⟩ := hlo k
  apply le_antisymm
  · unfold f
    apply csSup_le'
    rintro z ⟨B,hcB,hed,good⟩
    change z≤q
    by_contra! hz
    obtain ⟨T,hTB,hcT,hsize⟩ := intermediate hcB hq (by omega)
    obtain ⟨C,ht,hmiss⟩ := hhi k T hcT hsize
    exact hmiss (((good_iff hn hcB).mp good C ht).mono_left hTB)
  · unfold f
    apply le_csSup
    · refine ⟨n.choose 2, ?_⟩
      rintro z ⟨B,_,rfl,_⟩
      rw [Set.ncard_eq_toFinset_card']
      change B.edgeFinset.card ≤ n.choose 2
      simpa only [Fintype.card_fin] using B.card_edgeFinset_le_card_choose_two
    · refine ⟨G,hc,he,(good_iff hn hc).mpr ?_⟩
      intro C ht
      let S : Set (SimpleGraph (Fin (2*n-1))) := {B | B.CliqueFree 3}
      obtain ⟨B,hCB,hmax⟩ := S.toFinite.exists_le_maximal (show C∈S from ht)
      exact (hg B hmax).mono_right (compl_le_compl hCB)

lemma base : f 3 = 2 := by
  classical
  let C := cycleGraph 5
  have ban (G : SimpleGraph (Fin 5))
      (h : ∀ a b c, ¬ (G.Adj a b ∧ G.Adj a c ∧ G.Adj b c)) :
      ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G := by
    rintro ⟨e⟩
    exact h (e 0) (e 1) (e 2) ⟨e.toHom.map_rel (by decide),e.toHom.map_rel (by decide),
      e.toHom.map_rel (by decide)⟩
  have t : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ C := ban C (by decide +kernel)
  have u : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ Cᶜ := ban Cᶜ (by decide +kernel)
  have ecard (G : SimpleGraph (Fin 3)) : G.edgeSet.ncard = G.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  have topcard : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]; decide
  apply le_antisymm
  · unfold f
    apply csSup_le'
    rintro q ⟨G,hc,he,hg⟩
    by_contra! hq
    have hsub := edgeFinset_mono (show G ≤ ⊤ from le_top)
    have htop : G = ⊤ := edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub (by rw [topcard,←ecard,he]; omega))
    subst G
    exact u ((good_iff (by decide) hc).mp hg C (by
      by_contra h; exact t (by simpa only [completeGraph_eq_top] using (not_cliqueFree_iff_top_isContained 3).mp h)))
  · obtain ⟨T,_,hT⟩ := (connected_top : (⊤ : SimpleGraph (Fin 3)).Connected).exists_isTree_le
    unfold f
    apply le_csSup
    · refine ⟨3, ?_⟩
      rintro z ⟨G, _,rfl,_⟩
      simpa only [ecard,←topcard] using Finset.card_le_card (edgeFinset_mono (show G≤⊤ from le_top))
    · refine ⟨T,hT.connected,?_,OMA.tree_triangle_good 3 (by decide) T hT⟩
      have he := hT.card_edgeFinset
      rw [Fintype.card_fin] at he
      rw [ecard]; omega

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1.H2 := by
  intro hl hu
  exact ⟨base,table_entry hl hu 0,table_entry hl hu 1,table_entry hl hu 2,
    table_entry hl hu 3,table_entry hl hu 4,table_entry hl hu 5,table_entry hl hu 6,
    table_entry hl hu 7,table_entry hl hu 8⟩
end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1
