import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1
-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @jagong-cmu
-- H2 := ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →     2 ≤ Fintype.card α →     T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber


/-!
# Step H2 of the reduction R1 for WOWII Conjecture 372 (regularized)

Every tree of order at least two has vertex cover number at most twice its total
domination number. Root the tree at `r`. Take a minimum total dominating set `D`.
Let `P` be the vertices outside `D` with a child outside `D`. Then `D ∪ P` is a vertex
cover, and an injection sends each `u ∈ P` to a grandchild of `u` in `D`.
-/

namespace OMA.WOW372H2

open SimpleGraph

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma parent_unique {T : SimpleGraph α} (hT : T.IsTree) (r : α) {a b w : α}
    (ha : T.Adj a w) (hb : T.Adj b w) (hda : T.dist r w = T.dist r a + 1)
    (hdb : T.dist r w = T.dist r b + 1) : a = b := by
  obtain ⟨q, hq, hql⟩ := (hT.connected r w).exists_path_of_dist
  have key : ∀ c, T.Adj c w → T.dist r w = T.dist r c + 1 → c = q.penultimate := by
    intro c hc hdc
    by_cases hcs : c ∈ q.support
    · exact hT.isAcyclic.eq_penultimate_of_adj_end hq hc.symm hcs
    · exfalso
      obtain ⟨p, hp, hpl⟩ := (hT.connected r c).exists_path_of_dist
      have hw : w ∈ p.support :=
        hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hc hcs
      have h1 := SimpleGraph.dist_le (p.takeUntil w hw)
      have h2 := p.length_takeUntil_le_length hw
      omega
  rw [key a ha hda, key b hb hdb]

theorem h2 (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  classical
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hne : ∃ n, ∃ D : Finset α, T.IsTotalNDominatingSet n D := by
    refine ⟨Finset.univ.card, Finset.univ, ⟨?_, rfl⟩⟩
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p, hp, _⟩ := (hT.connected v w).exists_path_of_dist
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, by simp, h⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hDt : T.IsTotalDominating (D : Set α) := hD.1
  have hDc : D.card = T.totalDominationNumber := hD.2
  obtain ⟨r⟩ := hT.connected.nonempty
  let P : Finset α := Finset.univ.filter
    (fun u => u ∉ D ∧ ∃ v, T.Adj u v ∧ T.dist r v = T.dist r u + 1 ∧ v ∉ D)
  have hcover : T.IsVertexCover ((D ∪ P : Finset α) : Set α) := by
    intro u v huv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    by_cases hu : u ∈ D
    · exact Or.inl (Or.inl hu)
    by_cases hv : v ∈ D
    · exact Or.inr (Or.inl hv)
    rcases hT.dist_eq_dist_add_one_of_adj r huv with h | h
    · right; right
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv, u, huv.symm, h, hu⟩
    · left; right
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hu, v, huv, h, hv⟩
  have hf : ∀ u ∈ P, ∃ x, x ∈ D ∧ ∃ v, T.Adj u v ∧ T.dist r v = T.dist r u + 1 ∧
      T.Adj v x ∧ T.dist r x = T.dist r v + 1 := by
    intro u hu
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨huD, v, huv, hdv, hvD⟩ := hu
    obtain ⟨x, hxD, hvx⟩ := hDt v
    refine ⟨x, hxD, v, huv, hdv, hvx, ?_⟩
    rcases hT.dist_eq_dist_add_one_of_adj r hvx with h | h
    · exfalso
      have hxu : x = u := parent_unique hT r hvx.symm huv h hdv
      exact huD (hxu ▸ hxD)
    · exact h
  choose! f hfD hf2 using hf
  have hP : P.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      exact hfD u hu
    · intro u1 hu1 u2 hu2 heq
      obtain ⟨v1, h11, h12, h13, h14⟩ := hf2 u1 hu1
      obtain ⟨v2, h21, h22, h23, h24⟩ := hf2 u2 hu2
      rw [heq] at h13 h14
      have hv : v1 = v2 := parent_unique hT r h13 h23 h14 h24
      subst hv
      exact parent_unique hT r h11 h21 h12 h22
  have hle : T.vertexCoverNum ≤ ((D ∪ P).card : ℕ∞) := by
    have := hcover.vertexCoverNum_le
    rwa [Set.encard_coe_eq_coe_finsetCard] at this
  have h3 : T.vertexCoverNum.toNat ≤ (D ∪ P).card := ENat.toNat_le_of_le_natCast hle
  have h4 := Finset.card_union_le D P
  omega

end OMA.WOW372H2

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 :=
  fun _ _ _ T hT hn => OMA.WOW372H2.h2 T hT hn
