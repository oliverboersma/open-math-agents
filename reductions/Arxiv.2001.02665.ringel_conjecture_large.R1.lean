import FormalConjectures.Arxiv.«2001.02665».RingelConjecture

-- Reduction Arxiv.2001.02665.ringel_conjecture_large.R1 of Ringel's Conjecture and Kotzig's Conjecture for large $n$ — ringel conjecture large
-- Credit: @Albin0903
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Strategy: the target has two halves, existence of 2n+1 pairwise edge-disjoint copies of T in
-- K_{2n+1} (the Montgomery-Pokrovskiy-Sudakov input, isolated as H1) and the fact that those
-- copies cover every edge. The covering half is NOT assumed: it is derived from H2 and H3 by
-- counting. The 2n+1 copies are pairwise edge-disjoint and each one has n edges (H2), so the
-- union of their edge sets has (2n+1)*n = Nat.choose (2n+1) 2 elements (H3), which is exactly the
-- number of edges of K_{2n+1}; a subset of a finite set with the same cardinality is the set, so
-- the supremum of the copies is the complete graph. No lemma of the upstream module is used.

namespace OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1

open SimpleGraph

/-- H1, the deep input: for all large n, any tree with n edges packs into K_{2n+1}, that is, it
has 2n+1 pairwise edge-disjoint copies on the vertex set Fin (2n+1). -/
def H1 : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type} [Finite V] (T : SimpleGraph V),
    T.IsTree → T.edgeSet.ncard = n →
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet)

/-- H2, invariance of the edge count under an injective vertex map: a copy of a tree with n edges
still has n edges. -/
def H2 : Prop :=
  ∀ (n : ℕ) {V : Type} [Finite V] (T : SimpleGraph V) (g : V ↪ Fin (2 * n + 1)),
    (T.map g).edgeSet.ncard = T.edgeSet.ncard

/-- H3, the arithmetic of the edge count of a complete graph of odd order: (2n+1) trees with n
edges cover as many edges as K_{2n+1} has. -/
def H3 : Prop := ∀ n : ℕ, (2 * n + 1) * n = Nat.choose (2 * n + 1) 2

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2001.02665».ringel_conjecture_large := by
  intro h1 h2 h3
  simp only [H1, H2, H3] at h1 h2 h3
  filter_upwards [h1] with n hn
  intro V _ T hT hcard
  obtain ⟨f, hf⟩ := hn T hT hcard
  refine ⟨f, hf, ?_⟩
  -- every copy has n edges
  have hcopy : ∀ i : Fin (2 * n + 1), (T.map (f i)).edgeSet.ncard = n := by
    intro i
    rw [h2 n T (f i), hcard]
  have hfin : ∀ i : Fin (2 * n + 1), ((T.map (f i)).edgeSet).Finite :=
    fun i => Set.finite_univ.subset (Set.subset_univ _)
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin (2 * n + 1) => (T.map (f i)).edgeSet) :=
    hf
  -- the edge set of the supremum is the union of the edge sets of the copies
  have hsup : (⨆ i, T.map (f i)).edgeSet = ⋃ i, (T.map (f i)).edgeSet := SimpleGraph.edgeSet_iSup
  -- counting the union: (2n+1) disjoint copies of n edges
  have hleft : ((⨆ i, T.map (f i)).edgeSet).ncard = (2 * n + 1) * n := by
    rw [hsup, Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype,
      Finset.sum_const_nat (fun i _ => hcopy i), Finset.card_univ, Fintype.card_fin]
  -- counting the complete graph: Nat.choose (2n+1) 2 edges
  have htop : ((⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet).ncard
      = Nat.choose (2 * n + 1) 2 := by
    rw [SimpleGraph.edgeSet_top, Set.ncard_eq_toFinset_card', Set.toFinset_card,
      Sym2.card_diagSet_compl, Fintype.card_fin]
  rw [← SimpleGraph.edgeSet_inj]
  have hsub : (⨆ i, T.map (f i)).edgeSet ⊆ (⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet :=
    SimpleGraph.edgeSet_mono le_top
  have heq : ((⨆ i, T.map (f i)).edgeSet).ncard
      = ((⊤ : SimpleGraph (Fin (2 * n + 1))).edgeSet).ncard := by
    rw [hleft, htop, h3 n]
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq heq.symm)

end OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1
