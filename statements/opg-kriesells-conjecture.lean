import Mathlib

/-!
# Kriesell's Conjecture

Source: https://www.openproblemgarden.org/op/kriesells_conjecture
Credit: @LAPRAI

*Reference:* J. A. Bondy and U. S. R. Murty, Graph Theory, GTM 244, Springer, 2008 (unsolved
problem 22).

Let `G` be a graph and let `T ⊆ V(G)` such that for any pair `u, v ∈ T` there are `2k`
edge-disjoint paths from `u` to `v` in `G`. Then `G` contains `k` edge-disjoint trees, each of
which contains `T`.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s. This loses nothing for multigraphs: subdividing every
  edge once turns a multigraph into a simple graph with the same edge-disjoint `u`–`v` paths, and
  `k` edge-disjoint trees containing `T` in the subdivision give `k` in the original graph after
  pruning leaves outside `T` (and conversely).
* `T` is nonempty (for `T = ∅` on the empty graph there is no tree at all, and the statement is
  only meaningful for nonempty terminal sets).
* `2k` edge-disjoint paths from `u` to `v`: `2k` walks from `u` to `v`, each a path, with
  pairwise disjoint edge lists.
* A tree of `G` containing `T` is a subgraph `H` of `G` whose underlying graph `H.coe` is a tree
  (`SimpleGraph.IsTree`) and whose vertex set contains `T`; the `k` trees have pairwise disjoint
  edge sets.
-/

namespace OMA.S_opg_kriesells_conjecture

/-- There are `m` pairwise edge-disjoint paths from `u` to `v` in `G`. -/
def HasEdgeDisjointPaths {V : Type} (G : SimpleGraph V) (u v : V) (m : ℕ) : Prop :=
  ∃ P : Fin m → G.Walk u v, (∀ i, (P i).IsPath) ∧
    ∀ i j, i ≠ j → List.Disjoint (P i).edges (P j).edges

/-- **Kriesell's conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (T : Set V) (k : ℕ), T.Nonempty →
    (∀ u ∈ T, ∀ v ∈ T, HasEdgeDisjointPaths G u v (2 * k)) →
    ∃ H : Fin k → G.Subgraph, (∀ i, (H i).coe.IsTree ∧ T ⊆ (H i).verts) ∧
      ∀ i j, i ≠ j → Disjoint (H i).edgeSet (H j).edgeSet := by
  sorry

end OMA.S_opg_kriesells_conjecture
