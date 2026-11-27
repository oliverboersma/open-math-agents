import Mathlib

/-!
# Triangle-packing vs triangle edge-transversal (Tuza's conjecture)

Source: https://www.openproblemgarden.org/op/triangle_packing_vs_triangle_edge_transversal

Conjecture (Tuza). If G has at most k edge-disjoint triangles, then there is a set of
2k edges whose deletion destroys every triangle.

Conventions:
* G is a finite simple graph (`SimpleGraph V` with `Fintype V`), as in Tuza's paper
  (Graphs Combin. 6 (1990)) cited on the page; k is a natural number.
* A triangle is a 3-vertex clique, `G.IsNClique 3 t` with `t : Finset V`. Two distinct
  triangles are edge-disjoint iff they share at most one vertex, so
  G has at most k edge-disjoint triangles  means: every family of triangles that pairwise
  share at most one vertex has at most k members.
* a set of 2k edges: a finite set S of unordered pairs with at most 2k elements. Pairs
  that are not edges change nothing under deletion, and deleting further edges keeps
  the graph triangle-free, so this is equivalent to deleting a set of exactly
  min(2k, |E(G)|) edges.
* deletion destroys every triangle: `G.deleteEdges S` contains no 3-clique,
  `(G.deleteEdges S).CliqueFree 3`.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_triangle_packing_vs_triangle_edge_transversal

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
      (∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
          (∀ t ∈ T, ∀ s ∈ T, t ≠ s → (t ∩ s).card ≤ 1) → T.card ≤ k) →
      ∃ S : Finset (Sym2 V), S.card ≤ 2 * k ∧
        (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3 := by
  sorry

end OMA.S_opg_triangle_packing_vs_triangle_edge_transversal
