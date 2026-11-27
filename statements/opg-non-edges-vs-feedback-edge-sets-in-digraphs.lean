import Mathlib

/-!
# Non-edges vs. feedback edge sets in digraphs

Source: https://www.openproblemgarden.org/op/non_edges_vs_feedback_edge_sets_in_digraphs
Credit: @LAPRAI

For a simple digraph `G`, let `γ(G)` be the number of unordered pairs of nonadjacent vertices
(non-edges) and `β(G)` the size of a smallest feedback edge set. Conjecture (Chudnovsky, Seymour,
Sullivan): if `G` has no directed cycles of length `≤ 3`, then `β(G) ≤ γ(G) / 2`.

## Encoding

* Digraphs are finite Mathlib `Digraph`s. A directed cycle of length `m ≥ 1` is an injective
  sequence `c 0, …, c (m-1)` with an arc from each `c i` to `c (i + 1 mod m)`; excluding cycles
  of length `1, 2, 3` excludes loops and opposite arcs, so `G` is simple.
* Two distinct vertices are nonadjacent if there is no arc between them in either direction.
  Each unordered non-edge is counted twice among ordered pairs, so `γ(G)` is half the number of
  ordered nonadjacent pairs `(u, v)`, `u ≠ v`.
* A feedback edge set is a set `F` of arcs whose deletion leaves no directed cycle.
  `β(G) ≤ γ(G)/2` means: some feedback edge set `F` has `|F| ≤ γ(G)/2`, i.e.
  `4 |F| ≤ #(ordered nonadjacent pairs)`.
-/

namespace OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs

/-- `c` is a directed cycle of `G` (of length `m ≥ 1`). -/
def IsDirectedCycle {V : Type} (G : Digraph V) {m : ℕ} (c : Fin m → V) : Prop :=
  1 ≤ m ∧ Function.Injective c ∧ ∀ i : Fin m, G.Adj (c i) (c (finRotate m i))

/-- `G` with the arcs of `F` deleted. -/
def deleteArcs {V : Type} (G : Digraph V) (F : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∧ (u, v) ∉ F

/-- The number of ordered pairs of distinct nonadjacent vertices (twice `γ(G)`). -/
def orderedNonEdges {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] :
    ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2 ∧ ¬ G.Adj p.2 p.1)).card

/-- **Chudnovsky–Seymour–Sullivan conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
    (∀ (m : ℕ) (c : Fin m → V), m ≤ 3 → ¬ IsDirectedCycle G c) →
    ∃ F : Finset (V × V), (∀ p ∈ F, G.Adj p.1 p.2) ∧
      (∀ (m : ℕ) (c : Fin m → V), ¬ IsDirectedCycle (deleteArcs G F) c) ∧
      4 * F.card ≤ orderedNonEdges G := by
  sorry

end OMA.S_opg_non_edges_vs_feedback_edge_sets_in_digraphs
