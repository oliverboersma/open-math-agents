import Mathlib

/-!
# Partition of a cubic 3-connected graphs into paths of length 2.

Source: https://www.openproblemgarden.org/op/partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2
Credit: @LAPRAI

Problem: does every 3-connected cubic graph on `3k` vertices admit a partition into `k` paths of
length `2`? (This file states this main problem, not the more general packing question also on
the page.)

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; cubic means `IsRegularOfDegree 3`.
* `k`-connected (standard definition): more than `k` vertices, and deleting any set of fewer than
  `k` vertices leaves a connected graph. Mathlib has no vertex-connectivity notion, so it is
  defined here.
* A partition of the vertex set into `k` paths of length `2` (three vertices `a - b - c`, two
  edges) is a bijection `e : Fin k × Fin 3 ≃ V` such that, for each `i`, `e (i, 0)` is adjacent
  to `e (i, 1)` and `e (i, 1)` is adjacent to `e (i, 2)`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
set of fewer than `k` vertices. -/
def IsKConnected {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- The vertex set of `G` is partitioned into `k` paths of length `2`. -/
def HasP3Partition {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ e : Fin k × Fin 3 ≃ V, ∀ i : Fin k, G.Adj (e (i, 0)) (e (i, 1)) ∧ G.Adj (e (i, 1)) (e (i, 2))

/-- Every `3`-connected cubic graph on `3k` vertices has a partition into `k` paths of length `2`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    Fintype.card V = 3 * k → G.IsRegularOfDegree 3 → IsKConnected G 3 → HasP3Partition G k := by
  sorry

end OMA.S_opg_partition_of_a_cubic_3_connected_graphs_into_paths_of_length_2
