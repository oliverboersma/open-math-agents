import Mathlib

/-!
# Extremal minimal bipartite matching covered graphs

Source: https://arxiv.org/abs/2404.06445 (Mallik, Diwan, Kothari), Section 8, Conjecture 8.9
("Main Conjecture"): in a minimal k-extendable bipartite graph,
|V_{k+1}| ≥ 2/(2k-1) · (m - n + 2k).
Credit: @Genbox

Definitions as in Section 8 of the source (following Plummer): for a positive integer `k`, a
connected graph of order at least `2k+2` is `k`-extendable if it has a matching of size `k` and each
such matching extends to a perfect matching; it is minimal if deleting any edge results in a graph
that is not `k`-extendable. `n` = number of vertices, `m` = number of edges, `V_{k+1}` = set of
vertices of degree `k+1`.
-/

namespace OMA.S_arxiv_2404_06445

open SimpleGraph

/-- A connected graph of order at least `2k+2` is `k`-extendable if it has a matching of size `k`
and every matching of size `k` extends to a perfect matching. -/
def IsKExtendable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.Connected ∧ 2 * k + 2 ≤ Nat.card V ∧
    (∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k) ∧
    ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard = k →
      ∃ P : G.Subgraph, P.IsPerfectMatching ∧ M ≤ P

/-- Minimal `k`-extendable: `k`-extendable, and deleting any edge destroys `k`-extendability. -/
def IsMinimalKExtendable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsKExtendable G k ∧ ∀ e ∈ G.edgeSet, ¬ IsKExtendable (G.deleteEdges {e}) k

theorem main : ∀ k : ℕ, 1 ≤ k → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsBipartite → IsMinimalKExtendable G k →
    (2 : ℝ) / (2 * (k : ℝ) - 1) * ((G.edgeSet.ncard : ℝ) - (Fintype.card V : ℝ) + 2 * (k : ℝ)) ≤
      ({v : V | (G.neighborSet v).ncard = k + 1}.ncard : ℝ) := by
  sorry

end OMA.S_arxiv_2404_06445
