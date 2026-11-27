import Mathlib

/-!
# 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#1-factorization_conjecture
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): if `n` is odd or even
and `k ≥ n, n - 1`, respectively, then a `k`-regular graph with `2n` vertices is 1-factorable.
That is: if `n` is odd and `k ≥ n`, or `n` is even and `k ≥ n - 1`, then every `k`-regular simple
graph on `2n` vertices is 1-factorable.

A 1-factor of `G` is a perfect matching (a spanning 1-regular subgraph), and a 1-factorization of
`G` is a partition of the edge set of `G` into 1-factors.
-/

namespace OMA.S_wp_1_factorization_conjecture

open SimpleGraph

/-- `G` is 1-factorable: its edge set is partitioned by a family of perfect matchings of `G`,
i.e. the matchings are pairwise edge-disjoint and every edge of `G` lies in one of them. -/
def IsOneFactorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (ι : Type) (M : ι → G.Subgraph),
    (∀ i, (M i).IsPerfectMatching) ∧
    (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
    ∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet

theorem main :
    ∀ n k : ℕ, ((Odd n ∧ n ≤ k) ∨ (Even n ∧ n - 1 ≤ k)) →
      ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
        G.IsRegularOfDegree k → IsOneFactorable G := by
  sorry

end OMA.S_wp_1_factorization_conjecture
