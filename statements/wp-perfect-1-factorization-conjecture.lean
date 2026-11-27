import Mathlib

/-!
# Perfect 1-factorization conjecture

Source: https://en.wikipedia.org/wiki/Graph_factorization#Perfect_1-factorization
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): every complete graph on
an even number of vertices admits a perfect 1-factorization.

A 1-factorization of `G` is a partition of its edge set into 1-factors (perfect matchings). It is
*perfect* if the union of every two distinct 1-factors is a Hamiltonian cycle. Here the union of
two 1-factors is taken as a spanning subgraph of `G` on all vertices, and "is a Hamiltonian cycle"
is expressed by Mathlib's `SimpleGraph.IsHamiltonian` of that spanning subgraph (a union of two
disjoint perfect matchings is 2-regular, so containing a Hamiltonian cycle means being one).
-/

namespace OMA.S_wp_perfect_1_factorization_conjecture

open SimpleGraph

/-- A perfect 1-factorization of `G`: a family of perfect matchings of `G` that partitions the
edge set of `G`, such that the union of any two distinct members is a Hamiltonian cycle. -/
def HasPerfectOneFactorization {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ (ι : Type) (M : ι → G.Subgraph),
    (∀ i, (M i).IsPerfectMatching) ∧
    (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) ∧
    (∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edgeSet) ∧
    ∀ i j, i ≠ j → (M i ⊔ M j).spanningCoe.IsHamiltonian

theorem main : ∀ n : ℕ, HasPerfectOneFactorization (completeGraph (Fin (2 * n))) := by
  sorry

end OMA.S_wp_perfect_1_factorization_conjecture
