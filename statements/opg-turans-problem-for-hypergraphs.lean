import Mathlib

/-!
# Turán's problem for hypergraphs

Source: https://www.openproblemgarden.org/op/turans_problem_for_hypergraphs

Conjecture 1 (Turán). Every simple 3-uniform hypergraph on 3n vertices which contains no
complete 3-uniform hypergraph on four vertices has at most (1/2) n^2 (5n - 3) hyperedges.

Conjecture 2 (Turán). Every simple 3-uniform hypergraph on 2n vertices which contains no
complete 3-uniform hypergraph on five vertices has at most n^2 (n - 1) hyperedges.

The page states both conjectures; `main` is their conjunction.

Conventions:
* A simple 3-uniform hypergraph on m vertices is a set `F : Finset (Finset (Fin m))` of
  3-element subsets (simple: no repeated hyperedges, which a Finset guarantees).
* contains a complete 3-uniform hypergraph on four (five) vertices: some vertex set K with
  |K| = 4 (resp. 5) has all its 3-subsets in F, i.e. `K.powersetCard 3 ⊆ F`. Since F is
  3-uniform this is the same as containing a copy of K_4^(3) (resp. K_5^(3)).
* The bounds are stated without division: 2 |F| ≤ n^2 (5n - 3) and |F| ≤ n^2 (n - 1).
  The natural subtractions are harmless: for n ≥ 1 they are exact, and for n = 0 there
  are no vertices and F is empty.
* n ranges over all natural numbers, as on the page.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_turans_problem_for_hypergraphs

theorem main :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (3 * n)))),
      (∀ e ∈ F, e.card = 3) →
      (∀ K : Finset (Fin (3 * n)), K.card = 4 → ¬ K.powersetCard 3 ⊆ F) →
      2 * F.card ≤ n ^ 2 * (5 * n - 3)) ∧
    (∀ (n : ℕ) (F : Finset (Finset (Fin (2 * n)))),
      (∀ e ∈ F, e.card = 3) →
      (∀ K : Finset (Fin (2 * n)), K.card = 5 → ¬ K.powersetCard 3 ⊆ F) →
      F.card ≤ n ^ 2 * (n - 1)) := by
  sorry

end OMA.S_opg_turans_problem_for_hypergraphs
