import Mathlib

/-!
# Matchings extend to Hamiltonian cycles in hypercubes

Source: https://www.openproblemgarden.org/op/matchings_extends_to_hamilton_cycles_in_hypercubes
Credit: @LAPRAI

*Reference:* F. Ruskey and C. D. Savage, SIAM J. Discrete Math. 6 (1993), 152–166 (page 19,
question 3).

Question (Ruskey–Savage): does every matching of the hypercube `Q_d` extend to a Hamiltonian
cycle?

## Encoding

* `Q_d` has vertex set `Fin d → Bool`, two vertices being adjacent iff they differ in exactly
  one coordinate (Hamming distance `1`). Mathlib has no hypercube graph, so it is defined here.
* `d ≥ 2`: `Q_0` and `Q_1` have no Hamiltonian cycle, and the question concerns hypercubes that
  have one.
* A matching is a Mathlib subgraph `M` of `Q_d` with `M.IsMatching` (any set of pairwise disjoint
  edges); it *extends to* a Hamiltonian cycle `p` if every edge of `M` is an edge of `p`.
* The source asks a yes/no question without conjecturing an answer; `main` states the answer
  yes, and a disproof would answer no.
-/

namespace OMA.S_opg_matchings_extends_to_hamilton_cycles_in_hypercubes

/-- The `d`-dimensional hypercube graph `Q_d`. -/
def hypercube (d : ℕ) : SimpleGraph (Fin d → Bool) :=
  SimpleGraph.fromRel (fun x y => hammingDist x y = 1)

/-- Every matching of `Q_d` (`d ≥ 2`) extends to a Hamiltonian cycle. -/
theorem main : ∀ d : ℕ, 2 ≤ d → ∀ M : (hypercube d).Subgraph, M.IsMatching →
    ∃ (a : Fin d → Bool) (p : (hypercube d).Walk a a), p.IsHamiltonianCycle ∧
      ∀ e ∈ M.edgeSet, e ∈ p.edges := by
  sorry

end OMA.S_opg_matchings_extends_to_hamilton_cycles_in_hypercubes
