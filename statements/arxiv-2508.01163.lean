import Mathlib

/-!
# A new conjecture on the inertia of graphs

Source: https://arxiv.org/abs/2508.01163 (Akbari, Elphick, Kumar, Pragada)
Credit: @Genbox

Let `G` be a graph with adjacency matrix `A(G)`. Conjecture: `2 n⁺(G) ≤ n⁻(G) (n⁻(G) + 1)`, where
`n⁺(G)` and `n⁻(G)` denote the number of positive and negative eigenvalues of `A(G)` (counted with
multiplicity). Graphs are finite simple graphs, here on the vertex set `Fin n`.
-/

namespace OMA.S_arxiv_2508_01163

/-- Number of positive eigenvalues (with multiplicity) of the adjacency matrix of `G`. -/
noncomputable def nPos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun i => 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i).card

/-- Number of negative eigenvalues (with multiplicity) of the adjacency matrix of `G`. -/
noncomputable def nNeg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter fun i => (G.isHermitian_adjMatrix ℝ).eigenvalues i < 0).card

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    2 * nPos G ≤ nNeg G * (nNeg G + 1) := by
  sorry

end OMA.S_arxiv_2508_01163
