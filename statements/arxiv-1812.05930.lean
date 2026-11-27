import Mathlib

/-!
# Unweighted induced matching: integrality gap and approximation

Baste, Fürst and Rautenbach, arXiv:1812.05930, abstract and program (P).
Credit: @ryansolves

We state the two asymptotic claims in the catalog excerpt. A common additive
constant suffices, by taking the maximum of the constants for the two claims.
The integer optimum is expressed by comparison with feasible induced matchings.
This also covers edgeless graphs without dividing by zero.
-/

namespace OMA.S_arxiv_1812_05930

variable {n : ℕ}

noncomputable def edges (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical exact G.edgeFinset

noncomputable def degreeBound (G : SimpleGraph (Fin n)) : ℕ := by
  classical exact G.maxDegree

/-- The union of the two endpoint stars of an edge, including the edge itself. -/
noncomputable def incidentBlock (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :=
  (edges G).filter fun f => e.toFinset ∩ f.toFinset ≠ ∅

/-- The zero-one constraints of program (2), in edge-set form. -/
def inducedMatching (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  M ⊆ edges G ∧ ∀ e ∈ edges G, ((incidentBlock G e) ∩ M).card ≤ 1

def feasible (G : SimpleGraph (Fin n)) (x : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e ∈ edges G, 0 ≤ x e) ∧ ∀ e ∈ edges G, ∑ f ∈ incidentBlock G e, x f ≤ 1

/-- Explicit row-major adjacency matrices for both input and output.
The square length determines the vertex count, including isolated vertices. -/
def matrixBits (entry : Fin n → Fin n → Bool) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map (entry u)

noncomputable def graphBits (G : SimpleGraph (Fin n)) : List Bool := by
  classical exact matrixBits fun u v => decide (G.Adj u v)

def matchingBits (M : Finset (Sym2 (Fin n))) : List Bool :=
  matrixBits fun u v => decide (s(u, v) ∈ M)

theorem main :
    ∃ (C : ℝ) (algorithm : List Bool → List Bool), 0 ≤ C ∧
      Nonempty (Turing.TM2ComputableInPolyTime id id algorithm) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        let factor := (5 / 8 : ℝ) * degreeBound G + C
        (∀ x : Sym2 (Fin n) → ℝ, feasible G x →
          ∃ M, inducedMatching G M ∧ (∑ e ∈ edges G, x e) ≤ factor * M.card) ∧
        (∃ M, inducedMatching G M ∧ algorithm (graphBits G) = matchingBits M ∧
          ∀ N, inducedMatching G N → (N.card : ℝ) ≤ factor * M.card) := by
  sorry

end OMA.S_arxiv_1812_05930
