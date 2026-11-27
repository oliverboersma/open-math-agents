import Mathlib

/-!
# Erdős Problem 149

Source: https://www.erdosproblems.com/149
Credit: @Ciphore

The strong chromatic index of a graph is the least number of color classes in an edge
coloring whose color classes are strongly independent: two distinct edges of the same color
have disjoint endpoint sets, and no endpoint of one is adjacent to an endpoint of the other.
-/

namespace OMA.S_erdos_149

/-- A strong edge coloring with colors in `Fin k`: equally colored distinct edges are
strongly independent. -/
def IsStrongEdgeColoring {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : Sym2 V → Fin k) : Prop :=
  ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → c e = c f →
    ∀ v w : V, v ∈ e → w ∈ f → v ≠ w ∧ ¬ G.Adj v w

/-- The graph admits a strong edge coloring with at most `k` colors. -/
def HasStrongEdgeColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Sym2 V → Fin k, IsStrongEdgeColoring G c

/-- Erdős and Nešetřil's strong chromatic index conjecture. -/
theorem main : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Δ : ℕ),
    (∀ v : V, (G.neighborSet v).ncard ≤ Δ) →
    ∃ k : ℕ, HasStrongEdgeColoring G k ∧ (k : ℝ) ≤ (5 / 4 : ℝ) * Δ ^ 2 := by
  sorry

end OMA.S_erdos_149
