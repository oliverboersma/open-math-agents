import Mathlib

/-!
# Erdős Problem 993

Source: https://www.erdosproblems.com/993
Credit: @Ciphore

Unimodality of the independent-set sequence of a forest.
-/

namespace OMA.S_erdos_993

/-- Number of independent vertex sets of size `k`. -/
noncomputable def independentCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  {s : Finset V | s.card = k ∧ ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ G.Adj u v}.ncard

/-- The independent-set sequence of every forest is unimodal. -/
theorem main : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.IsAcyclic → ∃ m : ℕ,
      (∀ k : ℕ, k < m → independentCount G k ≤ independentCount G (k+1)) ∧
      (∀ k : ℕ, m ≤ k → independentCount G (k+1) ≤ independentCount G k) := by
  sorry

end OMA.S_erdos_993
