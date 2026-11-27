import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Real.Basic

/-!
# Chvátal's toughness conjecture

Source: https://en.wikipedia.org/wiki/Graph_toughness
Credit: @ArjunCodess

Chvátal asks whether some fixed positive toughness guarantees a Hamiltonian cycle.
The conjecture uses finite simple graphs with at least three vertices, the minimum
order of a graph containing a cycle.
-/

namespace OMA.S_wp_chvatal_s_toughness_conjecture

/-- Deleting vertices to leave more than one component costs at least `t` vertices per component. -/
def IsTough {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : Prop :=
  ∀ s : Finset (Fin n),
    let components := Nat.card (G.induce {v | v ∉ s}).ConnectedComponent
    1 < components → t * (components : ℝ) ≤ (s.card : ℝ)

theorem main :
    ∃ t : ℝ, 0 < t ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ G : SimpleGraph (Fin n), IsTough G t → G.IsHamiltonian := by
  sorry

end OMA.S_wp_chvatal_s_toughness_conjecture
