import Mathlib

/-!
# MathOverflow 475837

Source: https://mathoverflow.net/questions/475837
-/

namespace OMA.S_mo_475837



theorem main : ∀ s : ℕ → ℕ, StrictMono s →
    (∀ m : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ j < m, a + j * d ∈ Set.range s) →
    ∀ L : ℝ, 1 < L → ∃ k : ℕ, (s (k + 1) : ℝ) < L * s k := by
  sorry

end OMA.S_mo_475837
