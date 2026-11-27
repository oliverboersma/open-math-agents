import Mathlib

/-!
# 2-accessibility of primes

Question of Bruce M. Landman and Aaron Robertson, recorded at
https://www.openproblemgarden.org/op/2_accessibility_of_primes.
Oscar Quester proves the positive answer in https://arxiv.org/abs/2606.00410.
Lean statement by @dk8827.
-/

namespace OMA.S_opg_2_accessibility_of_primes

/-- Every two-colouring of the positive integers admits monochromatic sequences of
any length at least two with prime gaps between consecutive terms. -/
theorem main :
    ∀ (colour : ℕ+ → Fin 2) (k : ℕ), 2 ≤ k →
      ∃ (x : Fin k → ℕ+) (c : Fin 2),
        (∀ i, colour (x i) = c) ∧
          ∀ (i : ℕ) (hi : i + 1 < k),
            ((x ⟨i + 1, hi⟩ : ℕ) - (x ⟨i, lt_trans (Nat.lt_succ_self i) hi⟩ : ℕ)).Prime := by
  sorry

end OMA.S_opg_2_accessibility_of_primes
