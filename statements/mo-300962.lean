import Mathlib

/-!
# Two triangular numbers and two powers of five

Zhi-Wei Sun posed this question on MathOverflow.
https://mathoverflow.net/questions/300962
-/

namespace OMA.S_mo_300962

def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

theorem main : ∀ n : ℕ, 1 < n → ∃ a b c d : ℕ,
    n = triangular a + triangular b + 5 ^ c + 5 ^ d := by
  sorry

end OMA.S_mo_300962
