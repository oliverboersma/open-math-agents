import Mathlib

/-!
# A006519: Highest power of 2 dividing n

Source: https://oeis.org/A006519
Credit: @AkiRA-COM-FP

Formalizes Velin Yanev's OEIS A006519 conjecture (offset 1): for every `n >= 1`,
`a(n) = (1 / (sigma(2*n) / sigma(n) - 2) + 1) / 2`, where `a(n) = 2^(v_2(n))`.
-/

namespace OMA.S_oeis_a006519

/-- Highest power of `2` dividing `n`. -/
def a (n : ℕ) : ℕ :=
  2 ^ n.factorization 2

/-- For every `n >= 1`, `a(n) = (1 / (sigma(2*n) / sigma(n) - 2) + 1) / 2` in `ℚ`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) =
        (1 / (((ArithmeticFunction.sigma 1 (2 * n) : ℚ) /
          (ArithmeticFunction.sigma 1 n : ℚ)) - 2) + 1) / 2 := by
  sorry

end OMA.S_oeis_a006519
