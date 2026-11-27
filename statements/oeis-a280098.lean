import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The divisor-sum integrality conjecture in OEIS A280098

Robert G. Wilson v (December 25, 2016) conjectured that the positive
integers k for which the sum of the divisors of k*n - 1, divided by k, is
an integer for every positive n are exactly 1, 3, 4, 6, 8, 12, 24.

Source: https://oeis.org/A280098 (OEIS Foundation, CC BY-SA 4.0).

The quotient is integral exactly when k divides the sum of divisors.
Mathlib's sigma 1 gives that sum. For k = n = 1 its argument is zero,
where Mathlib assigns the value zero. Since k = 1 divides every integer,
this convention has no effect on the classification.
-/

namespace OMA.S_oeis_a280098

theorem main : ∀ k : ℕ, 0 < k →
    ((∀ n : ℕ, 0 < n → k ∣ ArithmeticFunction.sigma 1 (k * n - 1)) ↔
      k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 12 ∨ k = 24) := by
  sorry

end OMA.S_oeis_a280098
