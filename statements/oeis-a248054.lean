import Mathlib

/-!
# A248054: Least positive integer m such that m + n divides sigma(m^2) + sigma(n^2).

Source: https://oeis.org/A248054
Credit: @sntntHb

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n)` exists for any `n > 0`, i.e. for every
positive integer `n` there is a positive integer `m` such that `m + n` divides
`sigma(m^2) + sigma(n^2)`, where `sigma` is the sum of the positive divisors.

Existence of some positive `m` is equivalent to existence of the least one.
-/

namespace OMA.S_oeis_a248054

theorem main : ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, 0 < m ∧
      (m + n) ∣ ArithmeticFunction.sigma 1 (m ^ 2) + ArithmeticFunction.sigma 1 (n ^ 2) := by
  sorry

end OMA.S_oeis_a248054
