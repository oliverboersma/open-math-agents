import Mathlib

/-!
# A274536: a(n) = 6 * sigma(n)

Source: https://oeis.org/A274536
Credit: @xor2k

Formalizes the OEIS A274536 conjecture (offset 1):
a(n) = sigma(5*n) = A283118(n) iff n is not a multiple of 5.

Conventions: the sequence has offset 1, so the statement quantifies over `n : ℕ` with
`0 < n`. `sigma` is the sum-of-divisors function, Mathlib's `ArithmeticFunction.sigma 1`
(A000203). A283118(n) is by definition `sigma(5*n)`, so only the equation
`6 * sigma(n) = sigma(5*n)` is stated. Not being a multiple of 5 is `¬ 5 ∣ n`.
-/

namespace OMA.S_oeis_a274536

/-- `a(n) = 6 * sigma(n)`. -/
def a (n : ℕ) : ℕ :=
  6 * ArithmeticFunction.sigma 1 n

/-- For every `n ≥ 1`, `a(n) = sigma(5*n)` holds if and only if `5` does not divide `n`. -/
theorem main :
    ∀ n : ℕ, 0 < n → (a n = ArithmeticFunction.sigma 1 (5 * n) ↔ ¬ 5 ∣ n) := by
  sorry

end OMA.S_oeis_a274536
