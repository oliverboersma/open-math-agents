import Mathlib

/-!
# A034496: Sum of n-th powers of divisors of 8

Source: https://oeis.org/A034496
Credit: @AkiRA-COM-FP

Formalizes Artur Jasinski's OEIS A034496 conjecture (offset 0): no term in the sequence
`a(n) = Sum_{d | 8} d^n` is prime.
-/

namespace OMA.S_oeis_a034496

/-- Sum of `n`-th powers of the positive divisors of `8`. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ (8 : ℕ).divisors, d ^ n

/-- No term of A034496 is prime. -/
theorem main :
    ∀ n : ℕ, ¬ (a n).Prime := by
  sorry

end OMA.S_oeis_a034496
