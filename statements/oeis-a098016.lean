import Mathlib

/-!
# A098016: Indices x such that (1/4)(prime(x+1) + prime(x)) is prime

Source: https://oeis.org/A098016
Credit: @AkiRA-COM-FP

Formalizes the OEIS A098016 conjecture: for all `x`, the midpoint
`(1/2)(prime(x+1) + prime(x))` of two consecutive primes is never prime.
-/

namespace OMA.S_oeis_a098016

/-- The average of two consecutive primes is never a prime number. -/
theorem main :
    ∀ x : ℕ, ¬ ∃ q : ℕ, q.Prime ∧
      2 * q = Nat.nth Nat.Prime x + Nat.nth Nat.Prime (x + 1) := by
  sorry

end OMA.S_oeis_a098016
