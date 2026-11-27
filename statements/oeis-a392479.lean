import Mathlib

/-!
# A392479: Pairs of prime numbers (p,q), p minimal, such that prime(n) = p^3 - 2*q, or (0,0) if no such pair exists.

Source: https://oeis.org/A392479
Credit: @divmxnd0x

Conjecture (stated in A392479): Every prime number is of the form `p^3 - 2q` for some primes `p`
and `q`.

Formalization notes:
* The equation is taken in `ℤ`.
* With this definition the minimal `p` for the primes 2, 3, 5, 7, 11, 13 is 2, 5, 3, 5, 13, 3,
  matching the data of A392479 (pairs (2,3), (5,61), (3,11), (5,59), (13,1093), (3,7)).
-/

namespace OMA.S_oeis_a392479

/-- The conjecture of A392479: every prime is `p^3 - 2q` with `p, q` prime. -/
theorem main : ∀ r : ℕ, r.Prime → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (r : ℤ) = (p : ℤ) ^ 3 - 2 * q := by
  sorry

end OMA.S_oeis_a392479
