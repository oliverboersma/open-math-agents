import Mathlib

/-!
# A158013: 100*a(n)+13 and 100*a(n)+27 are consecutive primes, i.e., a prime gap 14.

Source: https://oeis.org/A158013
Credit: @LAPRAI

Formalizes the OEIS comment: It is conjectured that sequence is infinite.

Conventions: consecutive primes means both are prime and no number strictly between them is prime.
-/

namespace OMA.S_oeis_a158013

/-- There are infinitely many `a` such that `100a + 13` and `100a + 27` are consecutive primes. -/
theorem main : {a : ℕ | (100 * a + 13).Prime ∧ (100 * a + 27).Prime ∧
    ∀ m : ℕ, 100 * a + 13 < m → m < 100 * a + 27 → ¬ m.Prime}.Infinite := by
  sorry

end OMA.S_oeis_a158013
