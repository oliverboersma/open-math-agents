import Mathlib

/-!
# A303691: a(n) is the number of 3-smooth numbers k such that prime(n)-k is also a prime number

Source: https://oeis.org/A303691
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n)>0 for all n>1.

Conventions: the 3-smooth numbers (A003586) are the numbers `2^i * 3^j` with `i, j ≥ 0`
(so `1` is included). The primes `prime(n)` with `n > 1` are exactly the primes `p > 2`.
`a(n) > 0` means some 3-smooth `k < p` has `p - k` prime.
-/

namespace OMA.S_oeis_a303691

/-- Every prime `p > 2` is the sum of a prime and a 3-smooth number. -/
theorem main : ∀ p : ℕ, p.Prime → 2 < p →
    ∃ i j : ℕ, 2 ^ i * 3 ^ j < p ∧ (p - 2 ^ i * 3 ^ j).Prime := by
  sorry

end OMA.S_oeis_a303691
