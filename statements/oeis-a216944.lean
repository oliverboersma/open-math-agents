import Mathlib

/-!
# A216944: The least odd prime p for which the n-th prime can be written as 3p + q - 3 for some odd prime q

Source: https://oeis.org/A216944
Credit: @niclorusso

Conjecture (in the comments of A216944): Any prime >= 11 can be written this way, i.e. as
3p + q - 3 with p and q odd primes.

Conventions:
* p and q are odd primes (primes other than 2). Since p >= 3, 3p + q - 3 >= q > 0, so the
  natural-number subtraction is exact.
-/

namespace OMA.S_oeis_a216944

/-- The conjecture on A216944: every prime `r >= 11` is `3p + q - 3` for some odd primes `p`, `q`. -/
theorem main : ∀ r : ℕ, r.Prime → 11 ≤ r →
    ∃ p q : ℕ, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ 3 * p + q - 3 = r := by
  sorry

end OMA.S_oeis_a216944
