import Mathlib

/-!
# A282410: a(n) = binomial(2*p-1, p-1) modulo p^5, where p = prime(n).

Source: https://oeis.org/A282410
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) != 1 for all n (cf. McIntosh, 1995, p. 387).

Conventions: offset 1, so `prime(n)` ranges over all primes `p`; `a(n) != 1` means `binomial(2p-1, p-1) mod p^5 ≠ 1`.
-/

namespace OMA.S_oeis_a282410

/-- For every prime `p`, `binomial(2p-1, p-1) mod p^5 ≠ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → Nat.choose (2 * p - 1) (p - 1) % p ^ 5 ≠ 1 := by
  sorry

end OMA.S_oeis_a282410
