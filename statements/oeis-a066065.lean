import Mathlib

/-!
# A066065: a(n) = smallest prime q such that in decimal notation the concatenation prime(n)q yields a prime ( = A066064(n)).

Source: https://oeis.org/A066065
Credit: @divmxnd0x

Conjecture (stated in A066065): `a(k) < prime(k)` for `k > 2`, i.e. for every prime `p = prime(k)`
with `k > 2` (equivalently `p ≥ 5`) there is a prime `q < p` such that the decimal concatenation
of `p` and `q` is prime.

Formalization notes:
* The decimal concatenation of `a` and `b` is `a * 10^(number of digits of b) + b`.
* `prime(k)` with `k > 2` ranges exactly over the primes `p ≥ 5`.
* For `k = 1, ..., 15` the least prime `q` with `concat (prime k) q` prime is 3, 7, 3, 3, 3, 7,
  3, 3, 3, 3, 3, 3, 11, 3, 23, matching the data of A066065.
-/

namespace OMA.S_oeis_a066065

/-- Decimal concatenation of `a` and `b`. -/
def concat (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.digits 10 b).length + b

/-- The conjecture of A066065: for every prime `p ≥ 5` some prime `q < p` makes the concatenation
`p q` prime. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∃ q : ℕ, q.Prime ∧ q < p ∧ (concat p q).Prime := by
  sorry

end OMA.S_oeis_a066065
