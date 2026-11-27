import Mathlib

/-!
# A063793: a(n) = Min{ q prime | nextprime(q) - q - 1 = prime(n)}, or 0 if none exist.

Source: https://oeis.org/A063793
Credit: @divmxnd0x

Conjecture (stated in A063793): `a(n) > 0` for `n > 1`, i.e. for every odd prime `p`
(`p = prime(n)` with `n ≥ 2`) there is a prime `q` such that the next prime after `q` is
`q + p + 1` (a prime gap of length `p + 1`).

Formalization notes:
* "`nextprime(q) = q + p + 1`" is stated as: `q + p + 1` is prime and no prime lies strictly
  between `q` and `q + p + 1`.
* `prime(n)` with `n > 1` ranges exactly over the primes `p ≠ 2`.
* For `p = 3, 5, 7, 11, 13, 17` the least such `q` is 7, 23, 89, 199, 113, 523, matching the data of
  A063793.
-/

namespace OMA.S_oeis_a063793

/-- The conjecture of A063793: every odd prime `p` occurs as `nextprime(q) - q - 1` for some
prime `q`. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∃ q : ℕ, q.Prime ∧ (q + p + 1).Prime ∧ ∀ r : ℕ, q < r → r < q + p + 1 → ¬ r.Prime := by
  sorry

end OMA.S_oeis_a063793
