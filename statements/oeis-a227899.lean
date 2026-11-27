import Mathlib

/-!
# A227899: Number of primes p < n with 3*p - 4 and n^2 + (n - p)^2 both prime.

Source: https://oeis.org/A227899
Credit: @sntntHb

Data: 0, 0, 0, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3, ...

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` for all `n > 3`, i.e. for every
`n ≥ 4` there is a prime `p < n` such that `3p - 4` and `n^2 + (n - p)^2` are both prime.

Conventions: for a prime `p` we have `3p ≥ 4` and, since `p < n`, `n ≥ p`, so the natural-number
subtractions below are exact.
-/

namespace OMA.S_oeis_a227899

theorem main :
    ∀ n : ℕ, 3 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (3 * p - 4).Prime ∧
      (n ^ 2 + (n - p) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a227899
