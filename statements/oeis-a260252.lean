import Mathlib

/-!
# A260252: Least prime p such that n = (prime(6*q)-1)/(prime(6*p)-1) for some prime q.

Source: https://oeis.org/A260252
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260252): Let `n` be any positive integer, and let `s` and `t`
belong to the set `{1, -1}`. Then each positive rational number `r` can be written as
`(prime(p n) + s)/(prime(q n) + t)` with `p` and `q` both prime, unless `n > r = 1` and
`{s, t} = {1, -1}`.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`; the quotient
  is taken in `ℚ` (its denominator `prime(q n) + t ≥ 1` is nonzero).
* The exception "`n > r = 1` and `{s, t} = {1, -1}`" is `1 < n ∧ r = 1 ∧ s ≠ t`.
* With this definition the least prime `p` with `n = (prime(6q) - 1)/(prime(6p) - 1)` for some prime
  `q` is 2, 3, 19, 2 for `n = 1, 3, 4, 5`, matching the data of A260252.
-/

namespace OMA.S_oeis_a260252

/-- Sun's conjecture of A260252. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ s t : ℤ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
    ∀ r : ℚ, 0 < r → ¬ (1 < n ∧ r = 1 ∧ s ≠ t) →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        r = ((Nat.nth Nat.Prime (p * n - 1) : ℚ) + s) / ((Nat.nth Nat.Prime (q * n - 1) : ℚ) + t) := by
  sorry

end OMA.S_oeis_a260252
