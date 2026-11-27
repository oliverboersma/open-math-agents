import Mathlib

/-!
# A258803: Least prime p such that n = (prime(q)-1)/(prime(p)-1) for some prime q.

Source: https://oeis.org/A258803
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A258803): `a(n)` exists for any `n > 0`. Moreover, for any
integers `s` and `t` with `|s| = |t| = 1`, each positive rational number `r` can be written as
`(prime(p) + s)/(prime(q) + t)` with `p` and `q` both prime.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* `a(n)` exists iff `prime(q) - 1 = n (prime(p) - 1)` for some primes `p, q` (primes are at least 2,
  so the subtractions in `ℕ` are exact). The second part is taken in `ℚ` (the denominator
  `prime(q) + t ≥ 1` is nonzero).
* With this definition `a(1), ..., a(6)` = 2, 2, 5, 3, 2, 13, matching the data of A258803.
-/

namespace OMA.S_oeis_a258803

/-- Sun's conjectures of A258803. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
        Nat.nth Nat.Prime (q - 1) - 1 = n * (Nat.nth Nat.Prime (p - 1) - 1)) ∧
      ∀ s t : ℤ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) → ∀ r : ℚ, 0 < r →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          r = ((Nat.nth Nat.Prime (p - 1) : ℚ) + s) / ((Nat.nth Nat.Prime (q - 1) : ℚ) + t) := by
  sorry

end OMA.S_oeis_a258803
