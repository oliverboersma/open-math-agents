import Mathlib

/-!
# A260208: Least prime p such that 2p*n+1 = prime(q*n) for some prime q.

Source: https://oeis.org/A260208
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260208): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p` and `q` with `2 p n + 1 = prime(q n)`. In general, if `a > 0` is even and `b`
is 1 or -1, then for any positive integer `n` there are primes `p` and `q` such that
`a p n + b = prime(q n)`.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* The general statement is taken in `ℤ` (because of `b = -1`); the case `a = 2`, `b = 1` is the
  first part, which is stated separately as in the source.
* With this definition `a(1), ..., a(5)` = 2, 3, 2, 107, 271, matching the data of A260208.
-/

namespace OMA.S_oeis_a260208

/-- Sun's conjectures of A260208. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * p * n + 1 = Nat.nth Nat.Prime (q * n - 1)) ∧
      ∀ a : ℕ, 0 < a → Even a → ∀ b : ℤ, (b = 1 ∨ b = -1) → ∀ n : ℕ, 1 ≤ n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
          (a : ℤ) * p * n + b = (Nat.nth Nat.Prime (q * n - 1) : ℤ) := by
  sorry

end OMA.S_oeis_a260208
