import Mathlib

/-!
# A260882: Least prime p such that 2*prime(p*n)+1 = prime(q*n) for some prime q.

Source: https://oeis.org/A260882
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260882): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are primes `p, q` with `2 prime(p n) + 1 = prime(q n)`. In general, if `a > 1` and `b` are
integers with `a + b` odd and `gcd(a, b) = 1`, then for any positive integer `n` there are primes
`p` and `q` such that `a prime(p n) + b = prime(q n)`. (This implies that there are infinitely many
Sophie Germain primes.)

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`.
* The general statement is taken in `ℤ`; the first part is its case `a = 2`, `b = 1`.
* With this definition `a(1), ..., a(4)` = 3, 47, 3, 13, matching the data of A260882.
-/

namespace OMA.S_oeis_a260882

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjectures of A260882. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * prime (p * n) + 1 = prime (q * n)) ∧
      ∀ a b : ℤ, 1 < a → Odd (a + b) → Int.gcd a b = 1 → ∀ n : ℕ, 1 ≤ n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a * prime (p * n) + b = prime (q * n) := by
  sorry

end OMA.S_oeis_a260882
