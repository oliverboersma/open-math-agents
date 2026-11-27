import Mathlib

/-!
# A260120: Least integer k > 0 such that (prime(k*n)-1)^2 = prime(j*n)-1 for some j > 0.

Source: https://oeis.org/A260120
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260120): `a(n)` exists for any `n > 0`. In general, if
`a, b, c` and `m` are integers with `a > 0`, `gcd(a, b, c - m) = 1` and
`c ≡ (a + b + 1)(m + 1) (mod 2)` such that `b^2 - 4a(c - m)` is not a square and
`gcd(a m - b, b^2 + b - a c - 1)` is not divisible by 3, then for any positive integer `n` there are
two elements `x` and `y` of the set `{prime(k n) + m : k = 1, 2, 3, ...}` with `a x^2 + b x + c = y`.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; primes are
  at least 2, so `prime(t) - 1` in `ℕ` is the integer `prime(t) - 1`. The general statement is
  taken in `ℤ`.
* The first part is the case `a = 1`, `b = 0`, `c = 0`, `m = -1` of the general statement.
* With this definition `a(1), ..., a(4)` = 1, 2, 14, 1, matching the data of A260120.
-/

namespace OMA.S_oeis_a260120

/-- The set `{prime(k n) + m : k ≥ 1}`. -/
def S (m : ℤ) (n : ℕ) : Set ℤ :=
  {x | ∃ k : ℕ, 1 ≤ k ∧ x = (Nat.nth Nat.Prime (k * n - 1) : ℤ) + m}

/-- Sun's conjectures of A260120. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k j : ℕ, 0 < k ∧ 0 < j ∧
        (Nat.nth Nat.Prime (k * n - 1) - 1) ^ 2 = Nat.nth Nat.Prime (j * n - 1) - 1) ∧
      ∀ a b c m : ℤ, 0 < a → Int.gcd (Int.gcd a b) (c - m) = 1 →
        c % 2 = ((a + b + 1) * (m + 1)) % 2 → ¬ IsSquare (b ^ 2 - 4 * a * (c - m)) →
        ¬ (3 : ℤ) ∣ (Int.gcd (a * m - b) (b ^ 2 + b - a * c - 1) : ℤ) →
        ∀ n : ℕ, 1 ≤ n → ∃ x ∈ S m n, ∃ y ∈ S m n, a * x ^ 2 + b * x + c = y := by
  sorry

end OMA.S_oeis_a260120
