import Mathlib

/-!
# A260082: Least positive integer k such that (prime(k*n)-1)^2 = (prime(i*n)-1)*(prime(j*n)-1) for some integers 0 < i < j.

Source: https://oeis.org/A260082
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260082): `a(n)` exists for any `n > 0`. In general, for any
nonzero integer `m` and positive integer `n` there are distinct positive integers `i, j, k` such
that `(prime(i n) + m)(prime(j n) + m) = (prime(k n) + m)^2`.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; primes are
  at least 2, so `prime(t) - 1` in `ℕ` is the integer `prime(t) - 1`.
* The general statement is taken in `ℤ`.
* With this definition `a(1), ..., a(4)` = 2, 2, 2, 21, matching the data of A260082.
-/

namespace OMA.S_oeis_a260082

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjectures of A260082. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 0 < i ∧ i < j ∧ 0 < k ∧
        (prime (k * n) - 1) ^ 2 = (prime (i * n) - 1) * (prime (j * n) - 1)) ∧
      ∀ m : ℤ, m ≠ 0 → ∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ 1 ≤ k ∧
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        ((prime (i * n) : ℤ) + m) * ((prime (j * n) : ℤ) + m) = ((prime (k * n) : ℤ) + m) ^ 2 := by
  sorry

end OMA.S_oeis_a260082
