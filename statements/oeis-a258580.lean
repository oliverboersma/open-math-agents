import Mathlib

/-!
# A258580: Least positive integer k such that (prime(j*n)+prime(k*n))/2 = prime(i*n)^2 for some integers i > 0 and 0 < j < k.

Source: https://oeis.org/A258580
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A258580): `a(n)` exists for any `n > 0`. In general, for any
positive integers `a, m` and `n`, there are integers `i, j, k > 0` with `i > j` such that
`(prime(i n) + prime(j n))/2` (or `(prime(i n) - prime(j n))/2`) is equal to `a prime(k n)^m`.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`.
* Halves are cleared: `(x ± y)/2 = z` is stated as `x ± y = 2z`, which is the intended equality of
  integers. The difference is taken in `ℤ`.
* The general conjecture is stated for both readings (sum and difference), each with its own
  `i, j, k`.
* With this definition `a(1), ..., a(4)` = 3, 9, 4, 127, matching the data of A258580.
-/

namespace OMA.S_oeis_a258580

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjectures of A258580. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 0 < i ∧ 0 < j ∧ j < k ∧
        prime (j * n) + prime (k * n) = 2 * prime (i * n) ^ 2) ∧
      ∀ a m n : ℕ, 0 < a → 0 < m → 0 < n →
        (∃ i j k : ℕ, 0 < j ∧ j < i ∧ 0 < k ∧
          prime (i * n) + prime (j * n) = 2 * (a * prime (k * n) ^ m)) ∧
        (∃ i j k : ℕ, 0 < j ∧ j < i ∧ 0 < k ∧
          (prime (i * n) : ℤ) - prime (j * n) = 2 * (a * prime (k * n) ^ m)) := by
  sorry

end OMA.S_oeis_a258580
