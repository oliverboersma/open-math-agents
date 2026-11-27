import Mathlib

/-!
# A389525: Number of ways to write 2*n + 1 as prime(i^2) + prime(j^2) + prime(k^2) + 2*prime(m^2) with i >= j >= k >= m >= 1.

Source: https://oeis.org/A389525
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A389525): `a(n) > 0` for `n > 3200`, i.e. every odd number
`2n + 1` with `n > 3200` is `prime(i^2) + prime(j^2) + prime(k^2) + 2 prime(m^2)` for some
`i, j, k, m ≥ 1`. (Verified for `n ≤ 250000`.)

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`.
* The order condition `i ≥ j ≥ k ≥ m ≥ 1` of the counting function is kept as in the source.
* With this definition `a(0), ..., a(39)` agree with the data of A389525, and `a(n) > 0` for
  `3201 ≤ n < 5901`.
-/

namespace OMA.S_oeis_a389525

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjecture of A389525. -/
theorem main : ∀ n : ℕ, 3200 < n → ∃ i j k m : ℕ, 1 ≤ m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
    2 * n + 1 = prime (i ^ 2) + prime (j ^ 2) + prime (k ^ 2) + 2 * prime (m ^ 2) := by
  sorry

end OMA.S_oeis_a389525
