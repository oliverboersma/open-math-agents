import Mathlib

/-!
# A260080: Least positive integer k such that prime(k*n)^2 - 2 = prime(i*n)*prime(j*n) for some integers 0 < i < j.

Source: https://oeis.org/A260080
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260080): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are positive integers `k` and `0 < i < j` with `prime(k n)^2 - 2 = prime(i n) prime(j n)`.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; since
  `prime(t)^2 ≥ 4`, `prime(t) ^ 2 - 2` in `ℕ` is the integer `prime(t)^2 - 2`.
* With this definition `a(1), ..., a(4)` = 5, 18, 18, 9, matching the data of A260080.
-/

namespace OMA.S_oeis_a260080

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjecture: for every `n ≥ 1` some `prime(k n)^2 - 2` is `prime(i n) prime(j n)` with
`0 < i < j`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k i j : ℕ, 1 ≤ k ∧ 0 < i ∧ i < j ∧
    prime (k * n) ^ 2 - 2 = prime (i * n) * prime (j * n) := by
  sorry

end OMA.S_oeis_a260080
