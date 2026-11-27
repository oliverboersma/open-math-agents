import Mathlib

/-!
# A257856: Least positive integer k such that prime(k*n) - prime(k) is a square.

Source: https://oeis.org/A257856
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257856): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there is a positive integer `k` such that `prime(k n) - prime(k)` is a square. In general, every
rational number `r > 1` can be written as `m/n` with `m > n > 0` such that `prime(m) - prime(n)` is
a square.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`; it is
  increasing, so for `k n ≥ k` (resp. `m > n`) the subtraction in `ℕ` is the integer difference.
* `0` counts as a square (`a(1) = 1`, since `prime(1) - prime(1) = 0`).
* With this definition `a(1), ..., a(6)` = 1, 1, 5, 2, 1, 291, matching the data of A257856.
-/

namespace OMA.S_oeis_a257856

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- Sun's conjectures of A257856. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare (prime (k * n) - prime k)) ∧
      ∀ r : ℚ, 1 < r → ∃ m n : ℕ, 0 < n ∧ n < m ∧ r = (m : ℚ) / n ∧ IsSquare (prime m - prime n) := by
  sorry

end OMA.S_oeis_a257856
