import Mathlib

/-!
# A257663: Least positive integer k such that prime(k*n) - prime(k+n) is a square.

Source: https://oeis.org/A257663
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257663): `a(n)` exists for any `n > 1`, i.e. for every `n ≥ 2`
there is a positive integer `k` such that `prime(k n) - prime(k + n)` is a square. Also, for any
`n > 0` there is a number `k > 0` such that `prime(k n) + prime(k + n)` is a square.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* The difference is taken in `ℤ`, so a negative difference is never a square.
* With this definition `a(2), ..., a(5)` = 2, 24, 57, 32, matching the data of A257663.
-/

namespace OMA.S_oeis_a257663

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- Sun's conjectures of A257663. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare ((prime (k * n) : ℤ) - prime (k + n))) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare (prime (k * n) + prime (k + n)) := by
  sorry

end OMA.S_oeis_a257663
