import Mathlib

/-!
# A257926: Least positive integer k such that prime(k*n)+2 = prime(i*n)*prime(j*n) for some 0 < i < j.

Source: https://oeis.org/A257926
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257926): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are positive integers `k` and `0 < i < j` with `prime(k n) + 2 = prime(i n) prime(j n)`. This
is much stronger than Chen's result that there are infinitely many Chen primes.

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* With this definition `a(1), ..., a(5)` = 6, 4, 10, 8, 451, matching the data of A257926.
-/

namespace OMA.S_oeis_a257926

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- Sun's conjecture: for every `n ≥ 1` there are `k ≥ 1` and `0 < i < j` with
`prime(k n) + 2 = prime(i n) * prime(j n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k i j : ℕ, 1 ≤ k ∧ 0 < i ∧ i < j ∧
    prime (k * n) + 2 = prime (i * n) * prime (j * n) := by
  sorry

end OMA.S_oeis_a257926
