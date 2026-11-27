import Mathlib

/-!
# A387991: Number of ways to write n as i*prime(i) + j*prime(j) + k*prime(k) + m*prime(m) with 1 <= i <= j <= k <= m.

Source: https://oeis.org/A387991
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A387991): `a(n) > 0` for all `n ≥ 3070`. In other words, any
integer `n ≥ 3070` is a sum of four terms of A033286 (the numbers `i prime(i)`, `i ≥ 1`). This has
been verified for `n ≤ 2*10^5`.

Formalization notes:
* `prime(i)` is the `i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`.
* The order condition `i ≤ j ≤ k ≤ m` of the counting function does not affect existence; it is
  kept as in the source.
* With this definition `a(1), ..., a(50)` agree with the data of A387991, `a(3069) = 0`, and
  `a(n) > 0` for `3070 ≤ n < 6970`.
-/

namespace OMA.S_oeis_a387991

/-- The `i`-th prime, `prime 1 = 2`. -/
noncomputable def prime (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- Sun's conjecture: every `n ≥ 3070` is `i prime(i) + j prime(j) + k prime(k) + m prime(m)` with
`1 ≤ i ≤ j ≤ k ≤ m`. -/
theorem main : ∀ n : ℕ, 3070 ≤ n → ∃ i j k m : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ m ∧
    n = i * prime i + j * prime j + k * prime k + m * prime m := by
  sorry

end OMA.S_oeis_a387991
