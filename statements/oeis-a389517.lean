import Mathlib

/-!
# A389517: Number of ways to write 2*n as an unordered sum of four primes with square indices.

Source: https://oeis.org/A389517
Credit: @divmxnd0x

A prime with square index has the form `prime(k^2)` (A011757).

Conjecture (Zhi-Wei Sun, stated in A389517): `a(n) > 0` for any integer `n > 3286`, i.e. any even
number greater than 6572 is a sum of four terms from A011757.

Formalization notes:
* `prime(i)` is the `i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`; square
  indices are `k^2` with `k ≥ 1`.
* "Unordered" does not affect existence.
* With this definition `a(1), ..., a(40)` agree with the data of A389517, `a(3286) = 0`, and
  `a(n) > 0` for `3287 ≤ n < 5887`.
-/

namespace OMA.S_oeis_a389517

/-- The `i`-th prime, `prime 1 = 2`. -/
noncomputable def prime (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- Sun's conjecture: every `2n` with `n > 3286` is a sum of four primes with square indices. -/
theorem main : ∀ n : ℕ, 3286 < n → ∃ a b c d : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d ∧
    2 * n = prime (a ^ 2) + prime (b ^ 2) + prime (c ^ 2) + prime (d ^ 2) := by
  sorry

end OMA.S_oeis_a389517
