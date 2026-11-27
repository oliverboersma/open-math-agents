import Mathlib

/-!
# A232465: a(n) = |{0 < k <= n/2: prime(k) + prime(n-k) - 1 is prime}|.

Source: https://oeis.org/A232465
Credit: @sntntHb

Data: 0, 1, 0, 1, 1, 0, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 5, 2, 5, 2, ...

Conjecture (i) (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` except for `n = 1, 3, 6`.

Conventions:
- `prime(j)` is the `j`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (j - 1)`.
- The offset is 1, so the terms are `a(n)` for `n ≥ 1`; `0 < k ≤ n/2` is written `0 < k ∧ 2k ≤ n`.
- The statement says the positive `n` with `a(n) = 0` are exactly `1, 3, 6`.
-/

namespace OMA.S_oeis_a232465

/-- `prime j` is the `j`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ k : ℕ, 0 < k ∧ 2 * k ≤ n ∧ (prime k + prime (n - k) - 1).Prime} =
      {1, 3, 6} := by
  sorry

end OMA.S_oeis_a232465
