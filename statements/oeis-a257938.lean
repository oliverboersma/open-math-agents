import Mathlib

/-!
# A257938: Least positive integer k such that prime(k*n) - 1 = (prime(i*n)-1)*(prime(j*n)-1) for some integers 0 < i < j < k.

Source: https://oeis.org/A257938
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257938): `a(n)` exists for any `n > 0`, i.e. for every `n ≥ 1`
there are integers `0 < i < j < k` with `prime(k n) - 1 = (prime(i n) - 1)(prime(j n) - 1)`. In
general, for any nonzero integer `m` and positive integer `n`, the set
`{prime(k n) + m : k = 1, 2, 3, ...}` always contains three distinct elements `x, y` and `z` with
`x y = z`.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`; primes are
  at least 2, so `prime(t) - 1` in `ℕ` is the integer `prime(t) - 1`.
* The general statement is taken in `ℤ`; the elements `prime(k n) + m` are distinct exactly when
  their indices are distinct, since `prime` is strictly increasing.
* With this definition `a(1), ..., a(4)` = 6, 3, 8, 71, matching the data of A257938.
-/

namespace OMA.S_oeis_a257938

/-- The `t`-th prime, `prime 1 = 2`. -/
noncomputable def prime (t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (t - 1)

/-- Sun's conjectures of A257938. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ i j k : ℕ, 0 < i ∧ i < j ∧ j < k ∧
        prime (k * n) - 1 = (prime (i * n) - 1) * (prime (j * n) - 1)) ∧
      ∀ m : ℤ, m ≠ 0 → ∀ n : ℕ, 1 ≤ n → ∃ a b c : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ((prime (a * n) : ℤ) + m) * ((prime (b * n) : ℤ) + m) = (prime (c * n) : ℤ) + m := by
  sorry

end OMA.S_oeis_a257938
