import Mathlib

/-!
# A260078: Least positive integer k such that prime(k*n)-1+(prime(h*n)-1) = prime(i*n)-1 and prime(k*n)-1-(prime(h*n)-1) = prime(j*n)-1 for some positive integers h,i,j.

Source: https://oeis.org/A260078
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260078): `a(n)` exists for any `n > 0`. In general, if `m` and
`n > 0` are integers with `gcd(6, m) = 1`, then the set `{prime(k n) + m : k = 1, 2, 3, ...}`
contains two distinct elements `x` and `y` with `x + y` and `x - y` also in the set.

Formalization notes:
* `prime(t)` is the `t`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (t - 1)`.
* The statement is taken in `ℤ`. The first part (existence of `a(n)`) is the case `m = -1` of the
  general statement: with `x = prime(k n) - 1` and `y = prime(h n) - 1`.
* With this definition `a(1), ..., a(4)` = 3, 3, 15, 5, matching the data of A260078.
-/

namespace OMA.S_oeis_a260078

/-- The set `{prime(k n) + m : k ≥ 1}`. -/
def S (m : ℤ) (n : ℕ) : Set ℤ :=
  {x | ∃ k : ℕ, 1 ≤ k ∧ x = (Nat.nth Nat.Prime (k * n - 1) : ℤ) + m}

/-- Sun's conjectures of A260078. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ x ∈ S (-1) n, ∃ y ∈ S (-1) n, x + y ∈ S (-1) n ∧ x - y ∈ S (-1) n) ∧
      ∀ m : ℤ, Int.gcd 6 m = 1 → ∀ n : ℕ, 1 ≤ n →
        ∃ x ∈ S m n, ∃ y ∈ S m n, x ≠ y ∧ x + y ∈ S m n ∧ x - y ∈ S m n := by
  sorry

end OMA.S_oeis_a260078
