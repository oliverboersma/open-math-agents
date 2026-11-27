import Mathlib

/-!
# A306362: Prime numbers in A317298

Source: https://oeis.org/A306362
Credit: @xor2k

Formalizes the OEIS A306362 conjecture: Except the first term a(1) = 3, all the other terms do
not end with 3.

Conventions:
* A317298 (offset 0) is `b(n) = (1/2)*(1 + (-1)^n + 2*n + 4*n^2)`, defined here as `b` on `ℕ`
  with values in `ℤ`; the numerator is always even, so integer division `/ 2` is exact;
* the terms of A306362 are exactly the prime values of `b`, so the conjecture is stated for
  every index `n` with `b n` prime (primality in `ℤ` via `Prime`; all values are positive);
* the first term `3` is excluded by the hypothesis `b n ≠ 3`;
* ends with 3 means last decimal digit 3, i.e. `b n % 10 = 3` (values are positive).
-/

namespace OMA.S_oeis_a306362

/-- A317298: `b(n) = (1 + (-1)^n + 2*n + 4*n^2) / 2`. -/
def b (n : ℕ) : ℤ :=
  (1 + (-1) ^ n + 2 * n + 4 * n ^ 2) / 2

/-- Every prime term of A317298 other than `3` does not end with the digit `3`. -/
theorem main :
    ∀ n : ℕ, Prime (b n) → b n ≠ 3 → b n % 10 ≠ 3 := by
  sorry

end OMA.S_oeis_a306362
