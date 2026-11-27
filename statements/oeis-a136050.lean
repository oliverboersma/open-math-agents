import Mathlib

/-!
# A136050: Sum of digits of product of twin primes A037074.

Source: https://oeis.org/A136050
Credit: @rorcores

The entry (offset 1, data 6, 8, 8, 8, 26, 17, 26, 17, 8, 17, ...) records in its COMMENTS section:

  Conjecture: except for the initial term, each term is one less than a multiple of 9.
  - Harvey P. Dale, Dec 02 2016

Conventions:
* A037074 lists the products `p * (p + 2)` of the pairs of twin primes `(p, p + 2)` in increasing
  order: 15, 35, 143, 323, 899, ... . The terms of A136050 are the sums of the decimal digits of
  these products, `(Nat.digits 10 (p * (p + 2))).sum`: 6, 8, 8, 8, 26, ... .
* The initial term `6` comes from the first pair of twin primes `(3, 5)` (the entry's example: the
  product of the first twin primes is 15 = 3 * 5, with digit sum 6). The products are strictly
  increasing in `p`, so the terms other than the initial one are exactly the digit sums for the
  twin prime pairs `(p, p + 2)` with `p ≠ 3`.
* "One less than a multiple of 9" for a term `s` is stated as `9 ∣ s + 1`.
-/

namespace OMA.S_oeis_a136050

/-- The term of A136050 attached to the twin prime pair `(p, p + 2)`: the sum of the decimal
digits of `p * (p + 2)`. -/
def term (p : ℕ) : ℕ := (Nat.digits 10 (p * (p + 2))).sum

/-- Dale's conjecture: for every pair of twin primes `(p, p + 2)` other than `(3, 5)`, the sum of
the digits of `p * (p + 2)` is one less than a multiple of 9. -/
theorem main : ∀ p : ℕ, p.Prime → (p + 2).Prime → p ≠ 3 → 9 ∣ term p + 1 := by
  sorry

end OMA.S_oeis_a136050
