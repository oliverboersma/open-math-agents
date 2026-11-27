import Mathlib

/-!
# A131418: Numbers n such that Sum_digits(n)=Sum_digits[n+Sum_digits(n)], with n>=0.

Source: https://oeis.org/A131418
Credit: @rorcores

The entry (offset 1, data 0, 9, 18, 27, 36, 45, 54, 63, 72, 81, 108, 117, ...) records in its
COMMENTS section:

  Conjecture: all terms are divisible by 9. - Harvey P. Dale, Mar 28 2019

Conventions:
* `Sum_digits(n)` is the sum of the decimal digits of `n` (A007953), here
  `(Nat.digits 10 n).sum`; for `n = 0` the digit list is empty and the sum is `0`.
* A term is a natural number `n ≥ 0` with `Sum_digits(n) = Sum_digits(n + Sum_digits(n))`, as in
  the name of the sequence (the entry's example: `315 -> 3+1+5 = 9 -> 315+9 = 324 -> 3+2+4 = 9`).
* The conjecture is about every term, so it is stated for every natural number `n` that is a term
  (`0` is a term and is divisible by 9).
-/

namespace OMA.S_oeis_a131418

/-- The sum of the decimal digits of `n` (A007953). -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- `n` is a term of A131418: `Sum_digits(n) = Sum_digits(n + Sum_digits(n))`. -/
def IsTerm (n : ℕ) : Prop := digitSum n = digitSum (n + digitSum n)

/-- Dale's conjecture: every term of A131418 is divisible by 9. -/
theorem main : ∀ n : ℕ, IsTerm n → 9 ∣ n := by
  sorry

end OMA.S_oeis_a131418
