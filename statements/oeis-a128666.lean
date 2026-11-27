import Mathlib

/-!
# A128666: Least generalized Wilson prime p such that p^2 divides (n-1)!(p-n)! - (-1)^n; or 0 if no such prime exists.

Source: https://oeis.org/A128666
Credit: @divmxnd0x

A generalized Wilson prime of order `n` is a prime `p` with `p^2 ∣ (n-1)! (p-n)! - (-1)^n`.

Conjecture (stated in A128666): a(n) > 0 for all `n`, i.e. for every `n ≥ 1` (the offset of the
sequence) there is a generalized Wilson prime of order `n`.

Formalization notes:
* The factorial `(p-n)!` only makes sense for `p ≥ n`, so the prime is required to satisfy
  `n ≤ p`; then `p - n` in `ℕ` is the integer `p - n`. The divisibility is stated in `ℤ` because of the
  sign `(-1)^n`.
* For `n = 1` this is the Wilson condition `p^2 ∣ (p-1)! + 1`.
* The least such prime for `n = 1, 2, 3, 5, 6, 7` is 5, 2, 7, 5, 11, 17, matching the data of
  A128666 (a(4) = 10429).
-/

namespace OMA.S_oeis_a128666

/-- `p` is a generalized Wilson prime of order `n`. -/
def IsGenWilsonPrime (n p : ℕ) : Prop :=
  p.Prime ∧ n ≤ p ∧
    ((p : ℤ) ^ 2 ∣ ((n - 1).factorial * (p - n).factorial : ℤ) - (-1) ^ n)

/-- The conjecture of A128666: for every `n ≥ 1` there is a generalized Wilson prime of order `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, IsGenWilsonPrime n p := by
  sorry

end OMA.S_oeis_a128666
