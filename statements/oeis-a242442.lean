import Mathlib

/-!
# A242442: Ways of writing n as a sum of a triangular number, an odd square and a pentagonal number

Source: https://oeis.org/A242442
Credit: @niclorusso

A242442(n) is the number of ways of writing n, a positive integer, as an unordered sum of a
triangular number (A000217), an odd square (A016754) and a pentagonal number (A000326).

Conjecture (in the comments of A242442, see Z.-W. Sun, Remark 1.2 (b)): only 18 cannot be so
represented.

Conventions:
* Triangular numbers are x(x+1)/2 with x >= 0 (A000217, starting 0, 1, 3, 6, ...).
* Odd squares are (2y+1)^2 with y >= 0 (A016754, starting 1, 9, 25, ...).
* Pentagonal numbers are z(3z-1)/2 with z >= 0 (A000326, starting 0, 1, 5, 12, ...). For z = 0
  the natural-number expression z * (3z - 1) / 2 is 0, as it should be.
* n ranges over the positive integers (offset 1); a(18) = 0 in the data of A242442.
* "only 18 cannot be so represented" is stated as an equivalence: a positive integer n is such a
  sum if and only if n /= 18.
-/

namespace OMA.S_oeis_a242442

/-- `n` is a triangular number plus an odd square plus a pentagonal number. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, x * (x + 1) / 2 + (2 * y + 1) ^ 2 + z * (3 * z - 1) / 2 = n

/-- Sun's conjecture recorded in A242442: every positive integer except 18 is the sum of a
triangular number, an odd square and a pentagonal number. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (IsRepresentable n ↔ n ≠ 18) := by
  sorry

end OMA.S_oeis_a242442
