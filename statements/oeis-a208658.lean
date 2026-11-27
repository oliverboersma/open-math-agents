import Mathlib

/-!
# The row-sum formula and generating function for OEIS A208658

Source: https://oeis.org/A208658
Triangle source: https://oeis.org/A208657
Credit: @Heart-galaxy

A208658 is the sum of row n of A208657, indexed from n=1. Its source program
sums n*binomial(n,k)-binomial(n-1,k-1) for k=1,...,n; reversing this order
produces the same row sum. We use k+1 to express exactly these indices.
The integer-valued sum preserves the ordinary subtraction in that formula.
The empty sum a(0)=0 is the zero constant term of the source generating function.

Barker conjectured the closed formula and ordinary generating function on
March 20, 2012; Spezia confirmed both on November 19, 2023. The closed formula
is stated for every original positive index. Its two terms are merely reordered.
The generating function equality has its denominator multiplied through:
(1-X)^2*(1-2*X)^2 has constant coefficient 1 and hence is a unit, so this is
exactly equivalent to X^2*(4-7*X+2*X^2)/((1-X)^2*(1-2*X)^2).
-/

namespace OMA.S_oeis_a208658

def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n,
  ((n : ℤ) * (Nat.choose n (k+1) : ℤ) - (Nat.choose (n-1) k : ℤ))

def F : PowerSeries ℤ := PowerSeries.mk a

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = (n : ℤ)*((2 : ℤ)^n-1) - (2 : ℤ)^(n-1)) ∧
    ((1-PowerSeries.X)^2*(1-2*PowerSeries.X)^2*F =
      (4 : PowerSeries ℤ)*PowerSeries.X^2 - 7*PowerSeries.X^3 + 2*PowerSeries.X^4) := by
  sorry

end OMA.S_oeis_a208658
