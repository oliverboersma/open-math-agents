import Mathlib

/-!
# A134119: the empirical generating function of floor(n^2/10) - floor((n-1)^2/10)

Source: https://oeis.org/A134119
Credit: @ivillar

A134119 (offset 0) is a(n) = floor(n^2/10) - floor((n-1)^2/10), with data
0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, ...
Colin Barker (Aug 08 2013) gave the empirical g.f. x^4*(x^4+1) / (x^11 - x^10 - x + 1);
Sela Fried (Dec 08 2024) notes that this conjectured g.f. is correct.

Formalization: the floors are taken of rational numbers, with n - 1 computed in ℚ, so at
n = 0 the second term is floor(1/10) = 0 and a(0) = 0 as in the data. The g.f. identity is
stated over the formal power series ring ℤ⟦X⟧, cross-multiplied by the denominator
x^11 - x^10 - x + 1 (which has constant coefficient 1, so it is invertible there).
-/

namespace OMA.S_oeis_a134119

open PowerSeries

/-- A134119: a(n) = floor(n^2/10) - floor((n-1)^2/10). -/
def a (n : ℕ) : ℤ := ⌊((n : ℚ) ^ 2) / 10⌋ - ⌊(((n : ℚ) - 1) ^ 2) / 10⌋

/-- Barker's empirical g.f. x^4*(x^4+1) / (x^11 - x^10 - x + 1), cross-multiplied. -/
theorem main :
    PowerSeries.mk a * (X ^ 11 - X ^ 10 - X + 1 : PowerSeries ℤ) = X ^ 4 * (X ^ 4 + 1) := by
  sorry

end OMA.S_oeis_a134119
