import Mathlib

/-!
# A182079: the empirical generating function of floor(n*floor((n-1)/2)/3)

Source: https://oeis.org/A182079
Credit: @ivillar

A182079 (offset 0) is a(n) = floor(n*floor((n-1)/2)/3), with data
0, 0, 0, 1, 1, 3, 4, 7, 8, 12, 13, 18, 20, ...
Colin Barker (Nov 18 2012) gave the empirical g.f.
x^3*(x^4+x^3+x^2+1)/((1-x)^3*(1+x)^2*(x^2-x+1)*(x^2+x+1));
Sela Fried (Dec 27 2024) notes that this conjectured g.f. is correct.

Formalization: both floors are taken of rational numbers, with n - 1 computed in ℚ (so at
n = 0 the inner floor is floor(-1/2) = -1 and a(0) = 0, as in the data). The g.f. identity is
stated over the formal power series ring ℤ⟦X⟧, cross-multiplied by the denominator, whose
constant coefficient is 1.
-/

namespace OMA.S_oeis_a182079

open PowerSeries

/-- A182079: a(n) = floor(n*floor((n-1)/2)/3). -/
def a (n : ℕ) : ℤ := ⌊((n : ℚ) * (⌊((n : ℚ) - 1) / 2⌋ : ℚ)) / 3⌋

/-- Barker's empirical g.f., cross-multiplied by its denominator. -/
theorem main :
    PowerSeries.mk a *
        ((1 - X) ^ 3 * (1 + X) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) =
      X ^ 3 * (X ^ 4 + X ^ 3 + X ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a182079
