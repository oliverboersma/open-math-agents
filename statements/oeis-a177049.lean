import Mathlib

/-!
# OEIS A177049: numerator of (3n+1)(3n+2)/4

Source: https://oeis.org/A177049
Credit: @Heart-galaxy

The sequence has offset 0. It is defined exactly as the numerator of the stated
rational expression, using `Rat.num`; no recurrence or closed numerator formula
is built into this definition.

R. J. Mathar conjectured the order-nine recurrence and rational generating function
on December 12, 2010. Charles R Greathouse IV confirmed them on February 8, 2012.
Both claims are retained as this known result. The order-nine recurrence starts
at n=9, using the nine initial terms at indices 0 through 8.
The source's minus sign and denominator (x-1)^3 are combined into (1-x)^3;
its generating function is expressed after multiplication by the denominator.
-/

namespace OMA.S_oeis_a177049
def a (n : ℕ) : ℤ := (((3 * (n : ℚ) + 1) * (3 * n + 2) / 4) : ℚ).num

open PowerSeries

noncomputable def generating : PowerSeries ℤ := PowerSeries.mk a
noncomputable def denominator : PowerSeries ℤ := (1 - X) ^ 3 * (X ^ 2 + 1) ^ 3
noncomputable def numerator : PowerSeries ℤ :=
  (X ^ 2 + C 4 * X + 1) *
    (X ^ 6 - C 2 * X ^ 5 + C 12 * X ^ 4 - C 13 * X ^ 3 + C 12 * X ^ 2 - C 2 * X + 1)

theorem main :
    (∀ n : ℕ, 9 ≤ n → a n = 3 * a (n - 1) - 6 * a (n - 2) + 10 * a (n - 3) -
      12 * a (n - 4) + 12 * a (n - 5) - 10 * a (n - 6) + 6 * a (n - 7) -
      3 * a (n - 8) + a (n - 9)) ∧ denominator * generating = numerator  := by
  sorry

end OMA.S_oeis_a177049

