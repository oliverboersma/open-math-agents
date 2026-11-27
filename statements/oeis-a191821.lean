import Mathlib

/-!
# A191821: a(n) = n*(2^n - n + 1) + 2^(n-1)*(n^2 - 3*n + 2).

Source: https://oeis.org/A191821
Credit: @bIackr0se

Conjecture (Harvey P. Dale): the generating function is
`-((2 (-1+6 x-19 x^2+31 x^3-22 x^4+4 x^5))/(1-3 x+2 x^2)^3)`.

Formalization notes:
* The sequence is defined by the formula in its name, computed in `ℚ`
  (data: 2, 6, 26, 100, 332, 994, ... from n = 1). The exponent `n - 1` is natural-number
  subtraction; only `n >= 1` is used, where it is exact.
* The entry has offset 1, so the conjectured generating function is `Sum_{n >= 0} a(n+1) x^n`
  (its constant term is `2 = a(1)`). The power series below is that series.
* The identity is stated over `ℚ` with the denominator cleared:
  `A * (1 - 3x + 2x^2)^3 = -(2 (-1 + 6x - 19x^2 + 31x^3 - 22x^4 + 4x^5))`.
-/

namespace OMA.S_oeis_a191821

/-- `a(n) = n (2^n - n + 1) + 2^(n-1) (n^2 - 3n + 2)`. -/
def a (n : ℕ) : ℚ :=
  (n : ℚ) * (2 ^ n - n + 1) + 2 ^ (n - 1) * ((n : ℚ) ^ 2 - 3 * n + 2)

/-- The generating function of `a(1), a(2), ...` is
`-2 (-1 + 6x - 19x^2 + 31x^3 - 22x^4 + 4x^5) / (1 - 3x + 2x^2)^3`. -/
theorem main :
    PowerSeries.mk (fun n => a (n + 1)) *
        (1 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2) ^ 3 =
      -(2 * (-1 + 6 * PowerSeries.X - 19 * PowerSeries.X ^ 2 + 31 * PowerSeries.X ^ 3 -
        22 * PowerSeries.X ^ 4 + 4 * (PowerSeries.X : PowerSeries ℚ) ^ 5)) := by
  sorry

end OMA.S_oeis_a191821
