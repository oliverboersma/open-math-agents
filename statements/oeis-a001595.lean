import Mathlib

/-!
# A001595: a(n) = a(n-1) + a(n-2) + 1, with a(0) = a(1) = 1.

Source: https://oeis.org/A001595
Credit: @canneyi

The entry gives the generating function
`(1 - x + x^2)/(1 - 2x + x^3) = 2/(1 - x - x^2) - 1/(1 - x)`,
conjectured by Simon Plouffe in his 1992 dissertation.

Formalization notes:
* Offset 0, as in the entry (data: 1, 1, 3, 5, 9, 15, 25, 41, 67, ...).
* Both forms of the generating function are stated as identities of formal power series over `ℤ`
  with the denominators cleared: `A * (1 - 2x + x^3) = 1 - x + x^2` for the first form, and
  `A * ((1 - x - x^2) * (1 - x)) = 2 * (1 - x) - (1 - x - x^2)` for the second, where `A` is the
  ordinary generating function of the sequence.
-/

namespace OMA.S_oeis_a001595

/-- The sequence `a(n) = a(n-1) + a(n-2) + 1` with `a(0) = a(1) = 1`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => a (n + 1) + a n + 1

/-- The ordinary generating function of `a` is `(1 - x + x^2)/(1 - 2x + x^3)`, which equals
`2/(1 - x - x^2) - 1/(1 - x)`. -/
theorem main :
    (PowerSeries.mk a * (1 - 2 * (PowerSeries.X : PowerSeries ℤ) + PowerSeries.X ^ 3) =
      1 - PowerSeries.X + PowerSeries.X ^ 2) ∧
    (PowerSeries.mk a *
        ((1 - (PowerSeries.X : PowerSeries ℤ) - PowerSeries.X ^ 2) * (1 - PowerSeries.X)) =
      2 * (1 - PowerSeries.X) - (1 - PowerSeries.X - PowerSeries.X ^ 2)) := by
  sorry

end OMA.S_oeis_a001595
