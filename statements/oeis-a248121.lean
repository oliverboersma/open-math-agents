import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.PowerSeries.Basic

/-!
OEIS A248121: the two conjectures attributed to Chai Wah Wu (2022-08-03).
Source: https://oeis.org/A248121

The definition below is the original real-valued expression followed by
integer floor. The artificial zero-th coefficient is zero, so the ordinary
generating function starts at n = 1.

The generating-function identity is stated after multiplying by its
denominator, (1-X)^3 * (1+X+X^2). Its constant coefficient is one, so this
is exactly the rational generating-function conjecture, with no analytic
convergence assumption needed.

This statement-review file intentionally has one placeholder, in `main`.
The accompanying proof file proves the same proposition independently.
-/

namespace OMA.S_oeis_a248121

noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    ⌊1 / (1 / (n : ℝ) - Real.pi ^ 2 / 6 +
      ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2)⌋

theorem main :
    (∀ n : ℕ, 5 < n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 3) -
        2 * a (n - 4) + a (n - 5)) ∧
    ((1 - (PowerSeries.X : PowerSeries ℤ)) ^ 3 *
        (1 + PowerSeries.X + PowerSeries.X ^ 2) * PowerSeries.mk a =
      PowerSeries.X * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X + 2)) := by
  sorry

end OMA.S_oeis_a248121
