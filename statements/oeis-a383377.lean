import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Group.Abs

/-!
# OEIS A383377

Paul D. Hanna defines A by summing x^j times the series obtained by taking
absolute values of all coefficients in A^(-j). At degree n this is a finite
sum over 0 ≤ j ≤ n. He conjectures that every coefficient after degree one
is even.

Source: https://oeis.org/A383377
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a383377
open PowerSeries

theorem main : ∀ A : (PowerSeries ℤ)ˣ,
    (∀ n : ℕ, coeff n (A : PowerSeries ℤ) =
      ∑ j ∈ Finset.range (n + 1), |coeff (n - j) ((↑A⁻¹ : PowerSeries ℤ) ^ j)|) →
    ∀ n : ℕ, 1 < n → Even (coeff n (A : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a383377
