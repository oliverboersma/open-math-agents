import Mathlib

/-!
# A111913: Expansion of x*(-2-3*x-x^2+x^7+x^8+2*x^4) / ((x-1)*(x+1)*(x^8-x^4+1)).

Source: https://oeis.org/A111913
Credit: @ShoQo

Conjecture: "It appears that (a(n)) has period 24." (Charles R Greathouse IV, Feb 07 2013: "The
above conjecture is correct, since x^24 = 1 mod (x-1)*(x+1)*(x^8-x^4+1).")

Formalization notes:
* Offset 0: a(n) is the coefficient of x^n in the power series expansion, taken in ℚ⟦X⟧ (the
  denominator has constant term -1, so it is invertible; data: 0, 2, 3, 3, 3, 3, 6, ...).
* "Period 24" is stated as a(n + 24) = a(n) for all n ≥ 0.
-/

namespace OMA.S_oeis_a111913

open PowerSeries

/-- a(n): the coefficient of x^n in x(-2-3x-x^2+x^7+x^8+2x^4) / ((x-1)(x+1)(x^8-x^4+1)). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n ((X * (-2 - 3 * X - X ^ 2 + X ^ 7 + X ^ 8 + 2 * X ^ 4) : ℚ⟦X⟧) *
    ((X - 1) * (X + 1) * (X ^ 8 - X ^ 4 + 1) : ℚ⟦X⟧)⁻¹)

theorem main : ∀ n : ℕ, a (n + 24) = a n := by
  sorry

end OMA.S_oeis_a111913
