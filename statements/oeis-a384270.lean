import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Paul D. Hanna's parity conjecture for OEIS A384270

Source: https://oeis.org/A384270
Credit: @anmolspace

The generating series starts at x. Its defining quotient has a denominator of
order three, so the equation is expressed by cross-multiplication. This avoids
treating the denominator as a unit in the power series ring.
-/

namespace OMA.S_oeis_a384270

open PowerSeries

/-- The normalized integer generating series specified by Hanna. -/
def Defines (A : PowerSeries ℤ) : Prop :=
  A.constantCoeff = 0 ∧ coeff 1 A = 1 ∧
    A * A.subst ((X : PowerSeries ℤ)^3 + 3*X*A^3) =
      A.subst ((X : PowerSeries ℤ)^4 + 4*X*A^4)

/-- The equation has a normalized integer solution, and every such series has
odd coefficients precisely at the positive powers of two, including 1. -/
theorem main : (∃ A, Defines A) ∧
    ∀ A, Defines A → ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) := by
  sorry

end OMA.S_oeis_a384270
