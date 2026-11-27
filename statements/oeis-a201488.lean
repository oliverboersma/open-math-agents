import Mathlib

/-!
The A201488 conjecture of Simon Plouffe (2025) relates the CHSH quantum winning
probability to the integer coefficients A210066. The defining generating function
of A210066 is the square of phi(q^2)/phi(q), where phi(q) sums q^(k^2) over
all integers k. Sources: https://oeis.org/A201488 and https://oeis.org/A210066.
-/

namespace OMA.S_oeis_a201488

/-- The formal theta series phi(X^m), used for m = 1 and m = 2.
The zero lattice point occurs once and each positive index represents both signs. -/
noncomputable def thetaSeries (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    (if n = 0 then 1 else 0) +
      ∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then 2 else 0

/-- A210066 has offset zero. The denominator has constant coefficient one. -/
noncomputable def a210066 (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((thetaSeries 2 * PowerSeries.invOfUnit (thetaSeries 1) 1) ^ 2)

/-- The series at exp(-pi) sums to the optimal quantum CHSH winning probability. -/
theorem main :
    HasSum (fun n : ℕ => (a210066 n : ℝ) * Real.exp (-Real.pi) ^ n)
      ((2 + Real.sqrt 2) / 4) := by
  sorry

end OMA.S_oeis_a201488
