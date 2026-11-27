import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic

/-!
# Atiyah's conjecture on configurations
Source: Michael Atiyah, Configurations of points (2001), Conjecture 2.1.
Catalogue source: https://en.wikipedia.org/wiki/Atiyah_conjecture_on_configurations
Credit: @garrytaulu
-/

namespace OMA.S_wp_atiyah_conjecture_on_configurations

/-- Linear factor for the direction of a displacement, in the affine chart
with the north pole at infinity. The constant factor represents a homogeneous
linear factor whose root is at infinity. -/
noncomputable def directionFactor (d : Fin 3 → ℝ) : Polynomial ℂ :=
  let r := Real.sqrt ((d 0)^2 + (d 1)^2 + (d 2)^2)
  if r = d 2 then 1
  else Polynomial.C ((r - d 2 : ℝ) : ℂ) * Polynomial.X -
    Polynomial.C ((d 0 : ℂ) + (d 1 : ℂ) * Complex.I)

/-- Column i lists the coefficients of the polynomial whose projective roots
are the directions from point i to each of the other points. -/
noncomputable def configurationMatrix {n : ℕ} (p : Fin n → Fin 3 → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun k i => (∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i)).coeff k.val

theorem main : ∀ (n : ℕ) (p : Fin n → Fin 3 → ℝ), Function.Injective p →
    (configurationMatrix p).det ≠ 0 := by
  sorry

end OMA.S_wp_atiyah_conjecture_on_configurations
