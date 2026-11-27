import Mathlib

/-!
# Crouzeix's conjecture

Source: https://en.wikipedia.org/wiki/Crouzeix%27s_conjecture
Credit: @my-other-github-account

The polynomial formulation, with the spectral norm and sharp constant 2.
Positive matrix sizes are used so the numerical range is nonempty.
The zero-dimensional case is trivial and does not affect the optimal constant.
Numerical-range definition adapted from OpenAI math, DirectCrouzeix/Model.lean,
revision 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
-/

namespace OMA.S_wpc_crouzeix_conjecture

open scoped Matrix.Norms.L2Operator

noncomputable def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧
    inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u) = z}

noncomputable def UniversalBound (C : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
    ‖Polynomial.aeval A p‖ ≤ C * sSup ((fun z : ℂ => ‖p.eval z‖) '' numericalRange A)

theorem main : UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C := by
  sorry

end OMA.S_wpc_crouzeix_conjecture
