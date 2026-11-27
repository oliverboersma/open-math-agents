import Mathlib

/-!
# Bochner–Riesz conjecture

The Euclidean unit-radius multiplier formulation in the Bochner–Riesz
conjecture section of https://en.wikipedia.org/wiki/Bochner–Riesz_mean.
We take positive real order, as in the strict critical-index formulation.
For finite p, boundedness is the uniform estimate on Schwartz test functions,
which are dense in Lᵖ. Dilation gives the same operator bound at every radius.
-/

namespace OMA.S_wp_bochner_riesz_conjecture

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Multiply the Fourier transform by the positive part of 1 minus the
squared Euclidean norm, raised to the order δ, then invert the transform. -/
noncomputable def bochnerRiesz {n : ℕ} (δ : ℝ) (f : SchwartzMap (Euclidean n) ℂ) :
    Euclidean n → ℂ :=
  𝓕⁻ (fun ξ : Euclidean n =>
    (((max (1 - ‖ξ‖ ^ 2) 0) ^ δ : ℝ) : ℂ) * 𝓕 (f : Euclidean n → ℂ) ξ)

theorem main : ∀ (n : ℕ), 1 ≤ n → ∀ p δ : ℝ, 1 < p → 0 < δ →
    ((∃ C : ℝ≥0, ∀ f : SchwartzMap (Euclidean n) ℂ,
        eLpNorm (bochnerRiesz δ f) (ENNReal.ofReal p) volume ≤
          (C : ℝ≥0∞) * eLpNorm (f : Euclidean n → ℂ) (ENNReal.ofReal p) volume) ↔
      max ((n : ℝ) * |1 / p - 1 / 2| - 1 / 2) 0 < δ) := by
  sorry

end OMA.S_wp_bochner_riesz_conjecture
