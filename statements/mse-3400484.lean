import Mathlib

/-!
# A tail inequality at the mean for a log-concave density

The question by smcc asks for an inequality for every differentiable
log-concave probability density on a bounded interval with nonnegative
left endpoint. The CDF and the mean below use the original density.
The values of the density outside its interval of support play no role.

Source: https://math.stackexchange.com/q/3400484 (2019, CC BY-SA 4.0)
Credit: @ecirak42
-/

namespace OMA.S_mse_3400484

open MeasureTheory

noncomputable def cdf (f : ℝ → ℝ) (l x : ℝ) : ℝ := ∫ t in l..x, f t
noncomputable def mean (f : ℝ → ℝ) (l u : ℝ) : ℝ := ∫ x in l..u, x * f x

theorem main : ∀ (l u : ℝ) (f : ℝ → ℝ),
    0 ≤ l → l < u → DifferentiableOn ℝ f (Set.Icc l u) →
    (∀ x ∈ Set.Icc l u, 0 ≤ f x) → (∀ x ∈ Set.Ioo l u, 0 < f x) →
    ConcaveOn ℝ (Set.Ioo l u) (fun x => Real.log (f x)) →
    (∫ x in l..u, f x) = 1 →
    let μ := mean f l u
    (∫ x in μ..u, cdf f l x * (1 - cdf f l x)) ≤ μ * (cdf f l μ)^2 := by
  sorry

end OMA.S_mse_3400484
