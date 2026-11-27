import Mathlib.Probability.Distributions.Exponential

/-!
# Pinelis's sharp contraction conjecture for three identically distributed draws

Source: https://mathoverflow.net/questions/396509 (Iosif Pinelis, June 30, 2021).
Formalization by @LDJAI with OpenAI Codex. All integrals use Lebesgue measure.
-/

namespace OMA.S_mo_396509

open MeasureTheory ProbabilityTheory

/-- A log-concave probability density on the whole real line, allowing zeros. -/
def IsLogConcavePDF (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫ x : ℝ, f x) = 1 ∧
    ∀ x y : ℝ, ∀ t : ℝ, 0 < t → t < 1 →
      (f x) ^ (1 - t) * (f y) ^ t ≤ f ((1 - t) * x + t * y)

/-- The mean absolute difference of two independent draws. -/
noncomputable def spread (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, ∫ y : ℝ, |x - y| * f x * f y

/-- The improvement in absolute error when two draws are averaged against a third. -/
noncomputable def gain (f : ℝ → ℝ) : ℝ :=
  spread f - ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, |(x + y) / 2 - z| * f x * f y * f z

/-- The best universal constant is one ninth, attained by each positive-rate exponential. -/
theorem main :
    IsGreatest {c : ℝ | ∀ f : ℝ → ℝ, IsLogConcavePDF f → c * spread f ≤ gain f}
      (1 / 9 : ℝ) ∧
    ∀ r : ℝ, 0 < r → gain (exponentialPDFReal r) = (1 / 9 : ℝ) * spread (exponentialPDFReal r) := by
  sorry

end OMA.S_mo_396509
