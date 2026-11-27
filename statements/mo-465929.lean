import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Comparing the first two Wasserstein distances between centered Gaussian measures

Source: https://mathoverflow.net/questions/465929 (Vladimir Zolotov).
Lean formalization: @LDJAI (OpenAI Codex).

The metric is Euclidean. The same positive constant must work for every
finite dimension and every pair of centered Gaussian laws. The multiplicative
inequality includes equal laws without division by zero. Gaussianity includes
singular covariance matrices. For the two powers used here, every coupling
has finite cost because its marginals have finite second moments.
-/

namespace OMA.S_mo_465929

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Euclidean space with its usual Hilbert norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A joint measure with the prescribed marginals. -/
def IsCoupling {d : ℕ} (π : Measure (E d × E d)) (μ ν : Measure (E d)) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- The infimum of the expected `p`th power of the Euclidean displacement. -/
def transportCost {d : ℕ} (p : ℕ) (μ ν : Measure (E d)) : ℝ :=
  sInf {r : ℝ | ∃ π : Measure (E d × E d), IsCoupling π μ ν ∧
    r = ∫ z, dist z.1 z.2 ^ p ∂π}

/-- The comparison is uniform in the dimension and both covariance matrices. -/
theorem main :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (μ ν : Measure (E d)),
      IsGaussian μ → IsGaussian ν →
      (∫ x, x ∂μ) = 0 → (∫ y, y ∂ν) = 0 →
      Real.sqrt (transportCost 2 μ ν) ≤ C * transportCost 1 μ ν := by
  sorry

end

end OMA.S_mo_465929
