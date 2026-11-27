import Mathlib

/-!
# Sogge’s local smoothing conjecture
Source: https://en.wikipedia.org/wiki/Local_smoothing_conjecture
Credit: @my-other-github-account (catalog adaptation).
Definitions adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
Lean ComparatorChallenges/LocalSmoothing.lean (Apache-2.0).
For finite p the inhomogeneous Sobolev space is the completion of Schwartz
functions in the Bessel potential norm. The uniform estimate on this dense
class gives the unique bounded extension into the complete spacetime Lp.
Negative time in the negative-phase integral gives the required positive phase.
-/
open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace OMA.S_wpc_local_smoothing_conjecture

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def angularFourier {n : ℕ} (f : Space n → ℂ) (ξ : Space n) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f x

def angularInverse {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ

def halfWaveIntegral {n : ℕ} (t : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    angularFourier f ξ)

def besselPotential {n : ℕ} (s : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) • angularFourier f ξ)

def observationMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Icc 1 2))

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∀ p α : ℝ, 2 * (n : ℝ) / ((n : ℝ) - 1) ≤ p →
      ((n : ℝ) - 1) * (1 / 2 - 1 / p) - 1 / p < α →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
        MemLp (besselPotential (α) f)
          (ENNReal.ofReal p) ∧
        MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1)
          (ENNReal.ofReal p) (observationMeasure n) ∧
        eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1)
          (ENNReal.ofReal p) (observationMeasure n) ≤
        ENNReal.ofReal C *
          eLpNorm (besselPotential (α) f)
            (ENNReal.ofReal p) volume := by
  sorry

end OMA.S_wpc_local_smoothing_conjecture
