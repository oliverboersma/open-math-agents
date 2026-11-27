import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Squaring a random Schwartz distribution, MathOverflow 201997

We state the proposed blanket no-go theorem for the primary finite-variance
question, in the supercritical range where the source gives the input covariance
as a locally integrable Riesz kernel. The constant gamma permits either
normalization of the field. Real Schwartz tests determine the real Gaussian law
by polarization. Disjointly supported compact test tensors determine the
restriction of the output covariance off the diagonal. The map is only required
to be local and measurable. No sign symmetry or translation equivariance is added.
-/

namespace OMA.S_mo_201997

open MeasureTheory ProbabilityTheory

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Test (d : ℕ) := SchwartzMap (Space d) ℝ
abbrev Field (d : ℕ) := StrongDual ℝ (Test d)

noncomputable def rieszPair {d : ℕ} (exponent : ℝ) (f g : Test d) : ℝ :=
  ∫ x : Space d, ∫ y : Space d, f x * g y * ‖x - y‖ ^ (-exponent)

noncomputable abbrev observed {d : ℕ} (U : Set (Space d)) : MeasurableSpace (Field d) :=
  ⨆ f : {f : Test d // tsupport f ⊆ U},
    MeasurableSpace.comap (fun φ : Field d => φ f.val) (borel ℝ)

def localMap {d : ℕ} (S : Field d → Field d) : Prop :=
  ∀ (U : Set (Space d)), IsOpen U → ∀ f : Test d, tsupport f ⊆ U →
    @Measurable _ _ (observed U) (borel ℝ) (fun φ => S φ f)

theorem main :
    ∀ (d : ℕ), 0 < d → ∀ (h γ : ℝ), (d : ℝ) / 4 < h → h < (d : ℝ) / 2 → 0 < γ →
    ∀ (μ : @Measure (Field d) (borel (Field d))),
      letI : MeasurableSpace (Field d) := borel (Field d)
      IsProbabilityMeasure μ →
      (∀ f : Test d, HasLaw (fun φ : Field d => φ f)
        (gaussianReal 0 (γ * rieszPair (2*h) f f).toNNReal) μ) →
      ¬ ∃ S : Field d → Field d, Measurable S ∧ localMap S ∧
        (∀ f : Test d, MemLp (fun φ => S φ f) 2 μ ∧ (∫ φ, S φ f ∂μ) = 0) ∧
        ∀ f g : Test d, HasCompactSupport f → HasCompactSupport g →
          Disjoint (tsupport f) (tsupport g) →
          (∫ φ, S φ f * S φ g ∂μ) = 2 * γ^2 * rieszPair (4*h) f g := by
  sorry

end OMA.S_mo_201997
