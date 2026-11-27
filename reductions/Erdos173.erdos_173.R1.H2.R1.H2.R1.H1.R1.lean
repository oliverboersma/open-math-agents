import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1

/-!
Separate the continuous-field construction from its analytic moment argument.

H1 asks for the bounded real L² field and its three pair correlations. H2 is an
independent probability-space lemma: on [-1,1]³, the nonnegative quadratic form
1 + ab + ac + bc vanishes almost everywhere when its expectation is zero.
Thus the representation-theoretic construction only needs to establish a scalar
correlation identity; the pointwise identity follows from integrability and
positivity. No sigma-finiteness assumption is added.

This split follows the integral_qform and qform_field_ae arguments in Jacob
Parish / Plasma AI, plasma-ai/erdos-173, commit
bc41fe8950bafe3d69fc58f2a422f1dee9a1e943, Erdos173/Transfer/Sample.lean.
That file adapts OpenAI's openai/math at
adc7f1241b42e322a6451854ab7e4b4c146bf78a. Those sources are Apache-2.0 licensed.
-/

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- The representation-theoretic input, with its triangle constraint expressed through pair correlations. -/
def H1 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)
  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 → ∀ c : ℂ → Fin 2,
    avoids c 1 → avoids c x →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω), IsProbabilityMeasure ν ∧
      ∃ f : ℂ → Lp ℂ 2 ν, Continuous f ∧
        (∀ p : ℂ, ∀ᵐ ω ∂ν,
          (f p ω).im = 0 ∧ -1 ≤ (f p ω).re ∧ (f p ω).re ≤ 1) ∧
        ∀ r : ℝ, (r = 1 ∨ r = x) → ∀ p : ℂ, ∀ u : Circle,
          (1 + inner ℂ (f p) (f (p + u * r)) +
            inner ℂ (f p) (f (p + u * (r * ζ))) +
            inner ℂ (f (p + u * r)) (f (p + u * (r * ζ)))).re = 0

/-- A zero quadratic moment of three bounded real L² vectors gives a pointwise identity. -/
def H2 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A B C : Lp ℂ 2 ν),
    (∀ᵐ ω ∂ν, (A ω).im = 0 ∧ -1 ≤ (A ω).re ∧ (A ω).re ≤ 1) →
    (∀ᵐ ω ∂ν, (B ω).im = 0 ∧ -1 ≤ (B ω).re ∧ (B ω).re ≤ 1) →
    (∀ᵐ ω ∂ν, (C ω).im = 0 ∧ -1 ≤ (C ω).re ∧ (C ω).re ≤ 1) →
    (1 + inner ℂ A B + inner ℂ A C + inner ℂ B C).re = 0 →
    ∀ᵐ ω ∂ν,
      1 + (A ω).re * (B ω).re + (A ω).re * (C ω).re + (B ω).re * (C ω).re = 0

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1.H1 := by
  intro field moment x hlow hhigh hne c h₁ h₂
  obtain ⟨Ω, mΩ, ν, hν, f, hf, hbounded, hcorrelation⟩ :=
    field x hlow hhigh hne c h₁ h₂
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure ν := hν
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  refine ⟨Ω, mΩ, ν, hν, f, hf, ?_⟩
  intro r hr p u
  exact moment Ω ν (f p) (f (p + u * r)) (f (p + u * (r * ζ)))
    (hbounded p) (hbounded _) (hbounded _) (hcorrelation r hr p u)

end OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1
