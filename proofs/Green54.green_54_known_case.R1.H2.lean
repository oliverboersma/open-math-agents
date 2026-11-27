import OMAReductions.R_Green54_green_54_known_case_R1
import Mathlib

/-!
Step H2 of Green54.green_54_known_case.R1. The Gaussian product measure on the
Polish space of real sequences is inner regular, so the cylinder over A contains a
compact set of mass above r. Its balanced hull, the image of the unit interval times
that compact set under scalar multiplication, is still compact and stays inside the
cylinder because A is balanced.
-/

open MeasureTheory ProbabilityTheory in
theorem OMA.solution : OMA.R_Green54_green_54_known_case_R1.H2 := by
  unfold OMA.R_Green54_green_54_known_case_R1.H2
  intro I A r hA hbal hr
  have hprob : IsProbabilityMeasure Green54.gaussianMeasureInf := by
    unfold Green54.gaussianMeasureInf
    infer_instance
  have hS : MeasurableSet ((Finset.restrict (π := fun _ : ℕ => ℝ) I) ⁻¹' A) :=
    hA.preimage (Finset.continuous_restrict (A := fun _ : ℕ => ℝ) I).measurable
  have hmeas := OMA.R_Green54_green_54_known_case_R1.cylinder_measure I A hA
  obtain ⟨K₀, hK₀A, hK₀, hrK₀⟩ := hS.exists_lt_isCompact_of_ne_top
    (μ := Green54.gaussianMeasureInf) (measure_ne_top _ _) (by rw [hmeas]; exact hr)
  let K : Set (ℕ → ℝ) :=
    (fun p : ℝ × (ℕ → ℝ) => p.1 • p.2) '' (Metric.closedBall (0 : ℝ) 1 ×ˢ K₀)
  refine ⟨K, ((isCompact_closedBall (0 : ℝ) 1).prod hK₀).image continuous_smul, ?_, ?_, ?_⟩
  · intro a ha
    rintro _ ⟨_, ⟨⟨b, x⟩, ⟨hb, hx⟩, rfl⟩, rfl⟩
    refine ⟨(a * b, x), ⟨?_, hx⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right] at hb ⊢
      calc ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul a b
        _ ≤ 1 := mul_le_one₀ ha (norm_nonneg _) hb
    · show (a * b) • x = a • b • x
      rw [mul_smul]
  · refine hrK₀.le.trans (measure_mono ?_)
    intro x hx
    exact ⟨(1, x), ⟨by simp, hx⟩, by simp⟩
  · rintro _ ⟨⟨b, x⟩, ⟨hb, hx⟩, rfl⟩
    have hxA : Finset.restrict (π := fun _ : ℕ => ℝ) I x ∈ A := hK₀A hx
    have hb' : ‖b‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hb
      exact hb
    show I.restrict (b • x) ∈ A
    have hr' : I.restrict (b • x) = b • I.restrict x := rfl
    rw [hr']
    exact hbal b hb' (Set.smul_mem_smul_set hxA)
