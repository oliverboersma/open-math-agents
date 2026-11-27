import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1

-- Port of Jacob Parish (Plasma AI), plasma-ai/erdos-173 at 4a368a652753,
-- used under Apache-2.0. The two independent estimates are the Bessel
-- pair bound and the spectral representation of the two correlations.
-- Credit: @marcusbuffett

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1

open Real


lemma abs_inv_two_pi_mul_integral_le_one {f : ℝ → ℝ} (hf : ∀ θ, |f θ| ≤ 1) :
    |(2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (C := 1) (f := f) fun θ _ => hf θ
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos two_pi_pos, one_mul] at h
  rw [abs_mul, abs_of_pos (inv_pos.mpr two_pi_pos)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, f θ| ≤ (2 * π)⁻¹ * (2 * π) := by gcongr
    _ = 1 := inv_mul_cancel₀ two_pi_pos.ne'


theorem abs_besselJ0_le_one (x : ℝ) : |(fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) x| ≤ 1 :=
  abs_inv_two_pi_mul_integral_le_one fun _ => abs_cos_le_one _


theorem hasDerivAt_besselJ0 (x : ℝ) : HasDerivAt (fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) ((fun x : ℝ => -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ))) x) x := by
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos (x * cos θ)) (F' := fun x θ => -(cos θ * sin (x * cos θ)))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun θ => cos (x * cos θ))
      |>.aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => -(cos θ * sin (x * cos θ))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      simpa only [neg_mul, mul_neg, mul_comm] using
        ((hasDerivAt_mul_const (cos θ)).cos : HasDerivAt (fun y => cos (y * cos θ)) _ y))).2.const_mul (2 * π)⁻¹
  rwa [intervalIntegral.integral_neg, mul_neg] at h


theorem continuous_besselJ0 : Continuous (fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselJ0 x).continuousAt



open MeasureTheory Real

def H1 : Prop :=
  let J := fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)
  ∀ x : ℝ, 3 / 2 ≤ x → ∀ t : ℝ, 0 ≤ t →
  -83 / 125 ≤ J t + J (x * t)

def H2 : Prop :=
  let J := fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * ζ)) = c p)
  ∀ x : ℝ, 0 < x → ∀ c : ℂ → Fin 2, avoids c 1 → avoids c x →
    ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real Set.univ ≤ 1 ∧
      (∫ ξ, J ‖ξ‖ ∂ν) = -1 / 3 ∧ (∫ ξ, J (x * ‖ξ‖) ∂ν) = -1 / 3

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1.H1 := by
  let J := fun x : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)
  intro bound spectrum x hx hfar c h₁ h₂
  obtain ⟨ν, hfin, hmass, hcorr₁, hcorr₂⟩ := spectrum x hx c h₁ h₂
  letI : IsFiniteMeasure ν := hfin
  have hint (s : ℝ) : Integrable (fun ξ : ℂ => J (s * ‖ξ‖)) ν :=
    (integrable_const (1 : ℝ)).mono'
      (continuous_besselJ0.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
      (ae_of_all _ fun ξ => abs_besselJ0_le_one _)
  have hint₁ : Integrable (fun ξ : ℂ => J ‖ξ‖) ν := by simpa using hint 1
  have hlow (ξ : ℂ) : -83 / 125 ≤ J ‖ξ‖ + J (x * ‖ξ‖) := by
    rcases hfar with h | h
    · exact bound x h _ (norm_nonneg ξ)
    · have h' : 3 / 2 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
      have hb := bound (1 / x) h' _ (mul_nonneg hx.le (norm_nonneg ξ))
      rw [← mul_assoc, one_div_mul_cancel hx.ne', one_mul] at hb
      linarith
  have hi := integral_mono (integrable_const (-83 / 125 : ℝ)) (hint₁.add (hint x)) hlow
  simp only [Pi.add_apply] at hi
  rw [integral_add hint₁ (hint x), hcorr₁, hcorr₂, integral_const, smul_eq_mul] at hi
  nlinarith


end OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1
