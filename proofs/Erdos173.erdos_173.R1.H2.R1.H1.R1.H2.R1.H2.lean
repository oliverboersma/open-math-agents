import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1

/-! Angular inversion for the real Fourier transform of a finite measure on the plane.
The cosine identity follows from polar coordinates, then periodicity removes the argument of the frequency. -/
-- Credit: @marcusbuffett

open MeasureTheory Real Set Filter
open scoped Topology

private lemma angular_inner (ξ : ℂ) (r θ : ℝ) :
    inner ℝ ξ ((Circle.exp θ : ℂ) * (r : ℂ)) = (r * ‖ξ‖) * cos (θ - ξ.arg) := by
  simp only [Complex.inner, Circle.coe_exp, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_sub, Complex.conj_re, Complex.conj_im]
  have hc := Complex.norm_mul_cos_arg ξ
  have hs := Complex.norm_mul_sin_arg ξ
  linear_combination r * cos θ * (-hc) + r * sin θ * (-hs)

private lemma angular_shift (b d : ℝ) :
    (∫ θ in (0:ℝ)..2*π, cos (b*cos (θ-d))) = ∫ θ in (0:ℝ)..2*π, cos (b*cos θ) := by
  let f (θ : ℝ) := cos (b*cos θ)
  have hp : Function.Periodic f (2*π) := fun θ => by simp [f, Real.cos_add_two_pi]
  change (∫ θ in (0:ℝ)..2*π, f (θ-d)) = _
  rw [intervalIntegral.integral_comp_sub_right]
  simpa only [zero_sub,zero_add,sub_eq_add_neg,add_comm (2*π) (-d)] using
    hp.intervalIntegral_add_eq (-d) 0

private theorem planar_average (ν : Measure ℂ) [IsFiniteMeasure ν] (r : ℝ)
    (h : ∀ u : Circle, (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(r:ℂ))) : ℂ) ∂ν) = -1/3) :
    (∫ ξ : ℂ, (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2*π, cos ((r * ‖ξ‖) * cos θ)) ∂ν) = -1/3 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2*π))
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let F (θ : ℝ) (ξ : ℂ) := cos (inner ℝ ξ ((Circle.exp θ:ℂ)*(r:ℂ)))
  have point (θ : ℝ) : ∫ ξ, F θ ξ ∂ν = -1/3 := by
    have hi : Integrable (fun ξ : ℂ => (Circle.exp (inner ℝ ξ ((Circle.exp θ:ℂ)*(r:ℂ))) : ℂ)) ν :=
      Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
        (Eventually.of_forall fun _ => (Circle.norm_coe _).le)
    calc
      _ = ∫ ξ, RCLike.re (Circle.exp (inner ℝ ξ ((Circle.exp θ:ℂ)*(r:ℂ))) : ℂ) ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          change cos _ = (Circle.exp _ : ℂ).re
          exact (Complex.exp_ofReal_mul_I_re _).symm
      _ = RCLike.re (∫ ξ, (Circle.exp (inner ℝ ξ ((Circle.exp θ:ℂ)*(r:ℂ))) : ℂ) ∂ν) :=
        integral_re hi
      _ = -1/3 := by rw [h]; norm_num
  have hi : Integrable (Function.uncurry F) (μ.prod ν) :=
    Integrable.of_bound (by unfold Function.uncurry F; fun_prop : Continuous _).aestronglyMeasurable 1
      (Eventually.of_forall fun p => by
        change |cos _| ≤ 1
        exact abs_cos_le_one _)
  have fiber (ξ : ℂ) : (∫ θ, F θ ξ ∂μ) =
      ∫ θ in (0:ℝ)..2*π, cos ((r*‖ξ‖)*cos θ) := by
    dsimp only [μ]
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    simpa only [F, angular_inner] using angular_shift (r*‖ξ‖) ξ.arg
  simp_rw [← fiber]
  rw [integral_const_mul, ← integral_integral_swap hi]
  simp_rw [point]
  simp [μ, Real.two_pi_pos.le]
  field_simp [Real.pi_ne_zero]



theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro ν inst r hr h
  exact planar_average ν r h
