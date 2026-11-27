import FormalConjectures.ErdosProblems.«116»
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
An entire function with bounded values off a horizontal strip and controlled growth,
obtained by rotating an elementary Laplace integral.
-/

noncomputable section

open Set Metric Filter MeasureTheory Complex
open scoped Real Topology ENNReal ComplexConjugate

namespace LemniscateUpper

def realKernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((t:ℂ)*(z-(Real.log (1+t):ℂ)))

def contourKernel (z w : ℂ) : ℂ :=
  Complex.exp (w*(z-Complex.log (1+w)))

def entireStrip (z : ℂ) : ℂ := ∫ t in Ioi (0:ℝ), realKernel z t

private theorem realKernel_measurable (z : ℂ) : Measurable (realKernel z) := by
  unfold realKernel
  fun_prop

private theorem norm_realKernel (z : ℂ) (t : ℝ) :
    ‖realKernel z t‖ = Real.exp (t*(z.re-Real.log (1+t))) := by
  rw [realKernel,Complex.norm_exp,Complex.mul_re]
  simp

private theorem realKernel_deriv (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => realKernel w t) ((t:ℂ)*realKernel z t) z := by
  have h := (((hasDerivAt_id z).sub_const (Real.log (1+t):ℂ)).const_mul (t:ℂ)).cexp
  exact h.congr_deriv (by simp [realKernel,mul_comm])

private def cut (B : ℝ) : ℝ := Real.exp (B+2)

private def stepMajor (B t : ℝ) : ℝ :=
  (Icc 0 (cut B)).indicator (fun _ => (cut B+1)*Real.exp (B*cut B)) t + Real.exp (-t)

private theorem major_nonneg (B t : ℝ) : 0 ≤ stepMajor B t := by
  unfold stepMajor cut
  apply add_nonneg _ (Real.exp_pos _).le
  apply Set.indicator_nonneg
  intro _ _
  positivity

private theorem major_integrable (B : ℝ) : IntegrableOn (stepMajor B) (Ioi 0) := by
  have h : Integrable ((Icc 0 (cut B)).indicator (fun _ : ℝ => (cut B+1)*Real.exp (B*cut B))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  exact h.integrableOn.add (integrableOn_exp_neg_Ioi 0)

private theorem kernel_major_bound {B t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t)
    {z : ℂ} (hz : z.re ≤ B) :
    ‖realKernel z t‖ ≤ stepMajor B t ∧ ‖(t:ℂ)*realKernel z t‖ ≤ stepMajor B t := by
  have hlog : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith)
  have hnorm := norm_realKernel z t
  have hw : ‖(t:ℂ)‖ = t := by simp [Complex.norm_real,abs_of_nonneg ht]
  rw [norm_mul,hw,hnorm]
  by_cases hsmall : t ≤ cut B
  · have hmem : t ∈ Icc 0 (cut B) := ⟨ht,hsmall⟩
    have hh : t*(z.re-Real.log (1+t)) ≤ B*cut B := by
      calc
        _ ≤ t*B := mul_le_mul_of_nonneg_left (by linarith) ht
        _ ≤ B*cut B := by rw [mul_comm t B]; exact mul_le_mul_of_nonneg_left hsmall hB
    have hExp := Real.exp_le_exp.mpr hh
    rw [stepMajor,Set.indicator_of_mem hmem]
    have hT : 0 < cut B := Real.exp_pos _
    constructor
    · calc
        _ ≤ Real.exp (B*cut B) := hExp
        _ ≤ (cut B+1)*Real.exp (B*cut B) := le_mul_of_one_le_left (by positivity) (by linarith)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · calc
        _ ≤ (cut B+1)*Real.exp (B*cut B) :=
          mul_le_mul (by linarith) hExp (Real.exp_pos _).le (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have htl : cut B ≤ 1+t := by linarith [le_of_not_ge hsmall]
    have hb := Real.log_le_log (Real.exp_pos (B+2)) htl
    rw [Real.log_exp] at hb
    have hX : Real.exp (t*(z.re-Real.log (1+t))) ≤ Real.exp (-2*t) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hz),mul_nonneg ht (sub_nonneg.mpr hb)])
    have hmem : t ∉ Icc 0 (cut B) := fun h => hsmall h.2
    rw [stepMajor,Set.indicator_of_notMem hmem,zero_add]
    constructor
    · exact hX.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ Real.exp t * Real.exp (-2*t) :=
          mul_le_mul (by linarith [Real.add_one_le_exp t]) hX (Real.exp_pos _).le (by positivity)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem realKernel_integrable (z : ℂ) : IntegrableOn (realKernel z) (Ioi 0) := by
  refine (major_integrable ‖z‖).mono' (realKernel_measurable z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (kernel_major_bound (norm_nonneg z) ht.le (Complex.re_le_norm z)).1

theorem entireStrip_hasDerivAt (z : ℂ) :
    HasDerivAt entireStrip (∫ t in Ioi (0:ℝ), (t:ℂ)*realKernel z t) z := by
  let μ : Measure ℝ := volume.restrict (Ioi (0:ℝ))
  let B := ‖z‖+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBound : ∀ᵐ (t:ℝ) ∂μ, ∀ w ∈ ball z 1, ‖(t:ℂ)*realKernel w t‖ ≤ stepMajor B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have hr : w.re ≤ B := (Complex.re_le_norm _).trans (by
      have H : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w-z) z
      rw [mem_ball,dist_eq_norm] at hw
      dsimp [B]
      linarith)
    exact (kernel_major_bound hB ht.le hr).2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z zero_lt_one)
    (.of_forall (fun w => (realKernel_measurable w).aestronglyMeasurable)) (realKernel_integrable z)
    ((Complex.continuous_ofReal.measurable.mul (realKernel_measurable z)).aestronglyMeasurable)
    hBound (major_integrable B) (.of_forall (fun t w _ => realKernel_deriv w t))).2

theorem entireStrip_entire : Differentiable ℂ entireStrip :=
  fun z => (entireStrip_hasDerivAt z).differentiableAt

private theorem integral_major (B : ℝ) :
    (∫ t in Ioi (0:ℝ), stepMajor B t) =
      cut B*((cut B+1)*Real.exp (B*cut B))+1 := by
  have h : Integrable ((Icc 0 (cut B)).indicator (fun _ : ℝ => (cut B+1)*Real.exp (B*cut B))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hi : Icc 0 (cut B) ∩ Ioi (0:ℝ) = Ioc 0 (cut B) := by
    ext x
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.le,h.2⟩,h.1⟩⟩
  unfold stepMajor
  rw [integral_add h.integrableOn (integrableOn_exp_neg_Ioi 0),
    integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,hi,
    integral_const,Measure.real_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    ← Measure.real_def,Real.volume_real_Ioc_of_le (b := cut B) (Real.exp_pos _).le,sub_zero,smul_eq_mul,
    integral_exp_neg_Ioi_zero]

private theorem major_growth {B : ℝ} (hB : 0 ≤ B) :
    cut B*((cut B+1)*Real.exp (B*cut B))+1 ≤ Real.exp (Real.exp (2*B+5)) := by
  let T := cut B
  have hT : 0 ≤ T := (Real.exp_pos _).le
  have h1 : T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have h2 : T+1 ≤ Real.exp T := Real.add_one_le_exp T
  have hBT : 0 ≤ (B+2)*T := by positivity
  have hlead : T*((T+1)*Real.exp (B*T)) ≤ Real.exp ((B+2)*T) := by
    calc
      _ ≤ Real.exp T * (Real.exp T * Real.exp (B*T)) := by gcongr
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have h3 : (B+2)*T ≤ Real.exp (2*B+4) := by
    calc
      _ ≤ T*T := mul_le_mul_of_nonneg_right (by dsimp [T,cut]; linarith [Real.add_one_le_exp (B+2)]) hT
      _ = _ := by dsimp [T,cut]; rw [← Real.exp_add]; congr 1; ring
  have h4 : (B+2)*T+1 ≤ Real.exp (2*B+5) := by
    calc
      _ ≤ Real.exp (2*B+4)+Real.exp (2*B+4) := add_le_add h3 (Real.one_le_exp (by linarith))
      _ = 2*Real.exp (2*B+4) := by ring
      _ ≤ Real.exp 1*Real.exp (2*B+4) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp ((B+2)*T) + 1 := by gcongr
    _ ≤ Real.exp ((B+2)*T) + Real.exp ((B+2)*T) := add_le_add_right (Real.one_le_exp hBT) _
    _ = Real.exp ((B+2)*T)*2 := by ring
    _ ≤ Real.exp ((B+2)*T)*Real.exp 1 := mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_pos _).le
    _ = Real.exp ((B+2)*T+1) := by rw [Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr h4

theorem norm_deriv_entireStrip_le {B : ℝ} (hB : 0 ≤ B) {z : ℂ} (hz : z.re ≤ B) :
    ‖deriv entireStrip z‖ ≤ Real.exp (Real.exp (2*B+5)) := by
  rw [(entireStrip_hasDerivAt z).deriv]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (.of_forall (fun _ => norm_nonneg _)) (major_integrable B) ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (kernel_major_bound hB ht.le hz).2
  · rw [integral_major]
    exact major_growth hB

theorem entireStrip_real_lower {R : ℝ} (hR : 0 ≤ R) :
    Real.exp (R-2*Real.log 3) ≤ (entireStrip (R:ℂ)).re := by
  have hz (t : ℝ) : (realKernel (R:ℂ) t).re = Real.exp (t*(R-Real.log (1+t))) := by
    rw [realKernel,Complex.exp_re,Complex.mul_re,Complex.mul_im]
    simp
  have him : IntegrableOn (fun t => (realKernel (R:ℂ) t).re) (Ioi (0:ℝ)) :=
    Complex.reCLM.integrable_comp (realKernel_integrable _)
  have hs : Icc (1:ℝ) 2 ⊆ Ioi 0 := fun _ ht => zero_lt_one.trans_le ht.1
  change _ ≤ Complex.reCLM (∫ t in Ioi (0:ℝ), realKernel (R:ℂ) t)
  rw [← Complex.reCLM.integral_comp_comm (realKernel_integrable _)]
  change _ ≤ ∫ (t : ℝ) in Ioi 0, (realKernel (R:ℂ) t).re
  refine le_trans ?_ (setIntegral_mono_set him (.of_forall (fun t => by change 0 ≤ (realKernel (R:ℂ) t).re; rw [hz]; positivity))
    hs.eventuallyLE)
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (R-2*Real.log 3)) (Icc 1 2) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hb : (∫ _ : ℝ in Icc 1 2, Real.exp (R-2*Real.log 3)) = Real.exp (R-2*Real.log 3) := by
    rw [integral_const,Measure.real_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,
      ← Measure.real_def,Real.volume_real_Icc_of_le (by norm_num),show (2:ℝ)-1=1 by norm_num,one_smul]
  rw [← hb]
  apply setIntegral_mono_on hc (him.mono_set hs) measurableSet_Icc
  intro t ht
  rw [hz,Real.exp_le_exp]
  have hlog : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith [ht.1])
  have hi := Real.log_le_log (by linarith [ht.1] : 0 < 1+t) (show 1+t≤3 by linarith [ht.2])
  nlinarith [mul_nonneg hR (sub_nonneg.mpr ht.1),
    mul_le_mul ht.2 hi hlog (by norm_num : (0:ℝ)≤2)]

private theorem norm_contourKernel (z w : ℂ) :
    ‖contourKernel z w‖ = Real.exp
      (w.re*(z.re-Real.log ‖1+w‖)-w.im*(z.im-Complex.arg (1+w))) := by
  rw [contourKernel,Complex.norm_exp,Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.log_re,Complex.log_im]

private theorem contourKernel_eq_real (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    contourKernel z (t:ℂ) = realKernel z t := by
  rw [contourKernel,realKernel,← Complex.ofReal_one,← Complex.ofReal_add,Complex.ofReal_log]
  linarith

private theorem contourKernel_differentiable (z : ℂ) {w : ℂ} (hw : 0 ≤ w.re) :
    DifferentiableAt ℂ (contourKernel z) w := by
  have hs : (1+w) ∈ slitPlane := Or.inl (by simp; linarith)
  have ha : AnalyticAt ℂ (fun t : ℂ => 1+t) w := by fun_prop
  have := (ha.clog hs).differentiableAt
  unfold contourKernel
  fun_prop

def stripWidth : ℝ := π/2+1

private theorem contour_exponent_le (z w : ℂ) (hz : stripWidth ≤ z.im)
    (hx : 0 ≤ w.re) (hy : 0 ≤ w.im) :
    w.re*(z.re-Real.log ‖1+w‖)-w.im*(z.im-Complex.arg (1+w)) ≤
      w.re*(z.re-Real.log ‖1+w‖)-w.im := by
  have hx' : 0 ≤ (1+w).re := by simp; linarith
  have harg : Complex.arg (1+w) ≤ π/2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hx')
  have hh : 1 ≤ z.im-Complex.arg (1+w) := by unfold stripWidth at hz; linarith
  have H := mul_le_mul_of_nonneg_left hh hy
  linarith

private theorem contourKernel_imag_bound (z : ℂ) (hz : stripWidth ≤ z.im) {t : ℝ} (ht : 0 ≤ t) :
    ‖contourKernel z ((t:ℂ)*I)‖ ≤ Real.exp (-t) := by
  rw [norm_contourKernel,Real.exp_le_exp]
  have h := contour_exponent_le z ((t:ℂ)*I) hz (by simp) (by simpa using ht)
  simpa using h

private theorem contourKernel_far_bound (z w : ℂ) (hz : stripWidth ≤ z.im)
    (hx : 0 ≤ w.re) (hy : 0 ≤ w.im) {T : ℝ} (hT : Real.exp (z.re+1) ≤ T)
    (hn : T ≤ ‖1+w‖) (hfar : T ≤ w.re+w.im) :
    ‖contourKernel z w‖ ≤ Real.exp (-T) := by
  rw [norm_contourKernel,Real.exp_le_exp]
  refine (contour_exponent_le z w hz hx hy).trans ?_
  have hlog := Real.log_le_log (Real.exp_pos (z.re+1)) (hT.trans hn)
  rw [Real.log_exp] at hlog
  have h := mul_le_mul_of_nonneg_left (by linarith : z.re-Real.log ‖1+w‖ ≤ -1) hx
  linarith

private theorem imagKernel_integrable (z : ℂ) (hz : stripWidth ≤ z.im) :
    IntegrableOn (fun t : ℝ => contourKernel z ((t:ℂ)*I)) (Ioi 0) := by
  refine (integrableOn_exp_neg_Ioi 0).mono' (by unfold contourKernel; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact contourKernel_imag_bound z hz ht.le

private theorem rotate (z : ℂ) (hz : stripWidth ≤ z.im) :
    entireStrip z = I*(∫ t in Ioi (0:ℝ), contourKernel z ((t:ℂ)*I)) := by
  let bottom (T : ℝ) : ℂ := ∫ t in (0:ℝ)..T, realKernel z t
  let top (T : ℝ) : ℂ := ∫ t in (0:ℝ)..T, contourKernel z ((t:ℂ)+(T:ℂ)*I)
  let right (T : ℝ) : ℂ := ∫ t in (0:ℝ)..T, contourKernel z ((T:ℂ)+(t:ℂ)*I)
  let left (T : ℝ) : ℂ := ∫ t in (0:ℝ)..T, contourKernel z ((t:ℂ)*I)
  have hT (T : ℝ) (hT : 0 ≤ T) : bottom T - I*left T = top T - I*right T := by
    have hD : DifferentiableOn ℂ (contourKernel z) ((Icc (0:ℝ) T) ×ℂ (Icc (0:ℝ) T)) := by
      intro w hw
      exact (contourKernel_differentiable z hw.1.1).differentiableWithinAt
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (contourKernel z) (⟨0,0⟩:ℂ) (⟨T,T⟩:ℂ)
      (by simpa only [uIcc_of_le hT] using hD)
    change ((∫ t in (0:ℝ)..T, contourKernel z ((t:ℂ)+(0:ℝ)*I))-top T+
      I*right T - I*(∫ t in (0:ℝ)..T, contourKernel z ((0:ℝ)+(t:ℂ)*I))) = 0 at h
    simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_add] at h
    have hbot : (∫ t in (0:ℝ)..T, contourKernel z (t:ℂ)) = bottom T :=
      intervalIntegral.integral_congr (fun t ht => contourKernel_eq_real z ((uIcc_of_le hT ▸ ht).1))
    rw [hbot] at h
    change bottom T - top T + I*right T - I*left T=0 at h
    linear_combination h
  have hboundTop : ∀ᶠ T : ℝ in atTop, ‖top T‖ ≤ T*Real.exp (-T) := by
    filter_upwards [eventually_ge_atTop (Real.exp (z.re+1))] with T hT
    have hT0 : 0 ≤ T := (Real.exp_pos _).le.trans hT
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-T)) ?_).trans_eq ?_
    · intro t ht
      rw [uIoc_of_le hT0] at ht
      apply contourKernel_far_bound _ _ hz (by simpa using ht.1.le) (by simpa using hT0) hT
      · have h := Complex.abs_im_le_norm (1+((t:ℂ)+(T:ℂ)*I))
        simpa [Complex.add_im,Complex.mul_im,abs_of_nonneg hT0] using h
      · simpa [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] using
          (le_add_of_nonneg_left ht.1.le : T≤t+T)
    · rw [sub_zero,abs_of_nonneg hT0,mul_comm]
  have hboundRight : ∀ᶠ T : ℝ in atTop, ‖right T‖ ≤ T*Real.exp (-T) := by
    filter_upwards [eventually_ge_atTop (Real.exp (z.re+1))] with T hT
    have hT0 : 0 ≤ T := (Real.exp_pos _).le.trans hT
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-T)) ?_).trans_eq ?_
    · intro t ht
      rw [uIoc_of_le hT0] at ht
      apply contourKernel_far_bound _ _ hz (by simpa using hT0) (by simpa using ht.1.le) hT
      · have h := Complex.re_le_norm (1+((T:ℂ)+(t:ℂ)*I))
        exact (le_add_of_nonneg_left zero_le_one).trans (by simpa [Complex.add_re,Complex.mul_re] using h)
      · simpa [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] using
          (le_add_of_nonneg_right ht.1.le : T≤T+t)
    · rw [sub_zero,abs_of_nonneg hT0,mul_comm]
  have hlim : Tendsto (fun T : ℝ => T*Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have htop := squeeze_zero_norm' hboundTop hlim
  have hright := squeeze_zero_norm' hboundRight hlim
  have hbottom := intervalIntegral_tendsto_integral_Ioi 0 (realKernel_integrable z) tendsto_id
  have hleft := intervalIntegral_tendsto_integral_Ioi 0 (imagKernel_integrable z hz) tendsto_id
  have hl := hbottom.sub (tendsto_const_nhds.mul hleft : Tendsto (fun T => I*left T) atTop _)
  have hr := htop.sub (tendsto_const_nhds.mul hright : Tendsto (fun T => I*right T) atTop _)
  have hE := tendsto_nhds_unique_of_eventuallyEq hl hr (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT0 using hT T hT0)
  apply sub_eq_zero.mp
  simpa [entireStrip] using hE

private theorem strip_conj (z : ℂ) : entireStrip (conj z) = conj (entireStrip z) := by
  have h (t : ℝ) : realKernel (conj z) t = conj (realKernel z t) := by
    simp [realKernel,← Complex.exp_conj,map_mul,map_sub]
  simp only [entireStrip,h,integral_conj]

/-- The strip function is bounded by one whenever the imaginary coordinate is separated from zero. -/
theorem entireStrip_norm_le_one (z : ℂ) (hz : stripWidth ≤ |z.im|) :
    ‖entireStrip z‖ ≤ 1 := by
  have aux (w : ℂ) (hw : stripWidth ≤ w.im) : ‖entireStrip w‖ ≤ 1 := by
    rw [rotate w hw,norm_mul,Complex.norm_I,one_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_exp_neg_Ioi_zero]
    apply integral_mono_of_nonneg (.of_forall (fun _ => norm_nonneg _)) (integrableOn_exp_neg_Ioi 0)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact contourKernel_imag_bound w hw ht.le
  by_cases h : 0 ≤ z.im
  · exact aux z (by simpa only [abs_of_nonneg h] using hz)
  · have hh := aux (conj z) (by simpa only [Complex.conj_im,abs_of_neg (lt_of_not_ge h)] using hz)
    simpa only [strip_conj,Complex.norm_conj] using hh

end LemniscateUpper

/-
An exact circle-potential identity for the density derived from a holomorphic derivative.
-/

noncomputable section

open Set Metric MeasureTheory Filter Complex
open scoped Real Topology ComplexConjugate

namespace LemniscateUpper

def circle (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem norm_circle (θ : ℝ) : ‖circle θ‖ = 1 := by simp [circle,norm_circleMap_zero]

private theorem circle_ne_zero (θ : ℝ) : circle θ ≠ 0 := norm_ne_zero_iff.mp (by simp [norm_circle])

theorem periodic_circle : Function.Periodic circle (2*π) := periodic_circleMap 0 1

private theorem circle_full : circle (2*π) = circle 0 := by simpa only [zero_add] using periodic_circle 0

private theorem hder_circle (θ : ℝ) : HasDerivAt circle (circle θ*I) θ := hasDerivAt_circleMap 0 1 θ

private theorem circle_has_norm_one (w : ℂ) (hw : ‖w‖ = 1) :
    w*conj w = 1 := by
  rw [Complex.mul_conj,← Complex.sq_norm,hw]
  norm_num

private theorem conj_eq_inv_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : conj w = w⁻¹ := by
  rw [Complex.inv_def,← Complex.sq_norm,hw]
  norm_num

def boundaryLog (z : ℂ) (t : ℝ) : ℝ := Real.log ‖z-circle t‖

def angularMode (H : ℂ → ℂ) (t : ℝ) : ℝ := (circle t * deriv H (circle t)).re

def density (H : ℂ → ℂ) (A : ℝ) (t : ℝ) : ℝ := 1 - angularMode H t / A

private theorem continuous_circle : Continuous circle := continuous_circleMap 0 1

theorem boundaryLog_continuous {z : ℂ} (hz : ‖z‖ ≠ 1) : Continuous (boundaryLog z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : ‖z-circle t‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    exact hz ((congrArg norm (sub_eq_zero.mp h)).trans (norm_circle t))
  have hc : Continuous (fun t => ‖z-circle t‖) := (continuous_const.sub continuous_circle).norm
  exact ContinuousAt.comp' (f := fun t : ℝ => ‖z-circle t‖) (Real.continuousAt_log hn) hc.continuousAt

theorem density_continuous {H : ℂ → ℂ} (hH : Differentiable ℂ H) (A : ℝ) :
    Continuous (density H A) := by
  have hHd : Continuous (deriv H) := hH.deriv.continuous
  unfold density angularMode
  exact continuous_const.sub ((Complex.continuous_re.comp
    (continuous_circle.mul (hHd.comp continuous_circle))).div_const _)

private def reflectedLog (z w : ℂ) : ℂ := Complex.log (1-conj z*w)

private def angleLog (z : ℂ) (t : ℝ) : ℂ := Complex.log (1-z/circle t)

private theorem reflectedLog_positive {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    0 < (1-conj z*w).re := by
  have h : ‖conj z*w‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw).trans_lt hz
  simpa only [Complex.sub_re,Complex.one_re,sub_pos] using (Complex.re_le_norm _).trans_lt h

private theorem angleLog_positive {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    0 < (1-z/circle t).re := by
  have h : ‖z/circle t‖ < 1 := by rwa [norm_div,norm_circle,div_one]
  simpa only [Complex.sub_re,Complex.one_re,sub_pos] using (Complex.re_le_norm _).trans_lt h

private theorem reflectedLog_analytic {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (reflectedLog z) (closedBall (0:ℂ) 1) := by
  intro w hw
  have h : AnalyticAt ℂ (fun w : ℂ => 1-conj z*w) w := by fun_prop
  exact h.clog (Or.inl (reflectedLog_positive hz (mem_closedBall_zero_iff.mp hw)))

private theorem circle_log_conj {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    angleLog z t = conj (reflectedLog z (circle t)) := by
  have hre := reflectedLog_positive hz (norm_circle t).le
  have harg := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre.le)
  have hne : (1-conj z*circle t).arg ≠ π := by intro h; linarith [harg,Real.pi_pos]
  rw [reflectedLog,← Complex.log_conj _ hne,map_sub,map_one,map_mul,Complex.conj_conj,
    conj_eq_inv_of_norm_one (norm_circle t),angleLog,div_eq_mul_inv]

private theorem angleLog_re {z : ℂ} (t : ℝ) : (angleLog z t).re = boundaryLog z t := by
  rw [angleLog,boundaryLog,Complex.log_re,
    show 1-z/circle t = (circle t-z)/circle t by field_simp [circle_ne_zero],norm_div,norm_circle,div_one,norm_sub_rev]

private theorem angleLog_deriv {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    HasDerivAt (angleLog z) (I*z/(circle t-z)) t := by
  have hw : circle t - z ≠ 0 := by
    intro h
    have H := congrArg norm (sub_eq_zero.mp h)
    rw [norm_circle] at H
    linarith
  have hk := ((hasDerivAt_const t z).div (hder_circle t) (circle_ne_zero t)).const_sub (1:ℂ)
  have h := (Complex.hasDerivAt_log (Or.inl (angleLog_positive hz t))).scomp t hk
  refine h.congr_deriv ?_
  simp only [smul_eq_mul]
  change -((0*circle t-z*(circle t*I))/(circle t)^2) * (1-z/circle t)⁻¹ = I*z/(circle t-z)
  field_simp [circle_ne_zero t, hw, show 1-z/circle t≠0 from Complex.slitPlane_ne_zero (Or.inl (angleLog_positive hz t))]
  ring

private theorem circle_eval {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (closedBall (0:ℂ) 1))
    {z : ℂ} (hz : ‖z‖<1) :
    (∫ θ in (0:ℝ)..2*π, (circle θ/(circle θ-z))*F (circle θ)) = (2*(π:ℂ))*F z := by
  have hC := (hF.diffContOnCl_ball subset_rfl).circleIntegral_sub_inv_smul (mem_ball_zero_iff.mpr hz)
  rw [circleIntegral] at hC
  simp only [deriv_circleMap,smul_eq_mul] at hC
  change (∫ θ in (0:ℝ)..2*π, (circle θ*I)*((circle θ-z)⁻¹*F (circle θ))) = _ at hC
  have hpoint (θ : ℝ) :
      (circle θ*I)*((circle θ-z)⁻¹*F (circle θ)) =
      I*((circle θ/(circle θ-z))*F (circle θ)) := by ring
  simp_rw [hpoint,intervalIntegral.integral_const_mul] at hC
  apply mul_left_cancel₀ I_ne_zero
  calc
    _ = (2*(π:ℂ)*I)*F z := hC
    _ = _ := by ring

private theorem circle_mean {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (closedBall (0:ℂ) 1)) :
    (∫ θ in (0:ℝ)..2*π, F (circle θ)) = (2*(π:ℂ))*F 0 := by
  simpa only [sub_zero,div_self (circle_ne_zero _),one_mul] using circle_eval hF (z := 0) (by simp)

private theorem angleLog_prod {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hH0 : H 0 = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ θ in (0:ℝ)..2*π, angleLog z θ * (circle θ * deriv H (circle θ))) = -(2*(π:ℂ))*H z := by
  let G (θ : ℝ) := angleLog z θ * (circle θ * deriv H (circle θ))
  let K (θ : ℝ) := (z/(circle θ-z))*H (circle θ)
  have hR (t : ℝ) : circle t - z ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [norm_circle] at he
    linarith
  have hG : Continuous G := (continuous_iff_continuousAt.mpr (fun t =>
    (angleLog_deriv hz t).continuousAt)).mul
    (continuous_circle.mul (hH.deriv.continuous.comp continuous_circle))
  have hK : Continuous K := (continuous_const.div (continuous_circle.sub continuous_const) hR).mul
    (hH.continuous.comp continuous_circle)
  have hD (t : ℝ) : HasDerivAt (fun u => angleLog z u * H (circle u)) (I*(G t+K t)) t := by
    have hh := (hH (circle t)).hasDerivAt.scomp t (hder_circle t)
    have he := (angleLog_deriv hz t).mul hh
    refine he.congr_deriv ?_
    simp only [G,K,Function.comp_apply,smul_eq_mul]
    ring
  have hSame : angleLog z (2*π) = angleLog z 0 := by rw [angleLog,angleLog,circle_full]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    ((continuous_const.mul (hG.add hK)).intervalIntegrable (μ := volume) 0 (2*π))
  rw [hSame,circle_full,sub_self,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hG.intervalIntegrable _ _) (hK.intervalIntegrable _ _)] at hFTC
  have hGK := (mul_eq_zero.mp hFTC).resolve_left Complex.I_ne_zero
  have hIntK : (∫ t in (0:ℝ)..2*π,K t) = (2*(π:ℂ))*H z := by
    have he (t : ℝ) : K t = (circle t/(circle t-z))*H (circle t)-H (circle t) := by
      dsimp [K]
      field_simp [hR t]
      ring
    simp_rw [he]
    have hc : Continuous (fun t => H (circle t)) := hH.continuous.comp continuous_circle
    rw [intervalIntegral.integral_sub _ (hc.intervalIntegrable 0 (2*π)),
      circle_eval hH.differentiableOn hz,circle_mean hH.differentiableOn,hH0,mul_zero,sub_zero]
    exact (((continuous_circle.div (continuous_circle.sub continuous_const) hR).mul
      (hH.continuous.comp continuous_circle))).intervalIntegrable _ _
  rw [hIntK] at hGK
  change (∫ θ in (0:ℝ)..2*π, G θ) = _
  linear_combination hGK

theorem density_integral {H : ℂ → ℂ} (hH : Differentiable ℂ H) (A : ℝ) :
    (∫ θ in (0:ℝ)..2*π, density H A θ) = 2*π := by
  let G (w : ℂ) := w*deriv H w
  have hG : Differentiable ℂ G := differentiable_id.mul hH.deriv
  have hz : G 0 = 0 := by simp [G]
  have hC : Continuous (fun t => G (circle t)) := hG.continuous.comp continuous_circle
  have hmode : (∫ t in (0:ℝ)..2*π, angularMode H t) = 0 := by
    change (∫ t in (0:ℝ)..2*π, Complex.reCLM (G (circle t))) = _
    rw [Complex.reCLM.intervalIntegral_comp_comm (hC.intervalIntegrable _ _),circle_mean hG.differentiableOn,hz,mul_zero]
    rfl
  unfold density
  have hM : Continuous (angularMode H) := Complex.continuous_re.comp hC
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    ((hM.div_const A).intervalIntegrable _ _),intervalIntegral.integral_div,hmode,
    zero_div,sub_zero,intervalIntegral.integral_const]
  simp

/-- The logarithmic potential inside the unit disk, before normalization by circle length. -/
theorem density_potential_inside {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hH0 : H 0 = 0)
    (A : ℝ) (hA : A ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ t in (0:ℝ)..2*π, boundaryLog z t * density H A t) = (π/A)*(H z).re := by
  let G (w : ℂ) := w*deriv H w
  let J := reflectedLog z
  let Q := angleLog z
  have hG : Differentiable ℂ G := differentiable_id.mul hH.deriv
  have hJ : AnalyticOnNhd ℂ J (closedBall (0:ℂ) 1) := reflectedLog_analytic hz
  have hC : Continuous (fun θ => J (circle θ)) :=
    continuousOn_univ.mp (hJ.continuousOn.comp continuous_circle.continuousOn
      (fun t _ => mem_closedBall_zero_iff.mpr (norm_circle t).le))
  have hCG : Continuous (fun t => G (circle t)) := hG.continuous.comp continuous_circle
  have hCQ : Continuous Q :=
    continuous_iff_continuousAt.mpr (fun t => (angleLog_deriv hz t).continuousAt)
  have hJ0 : J 0 = 0 := by simp [J,reflectedLog]
  have he (t : ℝ) : boundaryLog z t = (J (circle t)).re := by
    have h := congrArg Complex.re (circle_log_conj hz t)
    simpa only [angleLog_re,Complex.conj_re] using h
  have hOne : (∫ t in (0:ℝ)..2*π, boundaryLog z t) = 0 := by
    simp_rw [he]
    change (∫ t in (0:ℝ)..2*π, Complex.reCLM (J (circle t))) = _
    rw [Complex.reCLM.intervalIntegral_comp_comm (hC.intervalIntegrable _ _),circle_mean hJ.differentiableOn,
      hJ0,mul_zero]
    rfl
  have hpt (t : ℝ) : boundaryLog z t * angularMode H t =
      ((J (circle t)*G (circle t)).re+(Q t*G (circle t)).re)/2 := by
    rw [he,show Q t = conj (J (circle t)) from circle_log_conj hz t]
    change (J (circle t)).re * (G (circle t)).re = _
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hCGJ : Continuous (fun t => J (circle t)*G (circle t)) := hC.mul hCG
  have hCGQ : Continuous (fun t => Q t*G (circle t)) := hCQ.mul hCG
  have hTwo : (∫ t in (0:ℝ)..2*π, boundaryLog z t * angularMode H t) = -π*(H z).re := by
    simp_rw [hpt]
    have hJr : Continuous (fun t => (J (circle t)*G (circle t)).re) := Complex.continuous_re.comp hCGJ
    have hQr : Continuous (fun t => (Q t*G (circle t)).re) := Complex.continuous_re.comp hCGQ
    rw [intervalIntegral.integral_div,intervalIntegral.integral_add
      (hJr.intervalIntegrable _ _) (hQr.intervalIntegrable _ _)]
    change ((∫ t in (0:ℝ)..2*π, Complex.reCLM (J (circle t)*G (circle t))) +
      (∫ t in (0:ℝ)..2*π, Complex.reCLM (Q t*G (circle t))))/2 = _
    rw [Complex.reCLM.intervalIntegral_comp_comm (hCGJ.intervalIntegrable _ _),
      Complex.reCLM.intervalIntegral_comp_comm (hCGQ.intervalIntegrable _ _)]
    have hpre : (∫ t in (0:ℝ)..2*π, J (circle t)*G (circle t)) = 0 := by
      change (∫ t in (0:ℝ)..2*π, (J*G) (circle t)) = 0
      rw [circle_mean (hJ.differentiableOn.mul hG.differentiableOn),Pi.mul_apply,hJ0,zero_mul,mul_zero]
    have hnext : (∫ t in (0:ℝ)..2*π, Q t*G (circle t)) = -(2*(π:ℂ))*H z :=
      angleLog_prod hH hH0 hz
    rw [hpre,hnext,map_zero,zero_add]
    change ((-(2*(π:ℂ))*H z).re)/2 = _
    rw [show -(2*(π:ℂ))=((-(2*π):ℝ):ℂ) by push_cast; rfl,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hB := boundaryLog_continuous hz.ne
  have hM : Continuous (angularMode H) := Complex.continuous_re.comp hCG
  simp_rw [density,mul_sub,mul_one,← mul_div_assoc]
  have hBM : Continuous (fun t => boundaryLog z t*angularMode H t/A) := (hB.mul hM).div_const A
  rw [intervalIntegral.integral_sub (hB.intervalIntegrable _ _)
    (hBM.intervalIntegrable _ _),intervalIntegral.integral_div,hOne,hTwo]
  field_simp
  ring

theorem midpointReflection_norm {z : ℂ} (hz : 1 < ‖z‖) : ‖(conj z)⁻¹‖ < 1 := by
  rw [norm_inv,Complex.norm_conj,inv_lt_one_iff₀]
  exact Or.inr hz

theorem midpointReflection_im {z : ℂ} (_hz : 1 < ‖z‖) :
    |((conj z)⁻¹).im| = |z.im|/‖z‖^2 := by
  rw [Complex.inv_im,Complex.conj_im,neg_neg,Complex.normSq_conj,← Complex.sq_norm,abs_div,
    abs_of_nonneg (sq_nonneg ‖z‖)]

private theorem boundaryLog_reflection {z : ℂ} (hz : 1 < ‖z‖) (t : ℝ) :
    boundaryLog z t = Real.log ‖z‖+boundaryLog ((conj z)⁻¹) t := by
  let w := circle t
  have hw : ‖w‖=1 := norm_circle t
  have hz0 : z≠0 := norm_ne_zero_iff.mp (by linarith)
  have hcz : conj z≠0 := (map_ne_zero conj).mpr hz0
  have h : (w-(conj z)⁻¹)*conj w = conj ((z-w)/z) := by
    rw [map_div₀,map_sub,sub_mul,circle_has_norm_one w hw,sub_div,div_self hcz,div_eq_mul_inv]
    ring
  have h' := congrArg norm h
  rw [norm_mul,Complex.norm_conj,hw,mul_one,Complex.norm_conj,norm_div,norm_sub_rev w] at h'
  have hn : ‖z-w‖ = ‖z‖*‖(conj z)⁻¹-w‖ := by
    have he := (eq_div_iff (norm_ne_zero_iff.mpr hz0)).mp h'
    simpa only [mul_comm] using he.symm
  have hp : (conj z)⁻¹-w ≠ 0 := by
    intro h
    have H := congrArg norm (sub_eq_zero.mp h)
    rw [hw] at H
    exact (midpointReflection_norm hz).ne H
  change Real.log ‖z-w‖ = Real.log ‖z‖ + Real.log ‖(conj z)⁻¹-w‖
  rw [hn,Real.log_mul (norm_ne_zero_iff.mpr hz0) (norm_ne_zero_iff.mpr hp)]

theorem density_potential_outside {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hH0 : H 0 = 0)
    (A : ℝ) (hA : A ≠ 0) {z : ℂ} (hz : 1 < ‖z‖) :
    (∫ t in (0:ℝ)..2*π, boundaryLog z t*density H A t) =
      Real.log ‖z‖*(2*π)+(π/A)*(H ((conj z)⁻¹)).re := by
  have hc := density_continuous hH A
  have h1 : Continuous (fun t => Real.log ‖z‖ * density H A t) := continuous_const.mul hc
  have h2 : Continuous (fun t => boundaryLog ((conj z)⁻¹) t*density H A t) :=
    (boundaryLog_continuous (midpointReflection_norm hz).ne).mul hc
  simp_rw [boundaryLog_reflection hz,add_mul]
  rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,density_integral hH A,
    density_potential_inside hH hH0 A hA (midpointReflection_norm hz)]

private theorem abs_log_difference_le {x y d : ℝ} (hd : 0 < d) (hx : d≤x) (hy : d≤y) :
    |Real.log x-Real.log y| ≤ (d⁻¹)*|x-y| := by
  have hx' := hd.trans_le hx
  have hy' := hd.trans_le hy
  have haux {a b : ℝ} (ha : d≤a) (hb : d≤b) (hab : a≤b) :
      Real.log b-Real.log a ≤ d⁻¹*(b-a) := by
    have ha' := hd.trans_le ha
    have hb' := hd.trans_le hb
    rw [← Real.log_div hb'.ne' ha'.ne']
    calc
      _ ≤ b/a-1 := Real.log_le_sub_one_of_pos (div_pos hb' ha')
      _ = (b-a)/a := by field_simp
      _ ≤ (b-a)/d := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hd ha
      _ = _ := by ring
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx' h)),abs_of_nonpos (sub_nonpos.mpr h)]
    simpa only [neg_sub] using haux hx hy h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy' h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact haux hy hx h

theorem boundaryLog_lipschitz {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : d ≤ |‖z‖-1|)
    (s t : ℝ) :
    |boundaryLog z s-boundaryLog z t| ≤ d⁻¹*|s-t| := by
  have hN (j : ℝ) : d ≤ ‖z-circle j‖ := hz.trans (by
    simpa only [norm_circle] using abs_norm_sub_norm_le z (circle j))
  refine (abs_log_difference_le hd (hN s) (hN t)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hd.le)
  have hDiff : |‖z-circle s‖-‖z-circle t‖| ≤ ‖circle s-circle t‖ := by
    have h := abs_norm_sub_norm_le (z-circle s) (z-circle t)
    convert h using 1
    rw [show z-circle s-(z-circle t) = -(circle s-circle t) by ring,norm_neg]
  refine hDiff.trans ?_
  have h := (lipschitzWith_circleMap 0 1).dist_le_mul s t
  simpa [circle,dist_eq_norm,Real.norm_eq_abs] using h

end LemniscateUpper

/-
Equal-mass quadrature with a lower bound on the angular density.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Real Topology BigOperators

namespace LemniscateUpper

private theorem sum_integral_adjacent (a : ℕ → ℝ) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ t in a i..a (i+1), f t) = ∫ t in a 0..a n, f t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

/-- Choose the sample points simultaneously for every Lipschitz test function. -/
theorem exists_equal_mass_samples {T : ℝ} (hT : 0 < T) {v : ℝ → ℝ} (hv : Continuous v)
    (hvlo : ∀ t∈Icc 0 T, (1/2:ℝ) ≤ v t)
    (hvm : (∫ t in (0:ℝ)..T,v t) = T) {n : ℕ} (hn : 0 < n) :
    ∃ θ : Fin n → ℝ, ∀ G : ℝ → ℝ, Continuous G → ∀ L : ℝ, 0 ≤ L →
      (∀ t t', |G t-G t'| ≤ L*|t-t'|) →
      (∫ t in (0:ℝ)..T, G t*v t) ≤
        (∑ i, G (θ i))*(T/n) + (2*T/n)*L*T := by
  classical
  let D (t : ℝ) := ∫ u in (0:ℝ)..t,v u
  have hDn (t : ℝ) : HasDerivAt D (v t) t :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
      hv.stronglyMeasurable.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hD : Continuous D := continuous_iff_continuousAt.mpr (fun t => (hDn t).continuousAt)
  have hD0 : D 0 = 0 := by simp [D]
  have hDT : D T = T := hvm
  have idiff (a b : ℝ) : (∫ t in a..b, v t) = D b - D a := by
    apply eq_sub_of_add_eq
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals (hv.intervalIntegrable _ _)
      (hv.intervalIntegrable _ _)
  have hDiff {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b∈Icc 0 T) (hab : a ≤ b) :
      (b-a)/2 ≤ D b-D a := by
    rw [← idiff]
    calc
      _ = ∫ t in a..b, (1/2:ℝ) := by simp [intervalIntegral.integral_const,smul_eq_mul,div_eq_mul_inv]
      _ ≤ _ := intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _)
        (hv.intervalIntegrable _ _) (fun t ht => hvlo t ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  let mass (i : ℕ) : ℝ := (i:ℝ)*(T/n)
  have ht (i : ℕ) (hi : i ≤ n) : ∃ t ∈ Icc 0 T, D t = mass i := by
    apply intermediate_value_Icc hT.le hD.continuousOn
    rw [hD0,hDT]
    refine ⟨by dsimp [mass]; positivity,?_⟩
    have h : (i:ℝ) ≤ n := by exact_mod_cast hi
    dsimp [mass]
    calc
      _ ≤ (n:ℝ)*(T/n) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by field_simp
  let θ (i : ℕ) := if hi : i≤n then (ht i hi).choose else 0
  have hθ (i : ℕ) (hi : i≤n) : θ i ∈ Icc 0 T ∧ D (θ i) = mass i :=
    by simpa only [θ,dif_pos hi] using (ht i hi).choose_spec
  have hθ0 : θ 0 = 0 := by
    have h0 := hθ 0 (Nat.zero_le n)
    have h := hDiff (left_mem_Icc.mpr hT.le) h0.1 h0.1.1
    rw [h0.2,hD0] at h
    simp only [mass,Nat.cast_zero,zero_mul,sub_zero] at h
    linarith [h0.1.1]
  have hθn : θ n = T := by
    have h0 := hθ n le_rfl
    have h := hDiff h0.1 (right_mem_Icc.mpr hT.le) h0.1.2
    rw [hDT,h0.2,show mass n=T by dsimp [mass]; field_simp,sub_self] at h
    linarith [h0.1.2]
  have hMono {i j : ℕ} (hij : i≤j) (hj : j≤n) : θ i ≤ θ j := by
    by_contra! H
    have hi := hij.trans hj
    have hr := hDiff (hθ j hj).1 (hθ i hi).1 H.le
    rw [(hθ i hi).2,(hθ j hj).2] at hr
    have hp : mass i ≤ mass j := by
      dsimp [mass]
      gcongr
    linarith
  have hseg (i : ℕ) (hi : i<n) : (∫ t in θ i..θ (i+1),v t) = T/n := by
    rw [idiff,(hθ (i+1) (Nat.succ_le_of_lt hi)).2,(hθ i hi.le).2]
    dsimp [mass]
    push_cast
    ring
  have hlen (i : ℕ) (hi : i<n) : θ (i+1)-θ i ≤ 2*T/n := by
    have hl := hDiff (hθ i hi.le).1 (hθ (i+1) (Nat.succ_le_of_lt hi)).1
      (hMono (Nat.le_succ i) (Nat.succ_le_of_lt hi))
    rw [← idiff,hseg i hi] at hl
    rw [mul_div_assoc]
    linarith
  refine ⟨fun i => θ i.val,fun G hG L hL hLip => ?_⟩
  have hGV : Continuous (fun t => G t*v t) := hG.mul hv
  have hloc (i : ℕ) (hi : i<n) :
      (∫ t in θ i..θ (i+1),G t*v t) ≤ (G (θ i)+(2*T/n)*L)*(T/n) := by
    have hi' := Nat.succ_le_of_lt hi
    rw [← hseg i hi,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (hMono (Nat.le_succ i) hi')
      (hGV.intervalIntegrable _ _) ((continuous_const.mul hv).intervalIntegrable _ _)
    intro t ht
    have hvp := hvlo t ⟨(hθ i hi.le).1.1.trans ht.1,ht.2.trans (hθ (i+1) hi').1.2⟩
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have h := (le_abs_self (G t-G (θ i))).trans (hLip t (θ i))
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at h
    have he := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 (θ i)) hL
    have hd := mul_le_mul_of_nonneg_left (hlen i hi) hL
    linarith [show L*(2*T/n)=(2*T/n)*L by ring]
  calc
    _ = ∑ i ∈ Finset.range n, ∫ t in θ i..θ (i+1),G t*v t := by
      rw [sum_integral_adjacent θ hGV,hθ0,hθn]
    _ ≤ ∑ i ∈ Finset.range n, (G (θ i)+(2*T/n)*L)*(T/n) :=
      Finset.sum_le_sum (fun i hi => hloc i (Finset.mem_range.mp hi))
    _ = _ := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
        (Fin.sum_univ_eq_sum_range (fun i => G (θ i)) n)]
      field_simp

end LemniscateUpper

namespace LemniscateUpper

def areaConstant : ℝ := 32*stripWidth+4*π

theorem stripWidth_pos : 0 < stripWidth := by unfold stripWidth; linarith [Real.pi_pos]

theorem areaConstant_pos : 0 < areaConstant :=
  add_pos (mul_pos (by norm_num) stripWidth_pos) (mul_pos (by norm_num) Real.pi_pos)

private theorem volume_rectangle (d : ℝ) (_hd : 0 ≤ d) :
    volume (Complex.measurableEquivRealProd ⁻¹' (Icc (-2:ℝ) 2 ×ˢ Icc (-d) d)) =
      ENNReal.ofReal (8*d) := by
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet]
  change ((volume:Measure ℝ).prod volume) (Icc (-2:ℝ) 2 ×ˢ Icc (-d) d) = _
  rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc,← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

private theorem ball_volume_eq (r : ℝ) (hr : 0 ≤ r) :
    volume (ball (0:ℂ) r) = ENNReal.ofReal (r^2*π) := by
  rw [Complex.volume_ball,← ENNReal.ofReal_pow hr,← ENNReal.ofReal_coe_nnreal (p:=NNReal.pi),
    ← ENNReal.ofReal_mul (sq_nonneg _),NNReal.coe_real_pi]

private theorem closedBall_volume_eq (r : ℝ) (hr : 0 ≤ r) :
    volume (closedBall (0:ℂ) r) = ENNReal.ofReal (r^2*π) := by
  rw [Complex.volume_closedBall,← ENNReal.ofReal_pow hr,← ENNReal.ofReal_coe_nnreal (p:=NNReal.pi),
    ← ENNReal.ofReal_mul (sq_nonneg _),NNReal.coe_real_pi]

theorem bad_region_volume {R : ℝ} (hR : 1 < R) :
    volume {z : ℂ | ‖z‖<2 ∧ (|z.im|<4*stripWidth/R ∨ |‖z‖-1|<R⁻¹)} ≤
      ENNReal.ofReal (areaConstant/R) := by
  let d := 4*stripWidth/R
  let e := R⁻¹
  let A := Complex.measurableEquivRealProd ⁻¹' (Icc (-2:ℝ) 2 ×ˢ Icc (-d) d)
  let B := ball (0:ℂ) (1+e) \ closedBall 0 (1-e)
  have hd : 0 ≤ d := div_nonneg (by have := stripWidth_pos; positivity) (by linarith)
  have he : 0 < e := inv_pos.mpr (by linarith)
  have he1 : e < 1 := inv_lt_one_iff₀.mpr (Or.inr hR)
  have hA : volume A = ENNReal.ofReal (8*d) := volume_rectangle d hd
  have hsubB : closedBall (0:ℂ) (1-e) ⊆ ball 0 (1+e) :=
    closedBall_subset_ball (by linarith)
  have hB : volume B = ENNReal.ofReal (4*π*e) := by
    change volume (ball (0:ℂ) (1+e) \ closedBall 0 (1-e)) = _
    rw [measure_sdiff hsubB measurableSet_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne,
      ball_volume_eq _ (by linarith),closedBall_volume_eq _ (by linarith),
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring
  have hsub : {z : ℂ | ‖z‖<2 ∧ (|z.im|<4*stripWidth/R ∨ |‖z‖-1|<R⁻¹)} ⊆ A∪B := by
    rintro z ⟨hz,h | h⟩
    · left
      change z.re∈Icc (-2:ℝ) 2 ∧ z.im∈Icc (-d) d
      have hre := (Complex.abs_re_le_norm z).trans hz.le
      exact ⟨abs_le.mp hre,abs_le.mp h.le⟩
    · right
      have h' := abs_lt.mp h
      change z∈ball 0 (1+e) ∧ z∉closedBall 0 (1-e)
      rw [mem_ball_zero_iff,mem_closedBall_zero_iff,not_le]
      constructor <;> linarith
  calc
    _ ≤ volume (A∪B) := measure_mono hsub
    _ ≤ volume A + volume B := measure_union_le _ _
    _ = _ := by
      rw [hA,hB,← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold areaConstant
      dsimp [d,e]
      ring

def shape (R : ℝ) (z : ℂ) : ℂ := entireStrip (R:ℂ) - entireStrip ((R:ℂ)+(R:ℂ)*z)

def amplitude (R : ℝ) : ℝ := 2*R*Real.exp (Real.exp (9*R))

private theorem shape_diff (R : ℝ) : Differentiable ℂ (shape R) := by
  have := entireStrip_entire
  unfold shape
  fun_prop

private theorem shape_zero (R : ℝ) : shape R 0 = 0 := by simp [shape]

private theorem shape_deriv {R : ℝ} (z : ℂ) :
    deriv (shape R) z = -( (R:ℂ) * deriv entireStrip ((R:ℂ)+(R:ℂ)*z)) := by
  have hi : HasDerivAt (fun z : ℂ => (R:ℂ)+(R:ℂ)*z) (R:ℂ) z := by
    exact (((hasDerivAt_id z).const_mul (R:ℂ)).const_add (R:ℂ)).congr_deriv (mul_one _)
  have he := (entireStrip_entire _).hasDerivAt.scomp z hi
  exact (he.const_sub (entireStrip (R:ℂ))).deriv

private theorem shape_re_lower {R : ℝ} (hR : 10 ≤ R) {z : ℂ} (hz : stripWidth ≤ R*|z.im|) :
    2 ≤ (shape R z).re := by
  have hE := entireStrip_real_lower (by linarith : 0 ≤ R)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  have h1 : (3:ℝ) ≤ (entireStrip (R:ℂ)).re := by
    linarith [Real.add_one_le_exp (R-2*Real.log 3)]
  have hZ : stripWidth ≤ |((R:ℂ)+(R:ℂ)*z).im| := by
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,zero_mul,add_zero,
      zero_add,abs_mul,abs_of_nonneg (by linarith : 0 ≤ R)]
    exact hz
  have hB := entireStrip_norm_le_one _ hZ
  have hC := (Complex.re_le_norm (entireStrip ((R:ℂ)+(R:ℂ)*z))).trans hB
  rw [shape,Complex.sub_re]
  linarith

private theorem density_ge_half {R : ℝ} (hR : 10 ≤ R) (t : ℝ) :
    (1/2:ℝ) ≤ density (shape R) (amplitude R) t := by
  have hR0 : 0 < R := by linarith
  have hRel : ((R:ℂ)+(R:ℂ)*circle t).re ≤ 2*R := by
    have he := (Complex.re_le_norm (circle t)).trans_eq (norm_circle t)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero]
    linarith [mul_le_mul_of_nonneg_left he hR0.le]
  have hD := norm_deriv_entireStrip_le (by positivity : 0 ≤ 2*R) hRel
  have hNorm : ‖deriv (shape R) (circle t)‖ ≤ R*Real.exp (Real.exp (9*R)) := by
    rw [shape_deriv,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0.le]
    gcongr
    exact hD.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith)))
  have hM : angularMode (shape R) t ≤ R*Real.exp (Real.exp (9*R)) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul,norm_circle,one_mul]
    exact hNorm
  have hA : 0 < amplitude R := by unfold amplitude; positivity
  have h := (div_le_iff₀ hA).mpr (show angularMode (shape R) t ≤ (1/2:ℝ)*amplitude R by
    unfold amplitude; linarith)
  rw [density]
  linarith

private theorem log_prod_nonneg {n : ℕ} {a : Fin n → ℂ} {z : ℂ}
    (h0 : ∀ i, z-a i≠0)
    (h : 0 ≤ ∑ i, Real.log ‖z-a i‖) : 1 ≤ ‖∏ i, (z-a i)‖ := by
  rw [norm_prod]
  have hb : 0 < ∏ i, ‖z-a i‖ := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (h0 i))
  apply (Real.log_nonneg_iff hb).mp
  rw [Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (h0 i))]
  exact h

theorem exists_roots_area {R : ℝ} (hR : 10 ≤ R) {n : ℕ} (hn : 0 < n)
    (hsize : 4*π*R*amplitude R ≤ (n:ℝ)) :
    ∃ a : Fin n → ℂ, (∀ i, ‖a i‖ = 1) ∧
      volume {z : ℂ | ‖∏ i, (z-a i)‖ < 1} ≤ ENNReal.ofReal (areaConstant/R) := by
  let T := 2*π
  let A := amplitude R
  let H := shape R
  have hH : Differentiable ℂ H := shape_diff R
  have hH0 : H 0 = 0 := shape_zero R
  have hR0 : 0 < R := by linarith
  have hA : 0 < A := by dsimp [A,amplitude]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨θ,hθ⟩ := exists_equal_mass_samples hT (density_continuous hH A)
    (fun t _ => density_ge_half hR t) (density_integral hH A) hn
  let a (i : Fin n) := circle (θ i)
  have ha (i : Fin n) : ‖a i‖ = 1 := norm_circle _
  refine ⟨a,ha,(measure_mono ?_).trans (bad_region_volume (by linarith))⟩
  intro z hz
  have hprod : ‖∏ i, (z-a i)‖ < 1 := hz
  have hz2 : ‖z‖ < 2 := by
    by_contra! H
    have hdist (i : Fin n) : 1 ≤ ‖z-a i‖ := by
      have hb := norm_add_le (z-a i) (a i)
      rw [sub_add_cancel,ha] at hb
      linarith
    exact (not_lt_of_ge (by
      rw [norm_prod]
      exact Finset.one_le_prod (fun i _ => hdist i))) hprod
  refine ⟨hz2,?_⟩
  by_contra! hg
  have hd : 0 < R⁻¹ := inv_pos.mpr hR0
  have hzn : ‖z‖≠1 := by intro h; simpa [h,not_le.mpr hd] using hg.2
  have htest := hθ (boundaryLog z) (boundaryLog_continuous hzn) R hR0.le
    (by simpa only [inv_inv] using boundaryLog_lipschitz hd hg.2)
  have hPot : T/A ≤ ∫ t in (0:ℝ)..T, boundaryLog z t*density H A t := by
    rcases lt_or_gt_of_ne hzn with h | h
    · have hwidth : stripWidth ≤ R*|z.im| := by
        have hh := (div_le_iff₀ hR0).mp hg.1
        linarith [stripWidth_pos]
      have hRe : 2 ≤ (H z).re := shape_re_lower hR hwidth
      change T/A ≤ ∫ t in (0:ℝ)..2*π, boundaryLog z t*density H A t
      rw [density_potential_inside hH hH0 A hA.ne' h]
      calc
        _ = (π/A)*2 := by dsimp [T]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hRe (by positivity)
    · have hwidth : stripWidth ≤ R*|((conj z)⁻¹).im| := by
        rw [midpointReflection_im h]
        have hh := (div_le_iff₀ hR0).mp hg.1
        rw [← mul_div_assoc]
        apply (le_div_iff₀ (by positivity : 0<‖z‖^2)).mpr
        have hq : ‖z‖^2 ≤ 4 := by nlinarith [norm_nonneg z]
        have hl := mul_le_mul_of_nonneg_left hq stripWidth_pos.le
        nlinarith
      have hRe : 2 ≤ (H ((conj z)⁻¹)).re := shape_re_lower hR hwidth
      change T/A ≤ ∫ t in (0:ℝ)..2*π, boundaryLog z t*density H A t
      rw [density_potential_outside hH hH0 A hA.ne' h]
      calc
        _ = (π/A)*2 := by dsimp [T]; ring
        _ ≤ (π/A)*(H ((conj z)⁻¹)).re := mul_le_mul_of_nonneg_left hRe (by positivity)
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (Real.log_nonneg h.le) hT.le)
  have hErr : (2*T/n)*R*T ≤ T/A := by
    have hs : 2*T*R*A ≤ (n:ℝ) := by dsimp [T,A]; convert hsize using 1; ring
    have hx : 2*T*R/n ≤ 1/A := (div_le_div_iff₀ hn' hA).mpr (by simpa using hs)
    calc
      _ = (2*T*R/n)*T := by ring
      _ ≤ (1/A)*T := mul_le_mul_of_nonneg_right hx hT.le
      _ = _ := by ring
  have hsum : 0 ≤ ∑ i, Real.log ‖z-a i‖ := by
    have hh : 0 ≤ (∑ i, boundaryLog z (θ i))*(T/n) := by linarith [hPot.trans htest]
    exact (mul_nonneg_iff_of_pos_right (div_pos hT hn')).mp hh
  have h0 (i : Fin n) : z-a i ≠ 0 := by
    intro h
    exact hzn ((congrArg norm (sub_eq_zero.mp h)).trans (ha i))
  exact (not_lt_of_ge (log_prod_nonneg h0 hsum)) hprod

theorem amplitude_growth {R : ℝ} (hR : 10 ≤ R) :
    4*π*R*amplitude R ≤ Real.exp (Real.exp (12*R)) := by
  have hR0 : 0 ≤ R := by linarith
  have hOne : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have hsq : R*R ≤ Real.exp R*Real.exp R := mul_le_mul hOne hOne hR0 (Real.exp_pos _).le
  have hπ : 8*π ≤ Real.exp (4*R) := by linarith [Real.pi_lt_four,Real.add_one_le_exp (4*R)]
  have hL : 8*π*(R*R) ≤ Real.exp (6*R) := by
    calc
      _ ≤ Real.exp (4*R)*(Real.exp R*Real.exp R) := by gcongr
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have hEx : 6*R + Real.exp (9*R) ≤ Real.exp (12*R) := by
    calc
      _ ≤ Real.exp (9*R) + Real.exp (9*R) := by linarith [Real.add_one_le_exp (9*R)]
      _ = Real.exp (9*R)*2 := by ring
      _ ≤ Real.exp (9*R)*Real.exp (3*R) := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (3*R)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (8*π*(R*R))*Real.exp (Real.exp (9*R)) := by unfold amplitude; ring
    _ ≤ Real.exp (6*R)*Real.exp (Real.exp (9*R)) :=
      mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
    _ = Real.exp (6*R+Real.exp (9*R)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hEx

private theorem loglog_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    0 < Real.log (Real.log (n:ℝ)) := by
  have hn' : (3:ℝ)≤n := by exact_mod_cast hn
  have hl := Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans_le hn')
  rw [Real.log_exp] at hl
  exact Real.log_pos hl

private theorem zero_roots_volume {n : ℕ} (hn : 0 < n) :
    volume {z : ℂ | ‖∏ _ : Fin n, (z-(0:ℂ))‖ < 1} = ENNReal.ofReal π := by
  have he : {z : ℂ | ‖∏ _ : Fin n, (z-(0:ℂ))‖ < 1} = ball 0 1 := by
    ext z
    simp only [Set.mem_ofPred_eq,sub_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      norm_pow,mem_ball_zero_iff]
    exact pow_lt_one_iff_of_nonneg (norm_nonneg _) hn.ne'
  rw [he,ball_volume_eq _ zero_le_one,one_pow,one_mul]

end LemniscateUpper

open LemniscateUpper in
/-- The upper bound for Erdős 116 follows the potential discretization of Krishnapur, Lundberg
and Ramachandran using an elementary rotated Laplace integral for the strip function.
See https://arxiv.org/abs/2503.18270, Section 4. -/
theorem OMA.solution : type_of% @Erdos116.erdos_116.variants.upper := by
  let N := ⌈Real.exp (Real.exp (120:ℝ))⌉₊
  have hN : Real.exp (Real.exp (120:ℝ)) ≤ (N:ℝ) := Nat.le_ceil _
  let C := max (12*areaConstant) (π*Real.log (Real.log (N:ℝ)))
  refine ⟨C,?_⟩
  intro n hn
  have hn0 : 0<n := by omega
  have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hll := LemniscateUpper.loglog_pos_of_three_le hn
  by_cases h : N ≤ n
  · let R := Real.log (Real.log (n:ℝ))/12
    have hnN : Real.exp (Real.exp (120:ℝ)) ≤ (n:ℝ) := hN.trans (by exact_mod_cast h)
    have h1 := Real.log_le_log (Real.exp_pos (Real.exp (120:ℝ))) hnN
    rw [Real.log_exp] at h1
    have h2 := Real.log_le_log (Real.exp_pos (120:ℝ)) h1
    rw [Real.log_exp] at h2
    have hR : 10 ≤ R := by dsimp [R]; linarith
    have hEq : Real.exp (Real.exp (12*R)) = (n:ℝ) := by
      rw [show 12*R=Real.log (Real.log (n:ℝ)) by dsimp [R]; ring,Real.exp_log hl,Real.exp_log hn0']
    obtain ⟨a,ha,hvol⟩ := exists_roots_area hR hn0 ((amplitude_growth hR).trans_eq hEq)
    refine ⟨a,fun i => (ha i).le,hvol.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    calc
      _ = 12*areaConstant/Real.log (Real.log (n:ℝ)) := by dsimp [R]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hll.le
  · have hnN : (n:ℝ) ≤ N := by exact_mod_cast (le_of_not_ge h)
    have hm := Real.log_le_log hl (Real.log_le_log hn0' hnN)
    have hC : π ≤ C/Real.log (Real.log (n:ℝ)) := by
      apply (le_div_iff₀ hll).mpr
      exact (mul_le_mul_of_nonneg_left hm Real.pi_pos.le).trans (le_max_right _ _)
    refine ⟨fun _ => 0,by simp,?_⟩
    exact (LemniscateUpper.zero_roots_volume hn0).le.trans (ENNReal.ofReal_le_ofReal hC)