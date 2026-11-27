import OMAReductions.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1
import Mathlib

/-! Quantitative prime number theorem in logarithmic coordinates.
Partial summation expresses the counting error in terms of θ(x)−x.
The logarithmic integral in the target differs from its usual normalization
by a fixed constant, which is retained explicitly. -/
noncomputable section
open Real Filter Set Asymptotics MeasureTheory
open scoped Topology

namespace OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1_H1_R1

/-- The quantitative prime number theorem for the first Chebyshev function. -/
def H1 : Prop := ∀ A : ℝ, 0<A →
  (fun x : ℝ => Chebyshev.theta x - x) =o[atTop] fun x : ℝ => x/(log x)^A

/-- Integration against the Abel kernel preserves arbitrary logarithmic savings. -/
def H2 : Prop := ∀ f : ℝ → ℝ,
  (∀ x ≥ (3:ℝ), IntervalIntegrable (fun t => f t / (t*(log t)^2)) volume 3 x) →
  (∀ B : ℝ, 0<B → f =o[atTop] fun x : ℝ => x/(log x)^B) →
  ∀ C A : ℝ, 0<A → (fun x : ℝ => C + ∫ t in (3:ℝ)..x, f t/(t*(log t)^2))
    =o[atTop] fun x : ℝ => x/(log x)^A

lemma model_integral {x : ℝ} (hx : 3≤x) :
    let F := fun u : ℝ => ∫ t in (1:ℝ)..u, exp (max 1 t) / max 1 t
    F (log x) - x/log x - (F (log 3) - 3/log 3) = ∫ t in (3:ℝ)..x, 1/(log t)^2 := by
  intro F
  symm
  let s := fun t : ℝ => exp (max 1 t) / max 1 t
  have hc : Continuous s :=
    ((continuous_const.max continuous_id).rexp).div (continuous_const.max continuous_id)
      (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => F (log t) - t/log t)
  · intro t ht
    rw [uIcc_of_le hx] at ht
    have tp : 0<t := by linarith [ht.1]
    have lp : 1 ≤ log t := (le_log_iff_exp_le tp).mpr (exp_one_lt_three.le.trans ht.1)
    have nz : log t ≠ 0 := by linarith
    have hf : HasDerivAt F (s (log t)) (log t) := intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable _ _) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    have hl := hasDerivAt_log tp.ne'
    have h := (hf.comp t hl).sub ((hasDerivAt_id t).div hl nz)
    have hs : s (log t) = t/log t := by simp [s,max_eq_right lp, exp_log tp]
    rw [hs] at h
    convert h using 1 <;> first | rfl | (dsimp; field_simp; ring) | (field_simp; ring)
  · exact Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)

lemma theta_int {a x : ℝ} (ha : 2≤a) (hx : a≤x) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t*(log t)^2)) volume a x := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
    (fun t ht => ⟨ha.trans ht.1.le,ht.2⟩)

lemma error_int {x : ℝ} (hx : 3≤x) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.theta t-t)/(t*(log t)^2)) volume 3 x := by
  have h := (theta_int (by norm_num : (2:ℝ)≤3) hx).sub
    (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num : (1:ℝ)<3) (by linarith : 1<x))
  apply h.congr
  intro t ht
  rw [uIoc_of_le hx] at ht
  have tp : t ≠ 0 := by linarith [ht.1]
  dsimp
  field_simp

theorem main : H1 → H2 → OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1.H1 := by
  intro pnt transfer A ha
  let F := fun u : ℝ => ∫ t in (1:ℝ)..u, exp (max 1 t) / max 1 t
  let C := (∫ t in (2:ℝ)..3, Chebyshev.theta t/(t*(log t)^2)) - (F (log 3) - 3/log 3)
  have i := transfer (fun t => Chebyshev.theta t-t) (fun _ h => error_int h) pnt C A ha
  have endpoint : (fun x : ℝ => (Chebyshev.theta x-x)/log x) =O[atTop]
      fun x : ℝ => Chebyshev.theta x-x := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (3:ℝ)] with t ht
    have lp : 1 ≤ log t := (le_log_iff_exp_le (by linarith)).mpr (exp_one_lt_three.le.trans ht)
    rw [norm_div,Real.norm_eq_abs (log t),abs_of_nonneg (by linarith)]
    exact div_le_self (norm_nonneg _) lp
  have combined := ((endpoint.trans_isLittleO (pnt A ha)).add i).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply combined.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (3:ℕ)] with k hk
  have hx : (3:ℝ)≤k := by exact_mod_cast hk
  have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral (show (2:ℝ)≤k by linarith)
  rw [Nat.floor_natCast] at hpi
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (theta_int (by norm_num : (2:ℝ)≤2) (by norm_num : (2:ℝ)≤3))
    (theta_int (by norm_num : (2:ℝ)≤3) hx)
  have hdiff : (∫ t in (3:ℝ)..k, (Chebyshev.theta t-t)/(t*(log t)^2)) =
      (∫ t in (3:ℝ)..k, Chebyshev.theta t/(t*(log t)^2)) -
      (∫ t in (3:ℝ)..k, 1/(log t)^2) := by
    rw [← intervalIntegral.integral_sub (theta_int (by norm_num : (2:ℝ)≤3) hx)
      (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num : (1:ℝ)<3) (by linarith : (1:ℝ)<k))]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    have tp : t≠0 := by linarith [ht.1]
    field_simp
  change (Chebyshev.theta k-k)/log k + (C+_) = (k.primeCounting:ℝ)-F (log k)
  dsimp only [C]
  rw [hpi,← hjoin,hdiff,← model_integral hx]
  dsimp only [F]
  ring

end OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1_H1_R1
