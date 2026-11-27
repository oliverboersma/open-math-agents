import OMAReductions.R_Erdos297_erdos_297_R1
import Mathlib

-- Credit: the analysis below is reused verbatim from the merged proof of
-- Erdos297.erdos_297.variants.general.R1.H1 by @ivillar (PR #3616).

/-! For l <= 0 the integrand is at least 1/(2y), so the integral is undefined and equals 0.
For l > 0 the integrand is bounded by 1/l; dominated convergence gives continuity, the
integrand decreases strictly in l, the value is at least -log l/(1+e) for l < 1 and at most
1/l, and the intermediate value theorem gives the unique solution. -/

open Filter Real Finset Erdos297 MeasureTheory intervalIntegral
open scoped Topology

namespace E297P2

noncomputable def g (l y : ℝ) : ℝ := 1 / (y * (1 + Real.exp (l / y)))

theorem mass_eq (l : ℝ) : massIntegral l = ∫ y in (0:ℝ)..1, g l y := rfl

theorem g_meas (l : ℝ) : Measurable (g l) := by
  unfold g; fun_prop

theorem g_nonneg (l : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ g l y :=
  div_nonneg zero_le_one (mul_nonneg hy (by positivity))

theorem g_le (l : ℝ) (hl : 0 < l) {y : ℝ} (hy : 0 ≤ y) : g l y ≤ 1 / l := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp [g]; positivity
  · unfold g
    apply one_div_le_one_div_of_le hl
    have e := Real.add_one_le_exp (l / y)
    have : y * (l / y) = l := by field_simp
    nlinarith

theorem g_int (l : ℝ) (hl : 0 < l) : IntervalIntegrable (g l) volume 0 1 := by
  refine (intervalIntegrable_const (c := 1 / l)).mono_fun (g_meas l).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
  rw [Set.uIoc_of_le zero_le_one] at hy
  show ‖g l y‖ ≤ ‖1 / l‖
  rw [Real.norm_of_nonneg (g_nonneg l hy.1.le), Real.norm_of_nonneg (by positivity)]
  exact g_le l hl hy.1.le

theorem g_int' (l : ℝ) (hl : 0 < l) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    IntervalIntegrable (g l) volume a b :=
  (g_int l hl).mono_set (by
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb)

theorem strict_anti : StrictAntiOn massIntegral (Set.Ioi 0) := by
  intro l1 h1 l2 h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  rw [mass_eq, mass_eq, ← sub_pos, ← intervalIntegral.integral_sub (g_int l1 h1) (g_int l2 h2)]
  apply intervalIntegral_pos_of_pos_on ((g_int l1 h1).sub (g_int l2 h2)) _ zero_lt_one
  intro y hy
  rw [sub_pos]
  unfold g
  apply one_div_lt_one_div_of_lt (by have := hy.1; positivity)
  apply mul_lt_mul_of_pos_left _ hy.1
  have : l1 / y < l2 / y := div_lt_div_of_pos_right h12 hy.1
  linarith [Real.exp_lt_exp.mpr this]

theorem cont : ContinuousOn massIntegral (Set.Ioi 0) := by
  intro l0 hl0
  simp only [Set.mem_Ioi] at hl0
  apply ContinuousAt.continuousWithinAt
  have hev : ∀ᶠ l in 𝓝 l0, l0 / 2 < l := lt_mem_nhds (by linarith)
  show ContinuousAt (fun l => ∫ y in (0:ℝ)..1, g l y) l0
  apply continuousAt_of_dominated_interval (bound := fun _ => 2 / l0)
  · exact Eventually.of_forall (fun l => (g_meas l).aestronglyMeasurable)
  · filter_upwards [hev] with l hl
    refine Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hlp : 0 < l := by linarith
    show ‖g l y‖ ≤ 2 / l0
    rw [Real.norm_of_nonneg (g_nonneg l hy.1.le)]
    calc g l y ≤ 1 / l := g_le l hlp hy.1.le
      _ ≤ 2 / l0 := by rw [div_le_div_iff₀ hlp hl0]; linarith
  · exact intervalIntegrable_const
  · refine Eventually.of_forall (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 : y ≠ 0 := hy.1.ne'
    show ContinuousAt (fun l => 1 / (y * (1 + Real.exp (l / y)))) l0
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact mul_ne_zero hy0 (by positivity)

theorem nonpos (l : ℝ) (hl : l ≤ 0) : massIntegral l = 0 := by
  rw [mass_eq]
  apply intervalIntegral.integral_undef
  intro hint
  have h2 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    have : IntervalIntegrable (fun y => 2 * g l y) volume 0 1 := hint.const_mul 2
    refine this.mono_fun (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 := hy.1
    show ‖y⁻¹‖ ≤ ‖2 * g l y‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hy0.le),
      Real.norm_of_nonneg (mul_nonneg zero_le_two (g_nonneg l hy0.le))]
    unfold g
    have he : Real.exp (l / y) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hl hy0.le)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [inv_mul_eq_div, div_le_iff₀ hy0]
    nlinarith [Real.exp_pos (l / y)]
  rw [intervalIntegrable_inv_iff] at h2
  rcases h2 with h | h
  · norm_num at h
  · exact h (by simp)

theorem small (l : ℝ) (hl : 0 < l) (hl1 : l < 1) :
    (- Real.log l) / (1 + Real.exp 1) ≤ massIntegral l := by
  rw [mass_eq, ← intervalIntegral.integral_add_adjacent_intervals
    (g_int' l hl le_rfl hl1.le hl.le) (g_int' l hl hl.le le_rfl hl1.le)]
  have h0 : 0 ≤ ∫ y in (0:ℝ)..l, g l y :=
    intervalIntegral.integral_nonneg hl.le (fun y hy => g_nonneg l hy.1)
  have hc : (0:ℝ) < 1 + Real.exp 1 := by positivity
  have hinv : IntervalIntegrable (fun y : ℝ => (1 + Real.exp 1)⁻¹ * y⁻¹) volume l 1 := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_inv_iff]
    right
    rw [Set.uIcc_of_le hl1.le]
    intro h; exact absurd h.1 (not_le.mpr hl)
  have hmono : ∫ y in l..1, (1 + Real.exp 1)⁻¹ * y⁻¹ ≤ ∫ y in l..1, g l y := by
    apply intervalIntegral.integral_mono_on hl1.le hinv (g_int' l hl hl.le le_rfl hl1.le)
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hl hy.1
    unfold g
    have : l / y ≤ 1 := (div_le_one hy0).mpr hy.1
    have he : Real.exp (l / y) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
    rw [← mul_inv, one_div]
    apply inv_anti₀ (by positivity)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hy0.le
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hl one_pos, one_div,
    Real.log_inv] at hmono
  rw [div_eq_inv_mul]
  linarith

theorem big (l : ℝ) (hl : 0 < l) : massIntegral l ≤ 1 / l := by
  rw [mass_eq]
  calc ∫ y in (0:ℝ)..1, g l y ≤ ∫ y in (0:ℝ)..1, 1 / l :=
        intervalIntegral.integral_mono_on zero_le_one (g_int l hl) intervalIntegrable_const
          (fun y hy => g_le l hl hy.1)
    _ = 1 / l := by simp

end E297P2

open E297P2 in
theorem E297P2.exists_unique_mass (x : ℚ) (hx : 0 < x) : ∃! l : ℝ, massIntegral l = x := by
  have hxR : (0:ℝ) < x := by exact_mod_cast hx
  set ls := Real.exp (-((x:ℝ) + 1) * (1 + Real.exp 1)) with hls
  have hc : (0:ℝ) < 1 + Real.exp 1 := by positivity
  have ls0 : 0 < ls := Real.exp_pos _
  have ls1 : ls < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hFs : (x:ℝ) + 1 ≤ massIntegral ls := by
    have := small ls ls0 ls1
    have hlog : -Real.log ls = ((x:ℝ) + 1) * (1 + Real.exp 1) := by rw [hls, Real.log_exp]; ring
    rw [hlog, mul_div_assoc, div_self hc.ne', mul_one] at this
    exact this
  set lb := 2 / (x:ℝ) with hlb
  have lb0 : 0 < lb := by positivity
  have hFb : massIntegral lb ≤ (x:ℝ) / 2 := by
    have := big lb lb0
    rw [hlb, one_div_div] at this
    exact this
  have hlt : ls < lb := by
    by_contra h
    replace h := not_lt.mp h
    rcases h.eq_or_lt with h | h
    · rw [h] at hFb; linarith
    · have := strict_anti lb0 ls0 h
      linarith
  have hivt := intermediate_value_Icc' hlt.le (cont.mono (fun y hy => lt_of_lt_of_le ls0 hy.1))
  obtain ⟨l, hl, hFl⟩ := hivt
    (show (x:ℝ) ∈ Set.Icc (massIntegral lb) (massIntegral ls) from ⟨by linarith, by linarith⟩)
  have hl0 : 0 < l := lt_of_lt_of_le ls0 hl.1
  refine ⟨l, hFl, fun l' hl' => ?_⟩
  have hl'' : massIntegral l' = x := hl'
  have hl'0 : 0 < l' := by
    by_contra h
    replace h := not_lt.mp h
    rw [nonpos l' h] at hl''
    linarith
  exact strict_anti.injOn hl'0 hl0 (hl''.trans hFl.symm)


open E297P2 in
theorem OMA.solution : OMA.R_Erdos297_erdos_297_R1.H1 := by
  unfold OMA.R_Erdos297_erdos_297_R1.H1
  obtain ⟨l, hl, huniq⟩ := exists_unique_mass 1 one_pos
  have hl1 : massIntegral l = 1 := by simpa using hl
  have hl0 : 0 < l := by
    by_contra h
    rw [nonpos l (not_lt.mp h)] at hl1
    norm_num at hl1
  exact ⟨l, hl0, hl1, fun t ht => huniq t (by simpa using ht)⟩
