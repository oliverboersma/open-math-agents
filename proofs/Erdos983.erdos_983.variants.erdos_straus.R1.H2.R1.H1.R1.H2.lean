import OMAReductions.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1_H1_R1

/-!
The derivative of x times a negative power of log x bounds the weighted tail. The compact initial interval contributes a constant.
-/
open Real Filter Set Asymptotics MeasureTheory
open scoped Topology
noncomputable section

private def primitive983 (A x : ℝ) := x * (log x)^(-A)
private def slope983 (A x : ℝ) := (log x)^(-A) * (1 - A/log x)

private theorem derivative983 (A : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primitive983 A) (slope983 A x) x := by
  have hp := log_pos hx
  have hn : x ≠ 0 := by linarith
  have hl := (Real.hasDerivAt_log hn).rpow_const (p := -A) (Or.inl hp.ne')
  apply ((hasDerivAt_id x).mul hl).congr_deriv
  unfold slope983
  rw [Real.rpow_sub_one hp.ne']
  dsimp
  field_simp
  ring

private theorem smallConst983 (A k : ℝ) :
    (fun _ : ℝ => k) =o[atTop] fun x : ℝ => x / (log x)^A := by
  have h := isLittleO_log_rpow_rpow_atTop A (show (0:ℝ)<1 by norm_num)
  simp only [Real.rpow_one] at h
  apply (isLittleO_iff_tendsto' ?_).2
  · have h' := h.tendsto_div_nhds_zero
    have := tendsto_const_nhds (x := k) |>.mul h'
    simpa only [mul_zero] using this.congr (fun x => by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm])
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact fun hz => False.elim ((div_ne_zero (by linarith) (Real.rpow_pos_of_pos (log_pos hx) A).ne') hz)

private theorem abel983 (f : ℝ → ℝ)
    (hint : ∀ x ≥ (3:ℝ), IntervalIntegrable (fun t => f t / (t*(log t)^2)) volume 3 x)
    (hdec : ∀ B : ℝ, 0<B → f =o[atTop] fun x : ℝ => x/(log x)^B)
    (C A : ℝ) (hA : 0<A) :
    (fun x : ℝ => C + ∫ t in (3:ℝ)..x, f t/(t*(log t)^2))
      =o[atTop] fun x : ℝ => x/(log x)^A := by
  apply IsLittleO.of_bound
  intro c hc
  have hb := (hdec A hA).bound (show 0 < c/4 by positivity)
  have he : ∀ᶠ t : ℝ in atTop, 3 ≤ t ∧ 1 ≤ log t ∧ 2*A ≤ log t ∧
      ‖f t‖ ≤ c/4 * ‖t / (log t)^A‖ := by
    filter_upwards [eventually_ge_atTop (3:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_ge_atTop (2*A), hb] with t h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 he
  let g := fun t : ℝ => f t / (t*(log t)^2)
  let K := C + ∫ t in (3:ℝ)..T, g t
  have hs := (smallConst983 A K).bound (show 0 < c/2 by positivity)
  filter_upwards [eventually_ge_atTop T, hs] with x hx hK
  have h3 := (hT T le_rfl).1
  have hint' : IntervalIntegrable g volume T x := (hint T h3).symm.trans (hint x (h3.trans hx))
  have hd : ContinuousOn (slope983 A) (uIcc T x) := by
    rw [uIcc_of_le hx]
    intro t ht
    have hlog := (hT t ht.1).2.1
    have ht0 : t ≠ 0 := by linarith [(hT t ht.1).1]
    have hl0 : log t ≠ 0 := by linarith
    unfold slope983
    fun_prop (disch := first | positivity | assumption | left; assumption)
  have hi := hd.intervalIntegrable (μ := volume)
  have hmono : (∫ t in T..x, ‖g t‖) ≤ ∫ t in T..x, (c/2)*slope983 A t := by
    apply intervalIntegral.integral_mono_on hx hint'.norm (hi.const_mul (c/2))
    intro t ht
    obtain ⟨ht3,hl,ha,hf⟩ := hT t ht.1
    have ht0 : 0<t := by linarith
    have hl0 : 0<log t := by linarith
    have hl2 : 1 ≤ (log t)^2 := by nlinarith [sq_nonneg (log t-1)]
    have hr := Real.rpow_pos_of_pos hl0 A
    have haa : A/log t ≤ 1/2 := (div_le_iff₀ hl0).2 (by linarith)
    simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht0.le hr.le)] at hf
    simp only [g,Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos ht0 (sq_pos_of_pos hl0)),
      slope983,Real.rpow_neg hl0.le]
    apply (div_le_iff₀ (mul_pos ht0 (sq_pos_of_pos hl0))).2
    calc
      |f t| ≤ c/4 * (t/(log t)^A) := hf
      _ = (c/4 * ((log t)^A)⁻¹)*t := by ring
      _ ≤ ((c/2) * (((log t)^A)⁻¹ * (1-A/log t)))*t := by
        apply mul_le_mul_of_nonneg_right _ ht0.le
        nlinarith [mul_nonneg (mul_nonneg hc.le (inv_nonneg.mpr hr.le)) (sub_nonneg.mpr haa)]
      _ ≤ _ := by
        have hpos : 0 ≤ 1 - A/log t := by linarith
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right ht0.le hl2) (by positivity)
  have hFTC : ∫ t in T..x, slope983 A t = primitive983 A x - primitive983 A T := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact derivative983 A (by linarith [(hT t ht.1).1])
  rw [intervalIntegral.integral_const_mul, hFTC] at hmono
  have tail := (intervalIntegral.norm_integral_le_integral_norm (f := g) hx).trans hmono
  have hTx : 0 < x := by linarith
  have hp : 0 ≤ primitive983 A T := by
    unfold primitive983
    have := (hT T le_rfl).2.1
    positivity
  have hprim : primitive983 A x = ‖x/(log x)^A‖ := by
    have hl := (hT x hx).2.1
    have hpos : 0 < log x := by linarith
    simp [primitive983, Real.rpow_neg hpos.le, Real.norm_eq_abs,
      abs_of_pos hTx, abs_of_pos (Real.rpow_pos_of_pos hpos A), div_eq_mul_inv]
  change ‖C + ∫ t in (3:ℝ)..x, g t‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint T h3) hint', ← add_assoc]
  calc
    _ ≤ ‖K‖ + ‖∫ t in T..x, g t‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [hprim] at tail
      nlinarith [mul_nonneg hc.le hp]


theorem OMA.solution : OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1_H1_R1.H2 := abel983
