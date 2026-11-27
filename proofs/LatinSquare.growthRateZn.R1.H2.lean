import OMAReductions.R_LatinSquare_growthRateZn_R1

-- Step LatinSquare.growthRateZn.R1.H2
-- Credit: @caa1982

open Real Filter
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_growthRateZn_R1.H2 := by
  have hst : Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) :=
    (hst.log (Real.sqrt_pos.mpr Real.pi_pos).ne').div_atTop tendsto_natCast_atTop_atTop
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => (Real.log 2 / 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hcomb : Tendsto (fun n : ℕ =>
      -1 + Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (Real.log 2 / 2) / (n : ℝ) + (3 / 2 : ℝ) * (Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 (-1)) := by
    simpa using (((tendsto_const_nhds (x := (-1 : ℝ))).add hlogst).add hconst).add
      (hlogn.const_mul (3 / 2 : ℝ))
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hst_pos : 0 < Stirling.stirlingSeq n := by
    rw [Stirling.stirlingSeq]
    positivity
  have hfac_eq : (n.factorial : ℝ) =
      Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    rw [Stirling.stirlingSeq]
    have hden : Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
    field_simp [hden]
  have hlog_fac : Real.log (n.factorial : ℝ) =
      Real.log (Stirling.stirlingSeq n) + (Real.log 2 + Real.log (n : ℝ)) / 2 +
        (n : ℝ) * (Real.log (n : ℝ) - 1) := by
    rw [hfac_eq, Real.log_mul hst_pos.ne' (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hn_pos.ne',
      Real.log_pow, Real.log_div hn_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  rw [hlog_fac]
  field_simp [hn_pos.ne']
  ring
