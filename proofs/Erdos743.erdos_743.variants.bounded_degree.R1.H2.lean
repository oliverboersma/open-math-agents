import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1

-- Step Erdos743.erdos_743.variants.bounded_degree.R1.H2
-- Credit: @caa1982

open Filter

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2 := by
  intro c hc d
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h0nat : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    h0.comp tendsto_natCast_atTop_atTop
  have hev := (h0nat.eventually (gt_mem_nhds (show (0 : ℝ) < c / ((d : ℝ) + 1) by positivity))).and
    (eventually_ge_atTop 2)
  filter_upwards [hev] with n ⟨hlog, hn2⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [le_div_iff₀ hlog_pos]
  have h1 : Real.log (n : ℝ) < c / ((d : ℝ) + 1) * (n : ℝ) := (div_lt_iff₀ hn_pos).mp hlog
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h2 : ((d : ℝ) + 1) * Real.log (n : ℝ) < c * (n : ℝ) := by
    have := mul_lt_mul_of_pos_left h1 hd1
    have heq : ((d : ℝ) + 1) * (c / ((d : ℝ) + 1) * (n : ℝ)) = c * (n : ℝ) := by
      field_simp [hd1.ne']
    linarith
  nlinarith
