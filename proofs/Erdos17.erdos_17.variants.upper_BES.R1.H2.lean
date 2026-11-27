import OMAReductions.R_Erdos17_erdos_17_variants_upper_BES_R1

/-! With y = log log x one has (log x)^A = exp (y A), so the claim is
exp (-c y^2) ≤ exp (-(y A)) for large x, which holds once y ≥ max 1 (A / c). -/

theorem OMA.solution : OMA.R_Erdos17_erdos_17_variants_upper_BES_R1.H2 := by
  intro A hA c hc
  have t1 : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have t2 : Filter.Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp t1
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [t1.eventually_ge_atTop 1, t2.eventually_ge_atTop (max 1 (A / c))]
    with x h1 h2
  have hL : 0 < Real.log (x : ℝ) := by linarith
  have hy1 : 1 ≤ Real.log (Real.log (x : ℝ)) := le_trans (le_max_left _ _) h2
  have hyc : A / c ≤ Real.log (Real.log (x : ℝ)) := le_trans (le_max_right _ _) h2
  have hAc : A ≤ c * Real.log (Real.log (x : ℝ)) := by
    rw [div_le_iff₀ hc] at hyc
    linarith
  have hpow : (Real.log (x : ℝ)) ^ A = Real.exp (Real.log (Real.log (x : ℝ)) * A) :=
    Real.rpow_def_of_pos hL A
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  rw [one_mul, hpow, Real.norm_of_nonneg (mul_nonneg hx0 (Real.exp_pos _).le),
    Real.norm_of_nonneg (div_nonneg hx0 (Real.exp_pos _).le), div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ hx0
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hAc (by linarith : (0 : ℝ) ≤ Real.log (Real.log (x : ℝ)))]
