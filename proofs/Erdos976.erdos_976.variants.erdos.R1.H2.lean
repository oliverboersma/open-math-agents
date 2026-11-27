import OMAReductions.R_Erdos976_erdos_976_variants_erdos_R1

/-! Write L = log n and y = log L. Then L^(log y) = exp (y log y) and L^c = exp (y c). For
y ≥ max 1 (6 / c^3) one has y log y ≤ y^2 ≤ (y c)^3 / 6 ≤ exp (y c), which gives the claim
with constant 1. -/

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_erdos_R1.H2 := by
  intro c hc
  have t1 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have t2 : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp t1
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [t1.eventually_ge_atTop 1, t2.eventually_ge_atTop (max 1 (6 / c ^ 3))]
    with n h1 h2
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (n : ℝ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  obtain ⟨y, hy⟩ : ∃ y, y = Real.log L := ⟨_, rfl⟩
  rw [← hy] at h2 ⊢
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) h2
  have hyc : 6 / c ^ 3 ≤ y := le_trans (le_max_right _ _) h2
  have hLpos : 0 < L := by linarith
  have e1 : L ^ Real.log y = Real.exp (y * Real.log y) := by
    rw [Real.rpow_def_of_pos hLpos, ← hy]
  have e2 : L ^ c = Real.exp (y * c) := by
    rw [Real.rpow_def_of_pos hLpos, ← hy]
  have hlogy : Real.log y ≤ y :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hc3 : 0 < c ^ 3 := by positivity
  have h6 : 6 ≤ c ^ 3 * y := by
    rw [div_le_iff₀ hc3] at hyc
    linarith
  have hexp : (y * c) ^ 3 / 6 ≤ Real.exp (y * c) := by
    have h := Real.pow_div_factorial_le_exp (y * c) (by positivity) 3
    have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rwa [h3] at h
  have hsq : y * Real.log y ≤ y ^ 2 := by nlinarith
  have hcube : y ^ 2 ≤ (y * c) ^ 3 / 6 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left h6 (sq_nonneg y)]
  have key : y * Real.log y ≤ Real.exp (y * c) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [one_mul, e1, e2, Real.norm_of_nonneg (mul_nonneg hn0 (Real.exp_pos _).le),
    Real.norm_of_nonneg (mul_nonneg hn0 (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) hn0
