import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1

/-! Analytic inversion of the `R(3, k)` independence threshold with integer rounding. -/

theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_conjecture_R1_H1_R1.H2 := by
  intro η hη0 hηhalf
  refine ⟨η / 4, by linarith, ?_⟩
  intro n0
  let k0 : ℕ := max 3 (max ⌈(n0 : ℝ) / (1 / 2 - η)⌉₊ ⌈2 / η⌉₊)
  refine ⟨k0, ?_⟩
  intro k hk
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast le_trans (le_max_left 3 _) hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have hexp : Real.exp 1 ≤ (k : ℝ) := by
      have h := Real.exp_one_lt_d9
      linarith
    have hlog := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at hlog
  have hlog_pos : 0 < Real.log (k : ℝ) := by linarith
  have hlog_le : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hk_pos
    linarith
  have hk_le_div : (k : ℝ) ≤ (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
    rw [le_div_iff₀ hlog_pos]
    nlinarith
  have hhalf_pos : (0 : ℝ) < 1 / 2 - η := by linarith
  set x : ℝ := ((1 : ℝ) / 2 - η) * ((k : ℝ) ^ 2 / Real.log (k : ℝ))
  have hx_pos : 0 < x := by positivity
  let N : ℕ := ⌈x⌉₊
  have hN_ge : x ≤ (N : ℝ) := Nat.le_ceil x
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hx_pos hN_ge
  have hn0_le : n0 ≤ N := by
    have h1 : (n0 : ℝ) / (1 / 2 - η) ≤ (k : ℝ) := by
      have hceil : (n0 : ℝ) / (1 / 2 - η) ≤ (⌈(n0 : ℝ) / (1 / 2 - η)⌉₊ : ℝ) := Nat.le_ceil _
      have hk' : (⌈(n0 : ℝ) / (1 / 2 - η)⌉₊ : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right 3 _)) hk
      exact hceil.trans hk'
    have h2 : (n0 : ℝ) ≤ (1 / 2 - η) * (k : ℝ) := by
      have := (div_le_iff₀ hhalf_pos).mp h1
      linarith
    have h3 : (1 / 2 - η) * (k : ℝ) ≤ x :=
      mul_le_mul_of_nonneg_left hk_le_div hhalf_pos.le
    exact_mod_cast h2.trans (h3.trans hN_ge)
  refine ⟨N, hn0_le, hN_ge, ?_⟩
  have hN_lt : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_pos.le
  have h1_le : (1 : ℝ) ≤ (η / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
    have h1 : 2 / η ≤ (k : ℝ) := by
      have hceil : 2 / η ≤ (⌈2 / η⌉₊ : ℝ) := Nat.le_ceil _
      have hk' : (⌈2 / η⌉₊ : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right 3 _)) hk
      exact hceil.trans hk'
    have h2 : 2 ≤ η * (k : ℝ) := by
      have := (div_le_iff₀ hη0).mp h1
      linarith
    have h3 : (η / 2) * (k : ℝ) ≤ (η / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hk_le_div (by linarith)
    linarith
  have hN_upper : (N : ℝ) ≤ ((1 - η) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
    have hsum : x + (η / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) =
        ((1 - η) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
      dsimp only [x]
      ring
    linarith
  have hdiv_le_sq : (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (k : ℝ) ^ 2 :=
    div_le_self (by positivity) hlog_ge1
  have hN_le_sq : (N : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hcoeff : (1 - η) / 2 ≤ 1 := by linarith
    have hpos_div : 0 ≤ (k : ℝ) ^ 2 / Real.log (k : ℝ) := by positivity
    nlinarith
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    have h1 := Real.log_le_log hN_pos hN_le_sq
    rw [Real.log_pow] at h1
    simpa using h1
  by_cases hln : 0 ≤ Real.log (N : ℝ)
  · have hprod : (N : ℝ) * Real.log (N : ℝ) ≤ (1 - η) * (k : ℝ) ^ 2 := by
      calc (N : ℝ) * Real.log (N : ℝ)
          ≤ (((1 - η) / 2) * ((k : ℝ) ^ 2 / Real.log (k : ℝ))) * (2 * Real.log (k : ℝ)) :=
            mul_le_mul hN_upper hlogN_le hln (mul_nonneg (by linarith) (by positivity))
        _ = (1 - η) * (k : ℝ) ^ 2 := by
            field_simp [hlog_pos.ne']
    have hcoeff_lt : (1 + η / 4) ^ 2 * (1 - η) < 1 := by
      have hη3 : 0 < η ^ 3 := pow_pos hη0 3
      have hη2 : 0 < η ^ 2 := pow_pos hη0 2
      nlinarith
    have hsq_lt : ((1 + η / 4) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ))) ^ 2 < (k : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hN_pos.le hln)]
      have h1 : (1 + η / 4) ^ 2 * ((N : ℝ) * Real.log (N : ℝ)) ≤
          (1 + η / 4) ^ 2 * ((1 - η) * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      have h2 : (1 + η / 4) ^ 2 * ((1 - η) * (k : ℝ) ^ 2) < (k : ℝ) ^ 2 := by
        have hk2 : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
        nlinarith
      exact h1.trans_lt h2
    have hlhs_nonneg : 0 ≤ (1 + η / 4) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by positivity
    nlinarith
  · have hneg : (N : ℝ) * Real.log (N : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hN_pos.le (le_of_not_ge hln)
    rw [Real.sqrt_eq_zero_of_nonpos hneg, mul_zero]
    exact hk_pos
