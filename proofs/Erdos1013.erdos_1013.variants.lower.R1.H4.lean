import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1

/-! Take δ = ε / 2. If ε ≥ 1/2 the left side is nonpositive. Otherwise n ≥ 2 (for n ≤ 1
the bound on k is 0), and squaring gives k^2 log n ≤ (2 + δ)^2 n. Then
n ≥ k^2 log 2 / (2 + δ)^2, hence log n ≥ 2 log k - c₀ ≥ (2 - 2ε) log k for large k, and
(1/2 - ε) (2 + δ)^2 ≤ 2 - 2ε finishes the estimate. -/

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H4 := by
  intro ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = 2 * Real.log (2 + ε / 2) - Real.log (Real.log 2) :=
    ⟨_, rfl⟩
  have tlog : Filter.Tendsto (fun k : ℕ => Real.log (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tlog.eventually_ge_atTop (max 0 (c0 / (2 * ε))),
    Filter.eventually_ge_atTop 1] with k h1 hk1 n hkn
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (k:ℝ) := ⟨_, rfl⟩
  rw [← hL] at h1 ⊢
  have hL0 : 0 ≤ L := le_trans (le_max_left _ _) h1
  have hLc : c0 / (2 * ε) ≤ L := le_trans (le_max_right _ _) h1
  have hc0L : c0 ≤ 2 * ε * L := by
    rw [div_le_iff₀ (by positivity)] at hLc
    linarith
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hk2 : (0:ℝ) ≤ (k:ℝ) ^ 2 := by positivity
  by_cases hεhalf : 1 / 2 ≤ ε
  · have h0 : (1 / 2 - ε) * (k:ℝ) ^ 2 * L ≤ 0 := by
      have e1 : (1 / 2 - ε) * ((k:ℝ) ^ 2 * L) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hk2 hL0)
      linarith
    exact h0.trans (Nat.cast_nonneg n)
  · have hεlt : ε < 1 / 2 := not_le.1 hεhalf
    by_cases hn : n ≤ 1
    · exfalso
      have hlog : Real.log (n:ℝ) ≤ 0 := by
        apply Real.log_nonpos (Nat.cast_nonneg n)
        exact_mod_cast hn
      rw [Real.sqrt_eq_zero_of_nonpos hlog, div_zero] at hkn
      linarith
    · have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      obtain ⟨ln, hln⟩ : ∃ ln, ln = Real.log (n:ℝ) := ⟨_, rfl⟩
      rw [← hln] at hkn
      have hlnpos : 0 < ln := by
        rw [hln]
        exact Real.log_pos (by linarith)
      have hln2 : Real.log 2 ≤ ln := by
        rw [hln]
        exact Real.log_le_log (by norm_num) hn2
      have hs : 0 < Real.sqrt ln := Real.sqrt_pos.2 hlnpos
      rw [le_div_iff₀ hs] at hkn
      have hsq : (k:ℝ) ^ 2 * ln ≤ (2 + ε / 2) ^ 2 * n := by
        have e := pow_le_pow_left₀ (by positivity) hkn 2
        rwa [mul_pow, mul_pow, Real.sq_sqrt hlnpos.le, Real.sq_sqrt (Nat.cast_nonneg n)] at e
      have hApos : (0:ℝ) < (2 + ε / 2) ^ 2 := by positivity
      have hnlow : (k:ℝ) ^ 2 * Real.log 2 / (2 + ε / 2) ^ 2 ≤ n := by
        rw [div_le_iff₀ hApos]
        have e1 : (k:ℝ) ^ 2 * Real.log 2 ≤ (k:ℝ) ^ 2 * ln :=
          mul_le_mul_of_nonneg_left hln2 hk2
        linarith
      have hkpos : (0:ℝ) < k := by linarith
      have hlow_pos : (0:ℝ) < (k:ℝ) ^ 2 * Real.log 2 / (2 + ε / 2) ^ 2 := by positivity
      have hlogn : 2 * L - c0 ≤ ln := by
        have e := Real.log_le_log hlow_pos hnlow
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (by positivity) hl2.ne', Real.log_pow, Real.log_pow, ← hL, ← hln] at e
        push_cast at e
        rw [hc0]
        linarith
      have hln' : (2 - 2 * ε) * L ≤ ln := by linarith
      have e2 : (k:ℝ) ^ 2 * ((2 - 2 * ε) * L) ≤ (k:ℝ) ^ 2 * ln :=
        mul_le_mul_of_nonneg_left hln' hk2
      have hpoly : (1 / 2 - ε) * (2 + ε / 2) ^ 2 ≤ 2 - 2 * ε := by
        nlinarith [sq_nonneg ε, pow_pos hε 3]
      have hk2L : 0 ≤ (k:ℝ) ^ 2 * L := mul_nonneg hk2 hL0
      have e3 := mul_le_mul_of_nonneg_right hpoly hk2L
      have e4 : (2 + ε / 2) ^ 2 * ((1 / 2 - ε) * (k:ℝ) ^ 2 * L) ≤ (2 + ε / 2) ^ 2 * n := by
        nlinarith
      exact le_of_mul_le_mul_left e4 hApos
