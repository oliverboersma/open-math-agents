import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1

/-! Put L = log k, x = (2 + ε) k^2 L and n the integer part of x. For large k one has
log n ≤ log x ≤ (2 + ε/2) L and n ≥ x - 1 ≥ (2 + 3ε/4) k^2 L, so with
ρ = (2 + 3ε/4) / (2 + ε/2) > 1 one gets k^2 ρ log n ≤ n, that is
k ≤ ρ^(-1/2) (n / log n)^(1/2). The statement holds with δ = 1 - ρ^(-1/2). -/

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1.H3 := by
  intro ε hε
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 + 3 * ε / 4) / (2 + ε / 2) := ⟨_, rfl⟩
  have hden : (0:ℝ) < 2 + ε / 2 := by linarith
  have hρ1 : 1 < ρ := by
    rw [hρ, lt_div_iff₀ hden]
    linarith
  have hρpos : 0 < ρ := by linarith
  have hsρ1 : 1 < Real.sqrt ρ := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hρ1
  have hsρpos : 0 < Real.sqrt ρ := by linarith
  refine ⟨1 - 1 / Real.sqrt ρ, ?_, ?_⟩
  · have h2 : 1 / Real.sqrt ρ < 1 := by
      rw [div_lt_one hsρpos]
      exact hsρ1
    linarith
  intro N
  have tlog : Filter.Tendsto (fun k : ℕ => Real.log (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tlittle := tlog.eventually
    (Real.isLittleO_log_id_atTop.bound (by positivity : (0:ℝ) < ε / 4))
  filter_upwards [tlog.eventually_ge_atTop (max 1 (4 * Real.log (2 + ε) / ε)), tlittle,
    Filter.eventually_ge_atTop (N + 1), Filter.eventually_ge_atTop ⌈4 / ε⌉₊] with k h1 h2 h3 h4
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (k:ℝ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) h1
  have hLA : 4 * Real.log (2 + ε) / ε ≤ L := le_trans (le_max_right _ _) h1
  have hLpos : 0 < L := by linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkN : (N:ℝ) + 1 ≤ k := by exact_mod_cast h3
  have hk4 : 4 / ε ≤ (k:ℝ) := Nat.ceil_le.1 h4
  have hkpos : (0:ℝ) < k := by linarith
  -- log L ≤ (ε/4) L
  have hlogL : Real.log L ≤ ε / 4 * L := by
    have h := h2
    simp only [id] at h
    rw [Real.norm_of_nonneg hLpos.le] at h
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  -- log (2+ε) ≤ (ε/4) L
  have hlogA : Real.log (2 + ε) ≤ ε / 4 * L := by
    rw [div_le_iff₀ hε] at hLA
    linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (2 + ε) * (k:ℝ) ^ 2 * L := ⟨_, rfl⟩
  rw [← hx]
  have hk2 : (1:ℝ) ≤ (k:ℝ) ^ 2 := by nlinarith
  have hk2L : (1:ℝ) ≤ (k:ℝ) ^ 2 * L := by nlinarith
  have hxpos : 0 < x := by
    rw [hx]
    positivity
  -- (ε/4) k^2 L ≥ 1
  have hgain : 1 ≤ ε / 4 * ((k:ℝ) ^ 2 * L) := by
    have e1 : 4 / ε ≤ (k:ℝ) ^ 2 * L := by nlinarith
    rw [div_le_iff₀ hε] at e1
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hn]
  have hnle : (n:ℝ) ≤ x := by
    rw [hn]
    exact Nat.floor_le hxpos.le
  have hngt : x - 1 < (n:ℝ) := by
    rw [hn]
    exact Nat.sub_one_lt_floor x
  have hnlow : (2 + 3 * ε / 4) * ((k:ℝ) ^ 2 * L) ≤ n := by
    rw [hx] at hngt
    nlinarith
  have hn2 : (2:ℝ) ≤ n := by nlinarith
  constructor
  · have hNn : (N:ℝ) ≤ n := by nlinarith
    exact_mod_cast hNn
  have hlogx : Real.log x = Real.log (2 + ε) + 2 * L + Real.log L := by
    rw [hx, Real.log_mul (by positivity) hLpos.ne', Real.log_mul (by linarith) (by positivity),
      Real.log_pow, hL]
    push_cast
    ring
  have hlogn : Real.log n ≤ (2 + ε / 2) * L := by
    have e1 := Real.log_le_log (by linarith : (0:ℝ) < n) hnle
    rw [hlogx] at e1
    linarith
  have hlognpos : 0 < Real.log n := Real.log_pos (by linarith)
  have key : (k:ℝ) ^ 2 * ρ * Real.log n ≤ n := by
    have e1 : (k:ℝ) ^ 2 * ρ * Real.log n ≤ (k:ℝ) ^ 2 * ρ * ((2 + ε / 2) * L) :=
      mul_le_mul_of_nonneg_left hlogn (by positivity)
    have e2 : (k:ℝ) ^ 2 * ρ * ((2 + ε / 2) * L) = (2 + 3 * ε / 4) * ((k:ℝ) ^ 2 * L) := by
      rw [hρ]
      field_simp
    linarith
  have hs : (k:ℝ) * Real.sqrt ρ * Real.sqrt (Real.log n) ≤ Real.sqrt n := by
    have e := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hkpos.le] at e
  have hslog : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 hlognpos
  rw [sub_sub_cancel, le_div_iff₀ hslog, div_mul_eq_mul_div, one_mul, le_div_iff₀ hsρpos]
  linarith
