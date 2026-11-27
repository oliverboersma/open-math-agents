import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1

/-! Put a = 1 / (1 - ε), β = a^2 > 1, δ = (β - 1) / (4 β) and τ = (β - 1) / 16, so that
(1/2 - δ) β = 1/2 + 4 τ. For large n put L = log n, s = (n L)^(1/2) and k = ⌊a s⌋.
Then (1 - ε) (n / L)^(1/2) k ≤ (1 - ε) a s (n / L)^(1/2) = n. Also
log k ≤ log a + (L + log L) / 2 ≤ (1/2 + 2 τ) L once log a ≤ τ L and log L ≤ τ L, while
k^2 ≥ (a s - 1)^2 ≥ β n L - 2 a s ≥ (β - 2 τ) n L once a ≤ τ s, so that
(1/2 - δ) k^2 ≥ (1/2 + 3 τ) n L ≥ n log k. -/

set_option maxHeartbeats 1000000 in
open Filter in
theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1.H3 := by
  intro ε hε hε1
  have h1e : 0 < 1 - ε := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (1 - ε) := ⟨_, rfl⟩
  have ha1 : 1 < a := by
    rw [ha, lt_div_iff₀ h1e]
    linarith
  have hapos : 0 < a := by linarith
  have hae : (1 - ε) * a = 1 := by
    rw [ha]
    field_simp
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = a ^ 2 := ⟨_, rfl⟩
  have hβ1 : 1 < β := by
    rw [hβ]
    nlinarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (β - 1) / 16 := ⟨_, rfl⟩
  have hτpos : 0 < τ := by
    rw [hτ]
    linarith
  refine ⟨(β - 1) / (4 * β), by positivity, ?_⟩
  have hδβ : (1 / 2 - (β - 1) / (4 * β)) * β = 1 / 2 + 4 * τ := by
    rw [hτ]
    field_simp
    ring
  have hδlt : (1 / 2 - (β - 1) / (4 * β)) ≤ 1 / 2 := by
    have : 0 ≤ (β - 1) / (4 * β) := by positivity
    linarith
  have hδpos : 0 ≤ (1 / 2 - (β - 1) / (4 * β)) := by
    have e : (β - 1) / (4 * β) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  intro K
  have tlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tlittle := tlog.eventually
    (Real.isLittleO_log_id_atTop.bound hτpos)
  filter_upwards [tlog.eventually_ge_atTop (max 1 (Real.log a / τ)), tlittle,
    eventually_ge_atTop (⌈(a / τ) ^ 2⌉₊ + (K + 1) ^ 2)] with n h1 h2 h3
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (n : ℝ) := ⟨_, rfl⟩
  rw [← hL] at h1 h2 ⊢
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) h1
  have hLa : Real.log a / τ ≤ L := le_trans (le_max_right _ _) h1
  have hLpos : 0 < L := by linarith
  have hloga : Real.log a ≤ τ * L := by
    rw [div_le_iff₀ hτpos] at hLa
    linarith
  have hlogL : Real.log L ≤ τ * L := by
    have h := h2
    simp only [id, Real.norm_eq_abs] at h
    rw [abs_of_pos hLpos] at h
    exact (le_abs_self _).trans h
  have hn1 : ((⌈(a / τ) ^ 2⌉₊ + (K + 1) ^ 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
  push_cast at hn1
  have hceil := Nat.le_ceil ((a / τ) ^ 2)
  have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := sq_nonneg _
  have hc0 : (0 : ℝ) ≤ (⌈(a / τ) ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
    linarith
  -- X = n L and s = sqrt X
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (n : ℝ) * L := ⟨_, rfl⟩
  have hXn : (n : ℝ) ≤ X := by
    rw [hX]
    nlinarith
  have hXpos : 0 < X := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt X := ⟨_, rfl⟩
  have hss : s ^ 2 = X := by
    rw [hs, Real.sq_sqrt hXpos.le]
  have hspos : 0 < s := by
    rw [hs]
    exact Real.sqrt_pos.2 hXpos
  have hsK : (K : ℝ) + 1 ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    linarith
  have hsa : a / τ ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    linarith
  have has : a ≤ τ * s := by
    rw [div_le_iff₀ hτpos] at hsa
    linarith
  have hs1 : 1 ≤ s := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hasx : 0 ≤ a * s := by positivity
  refine ⟨⌊a * s⌋₊, ?_, ?_, ?_⟩
  · have hlt : a * s - 1 < (⌊a * s⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hKs : (K : ℝ) < ⌊a * s⌋₊ := by nlinarith
    exact_mod_cast hKs.le
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊a * s⌋₊ := ⟨_, rfl⟩
    rw [← hk]
    have hkle : (k : ℝ) ≤ a * s := by
      rw [hk]
      exact Nat.floor_le hasx
    have hkgt : a * s - 1 < (k : ℝ) := by
      rw [hk]
      exact Nat.sub_one_lt_floor _
    have hkpos : (0 : ℝ) < k := by nlinarith
    -- log k ≤ log a + (L + log L) / 2
    have hlogk : Real.log k ≤ Real.log a + (L + Real.log L) / 2 := by
      have e1 : Real.log k ≤ Real.log (a * s) := Real.log_le_log hkpos hkle
      have e2 : Real.log (a * s) = Real.log a + Real.log s :=
        Real.log_mul hapos.ne' hspos.ne'
      have e3 : Real.log s = Real.log X / 2 := by
        rw [hs, Real.log_sqrt hXpos.le]
      have e4 : Real.log X = L + Real.log L := by
        rw [hX, Real.log_mul hnpos.ne' hLpos.ne', hL]
      rw [e2, e3, e4] at e1
      exact e1
    have hτL : 0 ≤ τ * L := by positivity
    have hlogk' : Real.log k ≤ (1 / 2 + 2 * τ) * L := by nlinarith
    have hleft : (n : ℝ) * Real.log k ≤ (1 / 2 + 2 * τ) * X := by
      rw [hX]
      have := mul_le_mul_of_nonneg_left hlogk' hnpos.le
      linarith
    have h0 : 0 ≤ a * s - 1 := by
      have := one_le_mul_of_one_le_of_one_le ha1.le hs1
      linarith
    have hk2 : (a * s - 1) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ h0 hkgt.le 2
    have e : (a * s) ^ 2 = β * X := by rw [hβ, ← hss]; ring
    have e2 : a * s ≤ τ * X := by
      have h := mul_le_mul_of_nonneg_right has hspos.le
      have h' : τ * s * s = τ * X := by rw [← hss]; ring
      linarith
    have hexp : β * X - 2 * (τ * X) ≤ (a * s - 1) ^ 2 := by
      have : (a * s - 1) ^ 2 = (a * s) ^ 2 - 2 * (a * s) + 1 := by ring
      linarith
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 / 2 - (β - 1) / (4 * β) := ⟨_, rfl⟩
    rw [← hD]
    rw [← hD] at hδβ hδlt hδpos
    have hτX : 0 ≤ τ * X := by positivity
    have f1 : D * (β * X) = (1 / 2 + 4 * τ) * X := by
      have : D * (β * X) = (D * β) * X := by ring
      rw [this, hδβ]
    have f2 : D * (2 * (τ * X)) ≤ 1 / 2 * (2 * (τ * X)) :=
      mul_le_mul_of_nonneg_right hδlt (by positivity)
    have f3 : D * (β * X - 2 * (τ * X)) ≤ D * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (le_trans hexp hk2) hδpos
    have f4 : D * (β * X - 2 * (τ * X)) = D * (β * X) - D * (2 * (τ * X)) := by ring
    linarith
  · have hkle : (⌊a * s⌋₊ : ℝ) ≤ a * s := Nat.floor_le hasx
    have hsq : s = Real.sqrt n * Real.sqrt L := by
      rw [hs, hX, Real.sqrt_mul hnpos.le]
    have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
    have hcoef : 0 ≤ (1 - ε) * Real.sqrt n / Real.sqrt L := by positivity
    calc (1 - ε) * Real.sqrt n / Real.sqrt L * (⌊a * s⌋₊ : ℝ)
        ≤ (1 - ε) * Real.sqrt n / Real.sqrt L * (a * s) :=
          mul_le_mul_of_nonneg_left hkle hcoef
      _ = ((1 - ε) * a) * (Real.sqrt n * Real.sqrt n) * (Real.sqrt L / Real.sqrt L) := by
          rw [hsq]; ring
      _ = n := by
          rw [hae, Real.mul_self_sqrt hnpos.le, div_self hsL.ne']
          ring
