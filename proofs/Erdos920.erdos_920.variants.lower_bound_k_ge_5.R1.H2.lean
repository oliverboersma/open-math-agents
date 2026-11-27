import OMAReductions.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1
import Mathlib

/-! General inversion of a Ramsey-type polynomial lower bound. The ceiling
and scaling argument is adapted from @hyprspacecoyote's four-clique proof
and applies to every degree at least two and every positive log exponent. -/
open Filter Asymptotics
set_option maxHeartbeats 1500000 in
theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_lower_bound_k_ge_5_R1.H2 := by
  intro d hd a C ap hC R F hev bridge
  have dr : (2:ℝ)≤d := by exact_mod_cast hd
  have dp : (0:ℝ)<d := by linarith
  have ppos : (0:ℝ)<1/d := by positivity
  have qpos : (0:ℝ)<1-1/d := by
    have hh : (1:ℝ)/d < 1 := (div_lt_one dp).mpr (by linarith)
    linarith
  have apos : 0<a/(d:ℝ) := div_pos ap dp
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hev
  set K : ℝ := max 1 (2 / C) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKC : 2 ≤ C * K^d := by
    have hmax : 2/C ≤ K := le_max_right _ _
    have hpow : K≤K^d := by simpa only [pow_one] using (pow_le_pow_right₀ hK1 (show 1≤d by omega))
    exact ((div_le_iff₀ hC).mp hmax).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hpow hC.le)
  have hKpos : 0 < K := by linarith
  apply IsBigO.of_bound (2 * K)
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlo := (isLittleO_log_rpow_rpow_atTop (a / (d:ℝ)) qpos).bound
    (by positivity : (0 : ℝ) < 1 / (4 * K))
  have hlo' := hcast.eventually hlo
  have ht := hcast.eventually ((tendsto_rpow_atTop ppos).eventually_ge_atTop
    ((M0 : ℝ) + 2))
  filter_upwards [hlo', ht, eventually_ge_atTop 3] with n hlog htM hn3
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  set L := Real.log n with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set t := (n : ℝ) ^ (1/(d:ℝ)) with ht'
  set u := (n : ℝ) ^ (1-1/(d:ℝ)) with hu
  set ℓ := L ^ (a / (d:ℝ)) with hℓ
  have htu : t * u = n := by
    rw [ht', hu, ← Real.rpow_add hnpos, show 1/(d:ℝ)+(1-1/d)=1 by ring,Real.rpow_one]
  have ht3 : t^d=(n:ℝ) := by
    rw [ht',←Real.rpow_natCast,←Real.rpow_mul hnpos.le,one_div_mul_cancel dp.ne',Real.rpow_one]
  have hℓ3 : ℓ^d=L^a := by
    rw [hℓ,←Real.rpow_natCast,←Real.rpow_mul (by linarith),div_mul_cancel₀ _ dp.ne']
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  have hupos : 0 < u := Real.rpow_pos_of_pos hnpos _
  have hℓ1 : 1 ≤ ℓ := Real.one_le_rpow hL1 apos.le
  have hℓu : ℓ ≤ u / (4 * K) := by
    have := hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at this
    linarith [show 1 / (4 * K) * u = u / (4 * K) by ring]
  set x := K * t * ℓ with hx
  have hx1 : 1 ≤ x := by
    have : 1 ≤ t := by
      rw [ht']; exact Real.one_le_rpow (by linarith) ppos.le
    have : 1 ≤ K * t := by nlinarith
    nlinarith
  have hxn : x + 1 ≤ n := by
    have : x ≤ n / 4 := by
      calc x = K * t * ℓ := rfl
        _ ≤ K * t * (u / (4 * K)) := by gcongr
        _ = t * u / 4 := by field_simp
        _ = n / 4 := by rw [htu]
    linarith
  set m := ⌈x⌉₊ with hm
  have hmx : x ≤ m := Nat.le_ceil x
  have hmx1 : (m : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hm2 : (2 : ℝ) ≤ m := by
    have : (M0 : ℝ) + 2 ≤ t := htM
    have : t ≤ x := by
      rw [hx]; nlinarith [mul_le_mul hK1 hℓ1 zero_le_one (by linarith)]
    have : (0 : ℝ) ≤ M0 := Nat.cast_nonneg _
    linarith
  have hmM0 : M0 ≤ m := by
    have h0 : (M0 : ℝ) + 2 ≤ t := htM
    have : t ≤ x := by
      rw [hx]; nlinarith [mul_le_mul hK1 hℓ1 zero_le_one (by linarith)]
    have : (M0 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hR := hM0 m hmM0
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hlogm : Real.log m ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hbig : (n : ℝ) < C * (m : ℝ) ^ d / (Real.log m) ^ a := by
    rw [lt_div_iff₀ (by positivity)]
    have hm3 : x ^ d ≤ (m : ℝ) ^ d := by gcongr
    have hx3 : x ^ d = K ^ d * n * L ^ a := by
      rw [hx, mul_pow, mul_pow, ht3, hℓ3]
    have hl4 : (Real.log m) ^ a ≤ L ^ a := Real.rpow_le_rpow hlogm_pos.le hlogm ap.le
    have hL4 : 0 < L ^ a := by positivity
    calc (n : ℝ) * (Real.log m) ^ a ≤ n * L ^ a := by gcongr
      _ < 2 * n * L ^ a := by nlinarith
      _ ≤ C * K ^ d * n * L ^ a := by gcongr
      _ = C * x ^ d := by rw [hx3]; ring
      _ ≤ C * (m : ℝ) ^ d := by gcongr
  have hNR : n < R m := by
    have : (n : ℝ) < R m := lt_of_lt_of_le hbig hR
    exact_mod_cast this
  have hf := bridge n m (by omega) hNR
  have hmpos : (0 : ℝ) < m := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Nat.cast_nonneg _)]
  change u / ℓ ≤ 2 * K * (F n : ℝ)
  have hstep : u / ℓ ≤ 2 * K * ((n : ℝ) / m) := by
    rw [div_le_iff₀ (by linarith)]
    have : (n : ℝ) / m ≥ n / (2 * x) := by
      apply div_le_div_of_nonneg_left (by positivity) hmpos
      linarith
    have hnx : (n : ℝ) / (2 * x) * ℓ = u / (2 * K) := by
      rw [hx, ← htu]; field_simp
    have : 2 * K * ((n : ℝ) / m) * ℓ ≥ 2 * K * (n / (2 * x)) * ℓ := by gcongr
    have : 2 * K * (n / (2 * x)) * ℓ = u := by
      rw [mul_assoc, hnx]; field_simp
    linarith
  calc u / ℓ ≤ 2 * K * ((n : ℝ) / m) := hstep
    _ ≤ 2 * K * (F n : ℝ) := by gcongr
