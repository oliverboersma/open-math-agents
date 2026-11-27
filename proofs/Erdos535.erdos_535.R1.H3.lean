import OMAReductions.R_Erdos535_erdos_535_R1

/-!
Proof of `Erdos535.erdos_535.R1.H3`: elementary cutoff choice for Erdős Problem 535.

For `C ≥ 1`, take `c = 4 * Real.log C + 64 > 0`. For `N ≥ ⌈exp (exp 10)⌉₊`, set
`x = log N ≥ exp 10 ≥ 1024`, `t = log x ≥ 10`, `y = ⌊√x⌋₊`, `L = ⌊2 * x⌋₊ + 1`, and
`K = ⌊x / log y⌋₊`. Then `2 ≤ y`, `N < 2 ^ L`, `N < y ^ (K + 1)`, and taking logarithms shows
`log (((L + 1) ^ y * (K + 1)) * C ^ K) ≤ c * x / t`, so the product is at most
`N ^ (c / log (log N))`.
-/

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H3 := by
  intro C hC
  have hC_pos : (0 : ℝ) < C := by linarith
  have hlogC : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  refine ⟨4 * Real.log C + 64, by linarith, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (Real.exp 10)⌉₊, fun N hN => ?_⟩
  have hN_ge : Real.exp (Real.exp 10) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hN)
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) hN_ge
  set x : ℝ := Real.log (N : ℝ) with hx_def
  set t : ℝ := Real.log x with ht_def
  have hx_ge_exp10 : Real.exp 10 ≤ x := by
    calc Real.exp 10
        = Real.log (Real.exp (Real.exp 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos _) hN_ge
  have hexp1_ge_2 : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hx_ge_1024 : (1024 : ℝ) ≤ x := by
    have hpow : (2 : ℝ) ^ (10 : ℕ) ≤ (Real.exp 1) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hexp1_ge_2 10
    have hexp10 : (Real.exp 1) ^ (10 : ℕ) = Real.exp 10 := by
      rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one]
    linarith [show (2 : ℝ) ^ (10 : ℕ) = 1024 by norm_num]
  have hx_pos : (0 : ℝ) < x := by linarith
  have ht_ge_10 : (10 : ℝ) ≤ t := by
    calc (10 : ℝ)
        = Real.log (Real.exp 10) := (Real.log_exp 10).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 10) hx_ge_exp10
  have ht_pos : (0 : ℝ) < t := by linarith
  have hsqrt_ge_32 : (32 : ℝ) ≤ Real.sqrt x := by
    calc (32 : ℝ)
        = Real.sqrt ((32 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt x := by linarith
  have hsqrt_eq : Real.sqrt x = Real.exp (t / 2) := by
    have hsq : Real.exp (t / 2) ^ 2 = x := by
      have hhalf : t / 2 + t / 2 = t := by ring
      rw [sq, ← Real.exp_add, hhalf, ht_def, Real.exp_log hx_pos]
    rw [← hsq, Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  have ht2_le : t ^ 2 ≤ 16 * Real.sqrt x := by
    have h1 : t / 4 ≤ Real.exp (t / 4) := by
      linarith [Real.add_one_le_exp (t / 4)]
    have h2 : (t / 4) ^ 2 ≤ Real.exp (t / 4) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    have h3 : Real.exp (t / 4) ^ 2 = Real.sqrt x := by
      have hq : t / 4 + t / 4 = t / 2 := by ring
      rw [sq, ← Real.exp_add, hq, ← hsqrt_eq]
    have h4 : (t / 4) ^ 2 = t ^ 2 / 16 := by ring
    linarith
  let y : ℕ := ⌊Real.sqrt x⌋₊
  let L : ℕ := ⌊2 * x⌋₊ + 1
  have hy_ge_32 : 32 ≤ y :=
    (Nat.le_floor_iff' (by norm_num : (32 : ℕ) ≠ 0)).mpr (by simpa using hsqrt_ge_32)
  have hy_ge_2 : 2 ≤ y := by omega
  have hy_pos : (0 : ℝ) < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hy_le : (y : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hy_gt : Real.sqrt x - 1 < (y : ℝ) := by
    linarith [Nat.lt_floor_add_one (Real.sqrt x)]
  have hy_ge_half : Real.sqrt x / 2 ≤ (y : ℝ) := by linarith
  have hlog2_le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogy_ge : t / 4 ≤ Real.log (y : ℝ) := by
    have h1 : Real.log (Real.sqrt x / 2) ≤ Real.log (y : ℝ) :=
      Real.log_le_log (div_pos hsqrt_pos (by norm_num)) hy_ge_half
    rw [Real.log_div (ne_of_gt hsqrt_pos) (by norm_num : (2 : ℝ) ≠ 0),
        hsqrt_eq, Real.log_exp] at h1
    linarith
  have hlogy_pos : (0 : ℝ) < Real.log (y : ℝ) := by linarith
  have hlogy_ge_1 : (1 : ℝ) ≤ Real.log (y : ℝ) := by linarith
  let K : ℕ := ⌊x / Real.log (y : ℝ)⌋₊
  have hL_lt : N < 2 ^ L := by
    have hL_gt : 2 * x < (L : ℝ) := by
      dsimp only [L]
      push_cast
      exact Nat.lt_floor_add_one (2 * x)
    have hx_lt : x < (L : ℝ) * Real.log 2 := by nlinarith
    have hreal : (N : ℝ) < ((2 ^ L : ℕ) : ℝ) := by
      rw [← Real.exp_log hN_pos, Nat.cast_pow, Nat.cast_ofNat]
      have h2L : (2 : ℝ) ^ L = Real.exp ((L : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [h2L]
      exact Real.exp_lt_exp.mpr hx_lt
    exact Nat.cast_lt.mp hreal
  have hK_lt : N < y ^ (K + 1) := by
    have hK_gt : x / Real.log (y : ℝ) < ((K + 1 : ℕ) : ℝ) := by
      dsimp only [K]
      push_cast
      exact Nat.lt_floor_add_one (x / Real.log (y : ℝ))
    have hx_lt : x < ((K + 1 : ℕ) : ℝ) * Real.log (y : ℝ) :=
      (div_lt_iff₀ hlogy_pos).mp hK_gt
    have hreal : (N : ℝ) < ((y ^ (K + 1) : ℕ) : ℝ) := by
      rw [← Real.exp_log hN_pos, Nat.cast_pow]
      have hyK : (y : ℝ) ^ (K + 1) = Real.exp (((K + 1 : ℕ) : ℝ) * Real.log (y : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hy_pos]
      rw [hyK]
      exact Real.exp_lt_exp.mpr hx_lt
    exact Nat.cast_lt.mp hreal
  have hL1_pos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
  have hK1_pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hL1_le : ((L + 1 : ℕ) : ℝ) ≤ x ^ 2 := by
    have hf : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
    have hL1_cast : ((L + 1 : ℕ) : ℝ) = (⌊2 * x⌋₊ : ℝ) + 2 := by
      dsimp only [L]
      push_cast
      ring
    nlinarith
  have hlogL1_le : Real.log ((L + 1 : ℕ) : ℝ) ≤ 2 * t := by
    calc Real.log ((L + 1 : ℕ) : ℝ)
        ≤ Real.log (x ^ 2) := Real.log_le_log hL1_pos hL1_le
      _ = 2 * t := by rw [Real.log_pow, Nat.cast_ofNat, ← ht_def]
  have hlogL1_nonneg : (0 : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ L + 1 by omega))
  have hK_le : (K : ℝ) ≤ 4 * x / t := by
    calc (K : ℝ)
        ≤ x / Real.log (y : ℝ) := Nat.floor_le (div_nonneg hx_pos.le hlogy_pos.le)
      _ ≤ x / (t / 4) := div_le_div_of_nonneg_left hx_pos.le (by positivity) hlogy_ge
      _ = 4 * x / t := by ring
  have hK_le_x : (K : ℝ) ≤ x := by
    calc (K : ℝ)
        ≤ x / Real.log (y : ℝ) := Nat.floor_le (div_nonneg hx_pos.le hlogy_pos.le)
      _ ≤ x / 1 := div_le_div_of_nonneg_left hx_pos.le (by norm_num) hlogy_ge_1
      _ = x := div_one x
  have hK1_le : ((K + 1 : ℕ) : ℝ) ≤ x ^ 2 := by
    have hK1_cast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; rfl
    nlinarith
  have hlogK1_le : Real.log ((K + 1 : ℕ) : ℝ) ≤ 2 * t := by
    calc Real.log ((K + 1 : ℕ) : ℝ)
        ≤ Real.log (x ^ 2) := Real.log_le_log hK1_pos hK1_le
      _ = 2 * t := by rw [Real.log_pow, Nat.cast_ofNat, ← ht_def]
  have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
  have hterm1 : (y : ℝ) * Real.log ((L + 1 : ℕ) : ℝ) ≤ 32 * x / t := by
    have hmul : (y : ℝ) * Real.log ((L + 1 : ℕ) : ℝ) ≤ Real.sqrt x * (2 * t) :=
      mul_le_mul hy_le hlogL1_le hlogL1_nonneg (Real.sqrt_nonneg x)
    have hbound : Real.sqrt x * (2 * t) ≤ 32 * x / t := by
      rw [le_div_iff₀ ht_pos]
      have hstep : 2 * Real.sqrt x * t ^ 2 ≤ 2 * Real.sqrt x * (16 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left ht2_le (by positivity)
      linarith [show Real.sqrt x * (2 * t) * t = 2 * Real.sqrt x * t ^ 2 by ring,
                show 2 * Real.sqrt x * (16 * Real.sqrt x) = 32 * (Real.sqrt x * Real.sqrt x) by ring]
    exact hmul.trans hbound
  have hterm2 : Real.log ((K + 1 : ℕ) : ℝ) ≤ 32 * x / t := by
    have hsqrt_le_x : Real.sqrt x ≤ x := by nlinarith
    have hbound : 2 * t ≤ 32 * x / t := by
      rw [le_div_iff₀ ht_pos]
      linarith [show 2 * t * t = 2 * t ^ 2 by ring, ht2_le, hsqrt_le_x]
    exact hlogK1_le.trans hbound
  have hterm3 : (K : ℝ) * Real.log C ≤ 4 * Real.log C * x / t := by
    have hmul : (K : ℝ) * Real.log C ≤ (4 * x / t) * Real.log C :=
      mul_le_mul_of_nonneg_right hK_le hlogC
    linarith [show (4 * x / t) * Real.log C = 4 * Real.log C * x / t by ring]
  refine ⟨y, L, K, hy_ge_2, hL_lt, hK_lt, ?_⟩
  set lhs : ℝ := (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K with hlhs_def
  have hpowL1_pos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) ^ y := pow_pos hL1_pos y
  have hprod_pos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) ^ y * ((K + 1 : ℕ) : ℝ) :=
    mul_pos hpowL1_pos hK1_pos
  have hCK_pos : (0 : ℝ) < C ^ K := pow_pos hC_pos K
  have hcast : (((L + 1) ^ y * (K + 1) : ℕ) : ℝ) =
      ((L + 1 : ℕ) : ℝ) ^ y * ((K + 1 : ℕ) : ℝ) := by
    push_cast; rfl
  have hlhs_pos : (0 : ℝ) < lhs := by
    rw [hlhs_def, hcast]
    exact mul_pos hprod_pos hCK_pos
  have hlog_lhs : Real.log lhs =
      (y : ℝ) * Real.log ((L + 1 : ℕ) : ℝ) + Real.log ((K + 1 : ℕ) : ℝ) +
        (K : ℝ) * Real.log C := by
    rw [hlhs_def, hcast,
        Real.log_mul (ne_of_gt hprod_pos) (ne_of_gt hCK_pos),
        Real.log_mul (ne_of_gt hpowL1_pos) (ne_of_gt hK1_pos),
        Real.log_pow, Real.log_pow]
  have hlog_le : Real.log lhs ≤ x * ((4 * Real.log C + 64) / t) := by
    rw [hlog_lhs]
    have hsum : 32 * x / t + 32 * x / t + 4 * Real.log C * x / t =
        x * ((4 * Real.log C + 64) / t) := by ring
    linarith
  rw [Real.rpow_def_of_pos hN_pos, ← hx_def, ← Real.exp_log hlhs_pos]
  exact Real.exp_le_exp.mpr hlog_le
