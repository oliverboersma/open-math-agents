import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1_H2_R1
import Mathlib

-- Step Erdos308.erdos_308.variants.croot.R1.H2.R1.H2: hypothesis H2 of reduction
-- Erdos308.erdos_308.variants.croot.R1.H2.R1
-- Credit: @ivillar

/-!
Write `L = log N` and `m = N / p`.

* If `N < p L ^ a` then `m < L ^ a`, and `m m! ≤ m ^ (m + 1)` has logarithm at most
  `(L ^ a + 1) a log L`, while `log p > L - a log L`. Since `(L ^ a + 2) log L = o(L)`
  (because `a < 1`), `m m! < p` for large `N`.
* If `p L ^ b ≤ N` then `m + 1 > L ^ b ≥ 2 L + 3`, so `m! ≥ 2 ^ (m - 1) > e ^ L = N ≥ p`.
-/

namespace OMA.Erdos308CrootR1H2R1H2

open Filter Real

lemma two_pow_le_factorial (m : ℕ) : 2 ^ (m - 1) ≤ m.factorial := by
  induction m with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.factorial_succ, show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      calc 2 ^ (k - 1) * 2 ≤ k.factorial * (k + 1) := Nat.mul_le_mul ih (by omega)
        _ = (k + 1) * k.factorial := by ring

lemma ev_E1 (a : ℝ) (ha : a < 1) : ∀ᶠ L : ℝ in atTop, (L ^ a + 2) * log L ≤ L / 2 := by
  have h1 := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 - a by linarith)).bound
    (show (0:ℝ) < 1 / 4 by norm_num)
  have h2 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 8 by norm_num)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with L h1 h2 hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ log L := log_nonneg hL
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity)] at h1
  rw [Real.norm_of_nonneg hlog, id, Real.norm_of_nonneg hL0.le] at h2
  have hmul : L ^ a * L ^ (1 - a) = L := by rw [← rpow_add hL0]; simp
  have hLa : 0 ≤ L ^ a := by positivity
  have h3 : L ^ a * log L ≤ L / 4 := by
    calc L ^ a * log L ≤ L ^ a * (1 / 4 * L ^ (1 - a)) := mul_le_mul_of_nonneg_left h1 hLa
      _ = 1 / 4 * (L ^ a * L ^ (1 - a)) := by ring
      _ = L / 4 := by rw [hmul]; ring
  nlinarith

lemma ev_E2 (b : ℝ) (hb : 1 < b) : ∀ᶠ L : ℝ in atTop, 2 * L + 3 ≤ L ^ b := by
  have h := (tendsto_rpow_atTop (show (0:ℝ) < b - 1 by linarith)).eventually_ge_atTop 3
  filter_upwards [h, eventually_ge_atTop 3] with L h hL
  have hL0 : 0 < L := by linarith
  have e : L ^ b = L ^ (b - 1) * L := by rw [← rpow_add_one hL0.ne', sub_add_cancel]
  rw [e]; nlinarith

end OMA.Erdos308CrootR1H2R1H2

open Filter Real OMA.Erdos308CrootR1H2R1H2 in
theorem OMA.solution : OMA.R_Erdos308_erdos_308_variants_croot_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos308_erdos_308_variants_croot_R1_H2_R1.H2
  intro a b ha ha1 hb1 hb2
  have hlogN : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogN.eventually (ev_E1 a ha1), hlogN.eventually (ev_E2 b hb1),
    hlogN.eventually (eventually_ge_atTop 3)] with N E1 E2 E3
  intro p hp
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
  set L := log (N:ℝ) with hLdef
  have hN0 : (0:ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [hLdef, h] at E3; simp at E3; linarith
    · exact_mod_cast h
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ log L := log_nonneg (by linarith)
  set m := N / p with hm
  constructor
  · intro hcut
    rcases Nat.eq_zero_or_pos m with h0 | hmpos
    · rw [h0]; simpa using hpp.pos
    · have hmle : (m:ℝ) ≤ (N:ℝ) / p := Nat.cast_div_le
      have hNp : (N:ℝ) / p < L ^ a := by
        rw [div_lt_iff₀ hp0]; linarith [mul_comm (p:ℝ) (L ^ a)]
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hmpos
      have hmLa : (m:ℝ) < L ^ a := lt_of_le_of_lt hmle hNp
      have hfac : m * m.factorial ≤ m ^ (m + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.factorial_le_pow m)
      suffices hlt : ((m ^ (m + 1) : ℕ) : ℝ) < p by
        have : m ^ (m + 1) < p := by exact_mod_cast hlt
        omega
      push_cast
      rw [← Real.log_lt_log_iff (by positivity) hp0, Real.log_pow]
      have hlogm : log (m:ℝ) ≤ a * log L := by
        rw [← Real.log_rpow hL0]; exact Real.log_le_log (by linarith) hmLa.le
      have hlogm0 : 0 ≤ log (m:ℝ) := log_nonneg hm1
      have hlogp : L < log p + a * log L := by
        rw [← Real.log_rpow hL0, ← Real.log_mul hp0.ne' (by positivity)]
        exact Real.log_lt_log hN0 hcut
      have h1 : ((m:ℝ) + 1) * log m ≤ (L ^ a + 1) * (a * log L) := by
        apply mul_le_mul (by linarith) hlogm hlogm0 (by positivity)
      have h0 : 0 ≤ (L ^ a + 2) * log L := by positivity
      have h2 : a * ((L ^ a + 2) * log L) ≤ (L ^ a + 2) * log L := by nlinarith
      push_cast
      nlinarith
  · intro hfac
    by_contra hcon
    push_neg at hcon
    have hdiv : (N:ℝ) < p * ((m:ℝ) + 1) := by
      have := Nat.lt_mul_div_succ N hpp.pos
      exact_mod_cast this
    have hmL : L ^ b < (m:ℝ) + 1 := by
      by_contra h
      push_neg at h
      nlinarith [mul_le_mul_of_nonneg_left h hp0.le]
    have hm2 : 2 * L + 2 < (m:ℝ) := by linarith
    have hm1 : 1 ≤ m := by
      have : (1:ℝ) < m := by linarith
      exact_mod_cast this.le
    have h2pow : (N:ℝ) < ((2 ^ (m - 1) : ℕ) : ℝ) := by
      rw [← Real.log_lt_log_iff hN0 (by positivity)]
      push_cast
      rw [Real.log_pow, Nat.cast_sub hm1]
      have hl2 := Real.log_two_gt_d9
      push_cast
      nlinarith
    have hf := two_pow_le_factorial m
    have h3 : 2 ^ (m - 1) ≤ m * m.factorial := hf.trans (Nat.le_mul_of_pos_left _ hm1)
    have h4 : N < 2 ^ (m - 1) := by exact_mod_cast h2pow
    omega
