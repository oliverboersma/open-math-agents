import OMAReductions.R_Erdos375_erdos_375_variants_log_R1
import Mathlib

/-! With M = log log S >= 64, take z = 1 - log 8 / log M, so M^z = M/8 and
M^(4-4z) = 8^4. The first inequality becomes M exp(3M/4) <= exp(7M/8), i.e. M <= exp(M/8),
which follows from exp x >= x^3/6. -/

open Finset Filter Real

namespace OMA.P2b375

theorem sol : OMA.R_Erdos375_erdos_375_variants_log_R1.H3 := by
  unfold OMA.R_Erdos375_erdos_375_variants_log_R1.H3
  refine ⟨8 ^ 4, by norm_num, ?_⟩
  have hT : Tendsto (fun S : ℝ => log (log S)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hT.eventually (eventually_ge_atTop 64), Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop 0)] with S hM hL
  set L := log S with hLdef
  set M := log L with hMdef
  have hM0 : 0 < M := by linarith
  have hl8 : 0 < log (8:ℝ) := Real.log_pos (by norm_num)
  have hlM : log 8 < log M := Real.log_lt_log (by norm_num) (by linarith)
  have hlM0 : 0 < log M := by linarith
  have hLM : L = exp M := (Real.exp_log hL).symm
  refine ⟨1 - log 8 / log M, ?_, ?_, ?_, ?_⟩
  · have : log 8 / log M ≤ 1 := by rw [div_le_one hlM0]; exact hlM.le
    linarith
  · have : 0 ≤ log 8 / log M := div_nonneg hl8.le hlM0.le
    linarith
  · have hMz : M ^ (1 - log 8 / log M) = M / 8 := by
      rw [Real.rpow_def_of_pos hM0]
      have : log M * (1 - log 8 / log M) = log M - log 8 := by field_simp
      rw [this, Real.exp_sub, Real.exp_log hM0, Real.exp_log (by norm_num)]
    rw [hMz, hLM]
    rw [Real.rpow_def_of_pos (Real.exp_pos M), Real.log_exp]
    -- exp (M * (3/4)) ≤ exp M / M * exp (-(M/8))
    have hcube : M ≤ exp (M / 8) := by
      have h := Real.pow_div_factorial_le_exp (M / 8) (by positivity) 3
      norm_num [Nat.factorial] at h
      have hsq : 3072 ≤ M ^ 2 := by nlinarith
      have h3 : M * 3072 ≤ M * M ^ 2 := mul_le_mul_of_nonneg_left hsq hM0.le
      have h4 : M ≤ (M / 8) ^ 3 / 6 := by nlinarith
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hM0, ← Real.exp_add]
    calc exp (M * (3 / 4)) * M ≤ exp (M * (3 / 4)) * exp (M / 8) :=
          mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
      _ = exp (M + -(M / 8)) := by rw [← Real.exp_add]; ring_nf
  · rw [Real.rpow_def_of_pos hM0]
    have : log M * (4 - 4 * (1 - log 8 / log M)) = 4 * log 8 := by field_simp; ring
    rw [this, show (4:ℝ) * log 8 = log (8 ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]

end OMA.P2b375

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_log_R1.H3 := OMA.P2b375.sol
