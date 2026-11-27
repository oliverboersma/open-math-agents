import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1
import Mathlib

-- Step RiemannHypothesis.lagarias_criterion.R1.H2.R1.H2: hypothesis H2 of reduction RiemannHypothesis.lagarias_criterion.R1.H2.R1
-- Credit: @ivillar

/-!
# An elementary upper bound for the harmonic expression in Lagarias' criterion

For `n ≥ 20`, with `H = harmonic n`, `L = log n` and `γ` the Euler-Mascheroni constant, Mathlib's
bounds `L + γ < H < log (n + 1) + γ` give `exp H < exp γ * (n + 1)` and
`log H < log L + (1 / n + γ) / L`. Multiplying out, the excess over `exp γ * n * log L` is at most
`H + exp γ * log L + exp γ * (n + 1) * (1 / n + γ) / L`, which is below `24 * n / L` because
`exp γ < 2`, `γ < 2 / 3`, `log L ≤ L - 1` and `L ^ 2 ≤ 4 * n`.
-/

namespace LagariasUpperStep

open Real

theorem lag_upper : ∀ n : ℕ, 20 ≤ n →
    (harmonic n : ℝ) + exp (harmonic n) * log (harmonic n) ≤
    exp eulerMascheroniConstant * n * log (log n) + 24 * n / log n := by
  intro n hn
  have hx20 : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hγ1 : 1 / 2 < eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant
  have hγ2 : eulerMascheroniConstant < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  -- `exp γ < 2`
  have hg2 : exp eulerMascheroniConstant < 2 := by
    have h1 : eulerMascheroniConstant < log 2 := by
      have := Real.log_two_gt_d9
      linarith
    calc exp eulerMascheroniConstant < exp (log 2) := exp_lt_exp.mpr h1
      _ = 2 := exp_log (by norm_num)
  have hg0 : 0 < exp eulerMascheroniConstant := exp_pos _
  -- `1 < log n`
  have hL1 : 1 < log (n : ℝ) := by
    rw [lt_log_iff_exp_lt hx0]
    have := Real.exp_one_lt_three
    linarith
  have hL0 : 0 < log (n : ℝ) := by linarith
  -- bounds on the harmonic number
  have hHlow : log (n : ℝ) + eulerMascheroniConstant < (harmonic n : ℝ) := by
    have h := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    rw [eulerMascheroniSeq', if_neg (by omega)] at h
    linarith
  have hHup : (harmonic n : ℝ) < log ((n : ℝ) + 1) + eulerMascheroniConstant := by
    have h := eulerMascheroniSeq_lt_eulerMascheroniConstant n
    rw [eulerMascheroniSeq] at h
    linarith
  -- `log (n + 1) ≤ log n + 1 / n`
  have hlog1 : log ((n : ℝ) + 1) ≤ log (n : ℝ) + 1 / (n : ℝ) := by
    have h := log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / (n : ℝ) by positivity)
    rw [log_div (by positivity) hx0.ne'] at h
    have h2 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp; ring
    linarith
  have hinv : 1 / (n : ℝ) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) hx20
  -- `δ = 1 / n + γ`
  have hδ0 : 0 < 1 / (n : ℝ) + eulerMascheroniConstant := by positivity
  have hδ : 1 / (n : ℝ) + eulerMascheroniConstant ≤ 0.72 := by
    norm_num at hinv ⊢
    linarith
  have hHU : (harmonic n : ℝ) < log (n : ℝ) + (1 / (n : ℝ) + eulerMascheroniConstant) := by
    linarith
  have hH1 : 1 < (harmonic n : ℝ) := by linarith
  -- `exp H ≤ (n + 1) * exp γ`
  have hexp : exp (harmonic n : ℝ) ≤ ((n : ℝ) + 1) * exp eulerMascheroniConstant := by
    calc exp (harmonic n : ℝ) ≤ exp (log ((n : ℝ) + 1) + eulerMascheroniConstant) :=
          exp_le_exp.mpr hHup.le
      _ = ((n : ℝ) + 1) * exp eulerMascheroniConstant := by
          rw [exp_add, exp_log (by positivity)]
  -- `log H ≤ log (log n) + δ / log n`
  have hlogH : log (harmonic n : ℝ) ≤
      log (log (n : ℝ)) + (1 / (n : ℝ) + eulerMascheroniConstant) / log (n : ℝ) := by
    have h1 : log (harmonic n : ℝ) ≤
        log (log (n : ℝ) + (1 / (n : ℝ) + eulerMascheroniConstant)) :=
      log_le_log (by linarith) hHU.le
    have h2 := log_le_sub_one_of_pos
      (show 0 < (log (n : ℝ) + (1 / (n : ℝ) + eulerMascheroniConstant)) / log (n : ℝ) by
        positivity)
    rw [log_div (by positivity) hL0.ne'] at h2
    have h3 : (log (n : ℝ) + (1 / (n : ℝ) + eulerMascheroniConstant)) / log (n : ℝ) - 1 =
        (1 / (n : ℝ) + eulerMascheroniConstant) / log (n : ℝ) := by
      field_simp
      ring
    linarith
  have hlogH0 : 0 ≤ log (harmonic n : ℝ) := log_nonneg hH1.le
  -- `0 ≤ log (log n) ≤ log n - 1`
  have hLL0 : 0 ≤ log (log (n : ℝ)) := log_nonneg hL1.le
  have hLL : log (log (n : ℝ)) ≤ log (n : ℝ) - 1 := log_le_sub_one_of_pos hL0
  -- `(log n) ^ 2 ≤ 4 * n`
  have hsq : log (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
    have hs0 : 0 < √(n : ℝ) := sqrt_pos.mpr hx0
    have h1 := log_le_sub_one_of_pos hs0
    rw [log_sqrt hx0.le] at h1
    have h2 : log (n : ℝ) ≤ 2 * √(n : ℝ) := by linarith
    calc log (n : ℝ) ^ 2 ≤ (2 * √(n : ℝ)) ^ 2 := pow_le_pow_left₀ hL0.le h2 2
      _ = 4 * (n : ℝ) := by rw [mul_pow, sq_sqrt hx0.le]; norm_num
  -- product of the two bounds
  have hprod : exp (harmonic n : ℝ) * log (harmonic n : ℝ) ≤
      ((n : ℝ) + 1) * exp eulerMascheroniConstant *
        (log (log (n : ℝ)) + (1 / (n : ℝ) + eulerMascheroniConstant) / log (n : ℝ)) :=
    mul_le_mul hexp hlogH hlogH0 (by positivity)
  -- the three error terms
  have ha : (harmonic n : ℝ) * log (n : ℝ) ≤ (log (n : ℝ) + 0.72) * log (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hL0.le
  have hb : exp eulerMascheroniConstant * log (log (n : ℝ)) * log (n : ℝ) ≤
      2 * (log (n : ℝ) - 1) * log (n : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hg2.le hLL hLL0 (by norm_num)) hL0.le
  have hc : exp eulerMascheroniConstant * ((n : ℝ) + 1) *
      (1 / (n : ℝ) + eulerMascheroniConstant) ≤ 2 * ((n : ℝ) + 1) * 0.72 :=
    mul_le_mul (mul_le_mul_of_nonneg_right hg2.le (by positivity)) hδ hδ0.le (by positivity)
  have key : ((harmonic n : ℝ) + exp eulerMascheroniConstant * log (log (n : ℝ))) *
      log (n : ℝ) + exp eulerMascheroniConstant * ((n : ℝ) + 1) *
        (1 / (n : ℝ) + eulerMascheroniConstant) ≤ 24 * (n : ℝ) := by
    nlinarith [ha, hb, hc, hsq, hL1, hx20]
  calc (harmonic n : ℝ) + exp (harmonic n : ℝ) * log (harmonic n : ℝ)
      ≤ (harmonic n : ℝ) + ((n : ℝ) + 1) * exp eulerMascheroniConstant *
          (log (log (n : ℝ)) + (1 / (n : ℝ) + eulerMascheroniConstant) / log (n : ℝ)) := by
        linarith
    _ = exp eulerMascheroniConstant * (n : ℝ) * log (log (n : ℝ)) +
          (((harmonic n : ℝ) + exp eulerMascheroniConstant * log (log (n : ℝ))) *
            log (n : ℝ) + exp eulerMascheroniConstant * ((n : ℝ) + 1) *
              (1 / (n : ℝ) + eulerMascheroniConstant)) / log (n : ℝ) := by
        field_simp
        ring
    _ ≤ exp eulerMascheroniConstant * (n : ℝ) * log (log (n : ℝ)) +
          24 * (n : ℝ) / log (n : ℝ) := by
        linarith [div_le_div_of_nonneg_right key hL0.le]

end LagariasUpperStep

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1.H2 :=
  LagariasUpperStep.lag_upper
