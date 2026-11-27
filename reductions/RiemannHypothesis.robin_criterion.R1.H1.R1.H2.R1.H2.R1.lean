import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1
import Mathlib

/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
Prime block decomposition and explicit scalar from kimihiro64/Robin1984, commit
e3697139babfe0f6cc7a76a08bf41a92aa7a2978, Apache-2.0. -/
namespace OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1
open Finset Real

/-- The analytic Abel-summation lower bound for the prime-square block under RH. -/
def H1 : Prop :=
  RiemannHypothesis → ∀ H : ℝ, exp 30 < H →
    let s := Real.sqrt (2 * H)
    let b := H / 2
    let err := (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
      (b ^ ((1 / 2 : ℝ) - 2) * (Real.log b)⁻¹ *
        (2 + (Real.log b)⁻¹ + 4 / (3 * (Real.log b)^2)))
    let L := 2 * s^(-(1 : ℝ)) * (Real.log s)⁻¹ -
      s^(-(1 : ℝ)) * ((Real.log s)^2)⁻¹ -
      (9 / 4 : ℝ) * s^(-(3 / 2 : ℝ)) * (Real.log s)⁻¹ -
      Real.log (2 * Real.pi) * s^(-(2 : ℝ)) * (Real.log s)⁻¹ -
      2 * b^(-(1 : ℝ)) * (Real.log b)⁻¹ - err
    L ≤ Chebyshev.theta s / (s^2 * Real.log s) +
      ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2

/-- The explicit numerical estimate for the scalar lower bound. -/
def H2 : Prop :=
  ∀ H : ℝ, exp 30 < H →
    let s := Real.sqrt (2 * H)
    let b := H / 2
    let err := (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
      (b ^ ((1 / 2 : ℝ) - 2) * (Real.log b)⁻¹ *
        (2 + (Real.log b)⁻¹ + 4 / (3 * (Real.log b)^2)))
    let L := 2 * s^(-(1 : ℝ)) * (Real.log s)⁻¹ -
      s^(-(1 : ℝ)) * ((Real.log s)^2)⁻¹ -
      (9 / 4 : ℝ) * s^(-(3 / 2 : ℝ)) * (Real.log s)⁻¹ -
      Real.log (2 * Real.pi) * s^(-(2 : ℝ)) * (Real.log s)⁻¹ -
      2 * b^(-(1 : ℝ)) * (Real.log b)⁻¹ - err
    (113/50 : ℝ) * (H^(-(1/2 : ℝ)) * (Real.log H)⁻¹) ≤ L

/-- Split the finite prime sum at s and bound each minimum on its own range. -/
def H3 : Prop :=
  ∀ H s b : ℝ, 1 < H → 1 < s → s ≤ b → H * log H ≤ s^2 * log s →
    Chebyshev.theta s / (s^2 * Real.log s) +
      ∑ p ∈ (Finset.Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ ^ 2 ≤
      ∑ p ∈ Nat.primesLE ⌊b⌋₊, min (log p / (H * log H)) ((p : ℝ)⁻¹ ^ 2)

theorem main : H1 → H2 → H3 → OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1.H2 := by
  intro analytic scalar split rh H hH
  have hbig : 32 ≤ H := by
    have h : (2:ℝ)^30 ≤ (exp 1)^30 := by gcongr; exact exp_one_gt_two.le
    have he : (exp 1)^30 = exp 30 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he] at h
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2*H by linarith)
  have hnon := Real.sqrt_nonneg (2*H)
  have hlow : 1 < sqrt (2*H) := by nlinarith
  have hhi : sqrt (2*H) ≤ H/2 := by
    nlinarith [mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H-8 by linarith)]
  have hlog : log (sqrt (2*H)) = (log 2 + log H) / 2 := by
    rw [Real.log_sqrt (by linarith), Real.log_mul (by norm_num) (by linarith)]
  have hden : H*log H ≤ sqrt (2*H)^2*log (sqrt (2*H)) := by
    rw [hs,hlog]
    nlinarith [mul_nonneg (show 0 ≤ H by linarith) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  exact (scalar H hH).trans ((analytic rh H hH).trans
    (split H _ _ (by linarith) hlow hhi hden))

end OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1
