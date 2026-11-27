import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1
import Mathlib

/- Copyright (c) 2026 Jonas Whidden. All rights reserved.
The theta tail estimates are from Robin1984/Analytic/PrimeSquareAbelBound.lean,
kimihiro64/Robin1984, revision e3697139babfe0f6cc7a76a08bf41a92aa7a2978,
used under Apache-2.0. -/
namespace OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1
open Real Finset MeasureTheory

/-- Lower tail estimate for the second theta weight under RH. -/
def H1 : Prop := RiemannHypothesis → ∀ s : ℝ, 366 ≤ s →
  2*s^(-(1:ℝ))*(log s)⁻¹-s^(-(1:ℝ))*((log s)^2)⁻¹-
    (9/4:ℝ)*s^(-(3/2:ℝ))*(log s)⁻¹-log (2*Real.pi)*s^(-(2:ℝ))*(log s)⁻¹ ≤ (∫ t in Set.Ioi s, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)

/-- Upper tail estimate, with the absolute sum over nontrivial zeros. -/
def H2 : Prop := RiemannHypothesis → ∀ b : ℝ, 2 ≤ b →
  (∫ t in Set.Ioi b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) ≤ 2*b^(-(1:ℝ))*(log b)⁻¹ +
    (Real.eulerMascheroniConstant+2-log (4*Real.pi)) *
      (b^((1/2:ℝ)-2)*(log b)⁻¹*(2+(log b)⁻¹+4/(3*(log b)^2)))

/-- The exact finite Abel identity for the kernel 1/(t² log t). -/
def H3 : Prop := ∀ s b : ℝ, 1<s → s ≤ b →
  Chebyshev.theta s/(s^2*log s) +
    (∑ p ∈ (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime, (p:ℝ)⁻¹^2) =
  Chebyshev.theta b/(b^2*log b) + (∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)

/-- Splitting the two convergent improper theta integrals at b. -/
def H4 : Prop := ∀ s b : ℝ, 366 ≤ s → s ≤ b →
  (∫ t in Set.Ioi s, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) - (∫ t in Set.Ioi b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t) = (∫ t in Set.Ioc s b, ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t)

theorem main : H1 → H2 → H3 → H4 → OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro lo hi identity tailSplit rh H hH
  have big : (2:ℝ)^30 ≤ H := by
    have h : (2:ℝ)^30 ≤ (exp 1)^30 := by gcongr; exact exp_one_gt_two.le
    have e : (exp 1)^30 = exp 30 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e] at h
    exact h.trans hH.le
  have hs := Real.sq_sqrt (show 0 ≤ 2*H by linarith)
  have non := Real.sqrt_nonneg (2*H)
  have lower : 366 ≤ sqrt (2*H) := by nlinarith
  have upper : sqrt (2*H) ≤ H/2 := by
    nlinarith [mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H-8 by linarith)]
  dsimp only
  rw [identity _ _ (by linarith) upper, ← tailSplit _ _ lower upper]
  have h : 0 ≤ Chebyshev.theta (H/2)/((H/2)^2*log (H/2)) :=
    div_nonneg (Chebyshev.theta_nonneg _) (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith)))
  linarith only [h,lo rh _ lower,hi rh (H/2) (by linarith)]

end OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1

