import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1
import Mathlib

/-! The oscillatory term is now the tail integral of the Chebyshev psi
error. Nicolas's Mertens-product comparison has error at most four over x.
The two estimates are the analytic and finite-product parts of Nicolas's
argument, as separated in Jonas Whidden's Robin1984, Apache-2.0,
e3697139babfe0f6cc7a76a08bf41a92aa7a2978. -/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1
open Real Filter MeasureTheory Set Asymptotics
open scoped Topology

/-- Off-line zeros force negative excursions of the psi-error tail. -/
def H1 : Prop := ¬RiemannHypothesis → ∃ b c : ℝ, 0<b ∧ b<1/2 ∧ 0<c ∧
  ∃ᶠ x : ℝ in atTop, c*x^(-b) ≤
    -(∫ t in Ioi x, (Chebyshev.psi t-t) * ((1/log t+1/(log t)^2)/t^2))

/-- Comparison between the finite product and the tail integral. -/
def H2 : Prop := ∀ᶠ x : ℝ in atTop,
  log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤
    (∫ t in Ioi x, (Chebyshev.psi t-t) * ((1/log t+1/(log t)^2)/t^2))+4/x

theorem rpow_neg_one_isLittleO_rpow_neg
    {b : Real} (hb : b < 1) :
    Asymptotics.IsLittleO atTop
      (fun x : Real => x ^ (-(1 : Real)))
      (fun x : Real => x ^ (-b)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hDecay : Tendsto
      (fun x : Real => x ^ (-(1 - b))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hSmall : Filter.Eventually
      (fun x : Real => x ^ (-(1 - b)) < c) atTop :=
    hDecay.eventually_lt_const hc
  filter_upwards [hSmall, eventually_gt_atTop (0 : Real)] with x hxSmall hxPos
  have hRecipPos : 0 < x ^ (-(1 : Real)) :=
    Real.rpow_pos_of_pos hxPos _
  have hMainPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hRecipPos,
    abs_of_pos hMainPos]
  have hFactor :
      x ^ (-(1 : Real)) = x ^ (-b) * x ^ (-(1 - b)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [hFactor]
  calc
    x ^ (-b) * x ^ (-(1 - b)) <= x ^ (-b) * c :=
      mul_le_mul_of_nonneg_left hxSmall.le hMainPos.le
    _ = c * x ^ (-b) := by ring


theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1.H1 := by
  intro osc cmp neg
  obtain ⟨b,c,bp,bh,cp,h⟩ := osc neg
  have sm : (fun x : ℝ => x^(-1:ℝ)) =o[atTop] (fun x : ℝ => x^(-b)) :=
    rpow_neg_one_isLittleO_rpow_neg (by linarith)
  have err := sm.bound (show 0<c/8 by positivity)
  refine ⟨b,c/2,bp,bh,half_pos cp,?_⟩
  apply (h.and_eventually (cmp.and (err.and (eventually_gt_atTop (0:ℝ))))).mono
  rintro x ⟨hx,hc,he,hp⟩
  simp only [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hp _)] at he
  rw [rpow_neg_one] at he
  rw [div_eq_mul_inv] at hc
  linarith

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1
