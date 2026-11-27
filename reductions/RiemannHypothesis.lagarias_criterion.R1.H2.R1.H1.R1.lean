import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1
import Mathlib

/-! The oscillation is sampled on the integers lcm(1,...,P). The Nicolas
function and the logarithmic margin are from Jonas Whidden, Robin1984,
e3697139babfe0f6cc7a76a08bf41a92aa7a2978, Apache-2.0. The proof here
quantifies the passage from the logarithmic margin to the divisor-sum excess. -/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1
open Real Filter MeasureTheory
open scoped ArithmeticFunction.sigma

/-- The negative logarithmic oscillation of Nicolas's Mertens product when
there is a zeta zero off the critical line. -/
def H1 : Prop := ¬ RiemannHypothesis → ∃ b c : ℝ, 0<b ∧ b<1/2 ∧ 0<c ∧
  ∃ᶠ x : ℝ in atTop, c*x^(-b) ≤ -(log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))))

/-- The loss incurred by transferring the Mertens product to the
logarithmic divisor-sum margin of the complete lcm is little-o of x to minus b. -/
def H2 : Prop := ∀ b : ℝ, 0<b → b<1/2 → ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop,
  let n := Nat.lcmUpto ⌊x⌋₊;
  -(log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ)))) - ε*x^(-b) ≤
    log ((σ 1 n : ℝ)/n) - eulerMascheroniConstant - log (log (log n))

lemma height {P : ℕ} (hP : 40≤P) : (P:ℝ)/8 ≤ log (Nat.lcmUpto P) := by
  have P40 : (40:ℝ)≤P := by exact_mod_cast hP
  have Ppos : (0:ℝ)<P+1 := by positivity
  have hlog := log_le_sub_one_of_pos (show 0<((P:ℝ)+1)/4 by positivity)
  rw [log_div (by positivity) (by norm_num)] at hlog
  have hfour : log 4 < 2 := by
    rw [show (4:ℝ)=2*2 by norm_num,log_mul (by norm_num) (by norm_num)]
    linarith only [log_two_lt_d9]
  have hhalf : (1:ℝ)/2 < log 2 := by linarith only [log_two_gt_d9]
  have h := Chebyshev.psi_ge P
  rw [Chebyshev.psi_eq_log_lcmUpto] at h
  nlinarith [mul_le_mul_of_nonneg_left hhalf.le (show (0:ℝ)≤P by positivity)]

lemma additive {a v z : ℝ} (ha : 0<a) (hv : 1≤v) (hz : 0≤z)
    (h : z≤log a-log v) : v+z≤a := by
  have vp : 0<v := by linarith
  have ex := exp_le_exp.mpr h
  rw [exp_sub,exp_log ha,exp_log vp] at ex
  have h₁ := (le_div_iff₀ vp).mp ((add_one_le_exp z).trans ex)
  nlinarith [mul_nonneg (sub_nonneg.mpr hv) hz]

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1.H1 := by
  intro oscillation loss neg
  obtain ⟨b,c,bp,bh,cp,large⟩ := oscillation neg
  let c' := (c/2)/(16:ℝ)^b
  have cp' : 0<c' := by dsimp [c']; positivity
  refine ⟨b,c',bp,bh,cp',frequently_atTop.mpr ?_⟩
  intro N
  have both := large.and_eventually (loss b bp bh (c/2) (half_pos cp))
  obtain ⟨x,hx,exc,err⟩ := frequently_atTop.mp both (max (N:ℝ) 40)
  let P := ⌊x⌋₊
  let n := Nat.lcmUpto P
  have hx40 : 40≤x := (le_max_right _ _).trans hx
  have xp : 0<x := by linarith
  have P40 : 40≤P := (Nat.le_floor_iff xp.le).mpr (by exact_mod_cast hx40)
  have NP : N≤P := (Nat.le_floor_iff xp.le).mpr ((le_max_left _ _).trans hx)
  have Pn : P≤n := by
    apply Nat.le_of_dvd (Nat.lcmUpto_pos _)
    have oneP : 1≤P := (by decide : 1≤40).trans P40
    have member : P ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨oneP,le_rfl⟩
    exact Finset.dvd_lcm (s := Finset.Icc 1 P) (f := id) member
  have np : (0:ℝ)<n := by exact_mod_cast Nat.lcmUpto_pos P
  have hP : (40:ℝ)≤P := by exact_mod_cast P40
  have hL : (P:ℝ)/8 ≤ log n := height P40
  have lp : 0<log n := by linarith
  have xP : x<(P:ℝ)+1 := Nat.lt_floor_add_one x
  have xL : x≤16*log n := by linarith
  have logOne : 1≤log (log n) := ((lt_log_iff_exp_lt lp).mpr (by linarith [exp_one_lt_three])).le
  let B := exp eulerMascheroniConstant*log (log n)
  have B1 : 1≤B := by
    have e : (1:ℝ)≤exp eulerMascheroniConstant := one_le_exp (by linarith [one_half_lt_eulerMascheroniConstant])
    exact one_le_mul_of_one_le_of_one_le e logOne
  have ap : 0 < (σ 1 n : ℝ)/n := by
    apply div_pos _ np
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by exact Nat.ne_of_gt (Nat.lcmUpto_pos P))
  have zpos : 0≤c/2*x^(-b) := (mul_pos (half_pos cp) (rpow_pos_of_pos xp _)).le
  have hgap : c/2*x^(-b) ≤ log ((σ 1 n:ℝ)/n)-log B := by
    change _ ≤ log ((σ 1 n:ℝ)/n)-eulerMascheroniConstant-log (log (log n)) at err
    have logB : log B = eulerMascheroniConstant+log (log (log n)) := by
      rw [show B=exp eulerMascheroniConstant*log (log n) by rfl,log_mul (exp_pos _).ne' (by linarith),log_exp]
    rw [logB]
    linarith only [exc,err]
  have bound := additive ap B1 zpos hgap
  have scaled : c'/(log n)^b ≤ c/2*x^(-b) := by
    dsimp [c']
    rw [rpow_neg xp.le,← div_eq_mul_inv,div_div,←mul_rpow (by norm_num : (0:ℝ)≤16) lp.le]
    exact div_le_div_of_nonneg_left (half_pos cp).le (rpow_pos_of_pos xp _) (rpow_le_rpow xp.le xL bp.le)
  refine ⟨n,NP.trans Pn,?_⟩
  have out := (le_div_iff₀ np).mp ((add_le_add (le_refl B) scaled).trans bound)
  dsimp [B] at out
  linarith only [show exp eulerMascheroniConstant * (n:ℝ) * log (log n) +
      c'*(n:ℝ)/(log n)^b = (exp eulerMascheroniConstant*log (log n)+c'/(log n)^b)*n by ring,out]

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1

