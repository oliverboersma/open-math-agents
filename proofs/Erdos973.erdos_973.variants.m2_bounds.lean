import FormalConjectures.ErdosProblems.«973»
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Bounds for the least maximum of the complex power sums. -/

/- Lower estimate for Erdős 973, via the reciprocal root polynomial and its exponential approximation. See L. Erdős (1992), https://doi.org/10.1007/BF00052086. -/

open Finset
open scoped Nat BigOperators PowerSeries Classical

namespace PowerSumLower973

noncomputable section

def psum (s : Finset ℕ) (z : ℕ→ℂ) (k : ℕ) : ℂ := ∑ i ∈ s, z i^k

def rootPoly (s : Finset ℕ) (z : ℕ→ℂ) : Polynomial ℂ :=
  ∏ i ∈ s, (1 - Polynomial.C (z i) * Polynomial.X)

private def factor (z : ℂ) : PowerSeries ℂ := 1 - PowerSeries.C z * PowerSeries.X

private def geom (z : ℂ) : PowerSeries ℂ := PowerSeries.mk fun k => z^k

private theorem factor_geom (z : ℂ) : factor z * geom z = 1 := by
  ext k
  rw [factor,sub_mul,one_mul,map_sub]
  rw [show (PowerSeries.C z * PowerSeries.X) * geom z =
    PowerSeries.C z * (geom z * PowerSeries.X^1) from by rw [pow_one]; ring,
    PowerSeries.coeff_C_mul]
  cases k with
  | zero =>
    simp [geom]
  | succ k =>
    simp [geom,pow_succ']

private theorem factor_derivative (z : ℂ) :
    PowerSeries.derivative ℂ (factor z) = factor z * -(PowerSeries.C z * geom z) := by
  have h : factor z * (PowerSeries.C z * geom z) = PowerSeries.C z := calc
    _ = PowerSeries.C z * (factor z * geom z) := by ring
    _ = _ := by rw [factor_geom,mul_one]
  rw [mul_neg,h]
  simp [factor,Derivation.leibniz,smul_eq_mul]

private theorem derivative_prod_relative (s : Finset ℕ) (f g : ℕ → PowerSeries ℂ)
    (h : ∀ i, PowerSeries.derivative ℂ (f i) = f i * g i) :
    PowerSeries.derivative ℂ (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi,sum_insert hi,Derivation.leibniz,h,ih]
    simp only [smul_eq_mul]
    ring

private theorem rootPoly_coe (s : Finset ℕ) (z : ℕ→ℂ) :
    (rootPoly s z : PowerSeries ℂ) = ∏ i ∈ s, factor (z i) := by
  rw [rootPoly,← Polynomial.coeToPowerSeries.ringHom_apply,map_prod]
  simp [factor,Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_sub]

private def expS (w : ℂ) : PowerSeries ℂ := PowerSeries.rescale w (PowerSeries.exp ℂ)

theorem coeff_expS (w : ℂ) (k : ℕ) :
    PowerSeries.coeff k (expS w) = w^k / (k ! : ℂ) := by
  rw [expS,PowerSeries.coeff_rescale,PowerSeries.coeff_exp,map_div₀,map_one,map_natCast]
  ring

private theorem expS_derivative (w : ℂ) :
    PowerSeries.derivative ℂ (expS w) = PowerSeries.C w * expS w := by
  ext k
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_C_mul,coeff_expS,coeff_expS,
    Nat.factorial_succ,pow_succ]
  push_cast
  have hk : (k:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

private def correction (s : Finset ℕ) (z : ℕ→ℂ) : PowerSeries ℂ :=
  (rootPoly s z : PowerSeries ℂ) * expS (psum s z 1)

private def logResidual (s : Finset ℕ) (z : ℕ→ℂ) : PowerSeries ℂ :=
  PowerSeries.C (psum s z 1) + ∑ i ∈ s, -(PowerSeries.C (z i) * geom (z i))

private theorem coeff_logResidual (s : Finset ℕ) (z : ℕ→ℂ) (k : ℕ) :
    PowerSeries.coeff k (logResidual s z) = if k=0 then 0 else - psum s z (k+1) := by
  rw [logResidual,map_add,map_sum]
  have hg (i : ℕ) : PowerSeries.coeff k (-(PowerSeries.C (z i) * geom (z i))) =
      -(z i)^(k+1) := by
    rw [map_neg,PowerSeries.coeff_C_mul,geom,PowerSeries.coeff_mk,pow_succ']
  simp_rw [hg]
  cases k <;> simp [psum,PowerSeries.coeff_C]

private theorem correction_deriv (s : Finset ℕ) (z : ℕ→ℂ) :
    PowerSeries.derivative ℂ (correction s z) = correction s z * logResidual s z := by
  rw [correction,Derivation.leibniz,expS_derivative,rootPoly_coe,
    derivative_prod_relative s (fun i => factor (z i)) _ (fun i => factor_derivative (z i))]
  rw [logResidual]
  simp only [smul_eq_mul]
  ring

private theorem correction_const (s : Finset ℕ) (z : ℕ→ℂ) :
    PowerSeries.coeff 0 (correction s z) = 1 := by
  have h : PowerSeries.constantCoeff (expS (psum s z 1)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_expS]
    simp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,correction,rootPoly_coe]
  simp [factor,h]

private theorem root_eq (s : Finset ℕ) (z : ℕ→ℂ) :
    (rootPoly s z : PowerSeries ℂ) = expS (-psum s z 1) * correction s z := by
  have h : expS (-(psum s z 1)) * expS (psum s z 1) = 1 := by
    rw [expS,expS,PowerSeries.exp_mul_exp_eq_exp_add,neg_add_cancel]
    simp
  rw [correction]
  calc
    _ = (rootPoly s z : PowerSeries ℂ) * (expS (-(psum s z 1)) * expS (psum s z 1)) := by rw [h,mul_one]
    _ = _ := by ring

end

end PowerSumLower973

namespace PowerSumLower973

noncomputable section

private theorem correction_step (s : Finset ℕ) (z : ℕ→ℂ) {N : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (h : ∀ j ∈ Icc 2 N, ‖psum s z j‖ ≤ ε) {k : ℕ} (hk : k+1 ≤ N) :
    ‖PowerSeries.coeff (k+1) (correction s z)‖ ≤
      ε * ∑ i ∈ range (k+1), ‖PowerSeries.coeff i (correction s z)‖ := by
  let B := correction s z
  let T := logResidual s z
  have hc : PowerSeries.coeff (k+1) B * ((k:ℂ)+1) =
      ∑ i ∈ range (k+1), PowerSeries.coeff i B * PowerSeries.coeff (k-i) T := by
    have hg := congrArg (PowerSeries.coeff k) (correction_deriv s z)
    rw [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hg
    exact hg
  have ht (i : ℕ) (hi : i ∈ range (k+1)) : ‖PowerSeries.coeff (k-i) T‖ ≤ ε := by
    rw [show T = logResidual s z from rfl,coeff_logResidual]
    by_cases hi0 : k-i=0
    · simpa [hi0] using he
    · have hin : k-i+1 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega,by omega⟩
      simpa [hi0] using h _ hin
  have h1 : 1 ≤ ‖(k:ℂ)+1‖ := by
    rw [← Nat.cast_succ,Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos k
  calc
    ‖PowerSeries.coeff (k+1) B‖ ≤ ‖PowerSeries.coeff (k+1) B * ((k:ℂ)+1)‖ := by
      rw [norm_mul]
      exact le_mul_of_one_le_right (norm_nonneg _) h1
    _ ≤ ∑ i ∈ range (k+1), ‖PowerSeries.coeff i B * PowerSeries.coeff (k-i) T‖ := by
      rw [hc]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ range (k+1), ε * ‖PowerSeries.coeff i B‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,mul_comm ε]
      exact mul_le_mul_of_nonneg_left (ht i hi) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

private theorem correction_sum (s : Finset ℕ) (z : ℕ→ℂ) {N : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (h : ∀ j ∈ Icc 2 N, ‖psum s z j‖ ≤ ε) :
    ∑ i ∈ range (N+1), ‖PowerSeries.coeff i (correction s z)‖ ≤ (1+ε)^N := by
  have hsum (k : ℕ) (hk : k ≤ N) :
      ∑ i ∈ range (k+1), ‖PowerSeries.coeff i (correction s z)‖ ≤ (1+ε)^k := by
    induction k with
    | zero => simp [correction_const]
    | succ k ih =>
      have hstep := correction_step s z he h hk
      rw [sum_range_succ]
      calc
        _ ≤ (∑ i ∈ range (k+1), ‖PowerSeries.coeff i (correction s z)‖) +
            ε * ∑ i ∈ range (k+1), ‖PowerSeries.coeff i (correction s z)‖ :=
          add_le_add_right hstep _
        _ = (∑ i ∈ range (k+1), ‖PowerSeries.coeff i (correction s z)‖)*(1+ε) := by ring
        _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_right (ih (by omega)) (by linarith)
  exact hsum N le_rfl

private theorem correction_error_sum (s : Finset ℕ) (z : ℕ→ℂ) {N : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (h : ∀ j ∈ Icc 2 N, ‖psum s z j‖ ≤ ε) :
    ∑ i ∈ range (N+1), ‖PowerSeries.coeff i (correction s z-1)‖ ≤ (1+ε)^N-1 := by
  have hsum := correction_sum s z he h
  rw [sum_range_succ'] at hsum ⊢
  simp only [map_sub,PowerSeries.coeff_one,Nat.succ_ne_zero,if_false,sub_zero,
    correction_const,if_true,sub_self,norm_zero,add_zero,norm_one] at hsum ⊢
  linarith

set_option maxHeartbeats 500000 in
theorem coefficient_error (s : Finset ℕ) (z : ℕ→ℂ) {N : ℕ} {ε : ℝ} (he : 0 ≤ ε)
    (h : ∀ j ∈ Icc 2 N, ‖psum s z j‖ ≤ ε) {k : ℕ} (hk : k ≤ N) :
    ‖(rootPoly s z).coeff k - (-psum s z 1)^k / (k ! : ℂ)‖ ≤
      Real.exp ‖psum s z 1‖ * ((1+ε)^N-1) := by
  let A := expS (-psum s z 1)
  let B := correction s z - 1
  have hAB : (rootPoly s z : PowerSeries ℂ)-A=A*B := by
    rw [show (rootPoly s z : PowerSeries ℂ) = A*correction s z from root_eq s z]
    simp only [B,mul_sub,mul_one]
  have hSub : Finset.HasAntidiagonal.antidiagonal k ⊆ range (N+1) ×ˢ range (N+1) := by
    intro i hi
    have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
  have ha : ∑ i ∈ range (N+1), ‖PowerSeries.coeff i A‖ ≤ Real.exp ‖psum s z 1‖ := by
    simp only [A,coeff_expS,norm_div,norm_pow,norm_neg,Complex.norm_natCast]
    exact Real.sum_le_exp_of_nonneg (norm_nonneg _) _
  have hb := correction_error_sum s z he h
  have hb0 : 0 ≤ ∑ i ∈ range (N+1), ‖PowerSeries.coeff i B‖ := by positivity
  have hab (i j : ℕ) := norm_mul (PowerSeries.coeff i A) (PowerSeries.coeff j B)
  rw [← Polynomial.coeff_coe,← coeff_expS,← map_sub]
  change ‖PowerSeries.coeff k ((rootPoly s z : PowerSeries ℂ)-A)‖ ≤ _
  rw [hAB,PowerSeries.coeff_mul]
  calc
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ range (N+1) ×ˢ range (N+1), ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun _ _ _ => norm_nonneg _)
    _ = (∑ i ∈ range (N+1), ‖PowerSeries.coeff i A‖)*(∑ i ∈ range (N+1), ‖PowerSeries.coeff i B‖) := by
      rw [Finset.sum_product]
      simp_rw [hab,← Finset.mul_sum,← Finset.sum_mul]
    _ ≤ _ := mul_le_mul ha hb hb0 (Real.exp_nonneg _)

private theorem rootPoly_deg (s : Finset ℕ) (z : ℕ→ℂ) :
    (rootPoly s z).natDegree ≤ s.card := by
  unfold rootPoly
  calc
    _ ≤ ∑ i ∈ s, (1 - Polynomial.C (z i) * Polynomial.X : Polynomial ℂ).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun i _ => by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      simpa using Polynomial.natDegree_mul_le (p := Polynomial.C (z i)) (q := Polynomial.X)
    _ = _ := by simp

/-- Two scalar consequences of small higher power sums when the tuple contains the unit root 1. -/
theorem lower_certificate (s : Finset ℕ) (z : ℕ→ℂ) {ε : ℝ} (he : 0 ≤ ε)
    (hroot : ∃ j ∈ s, z j=1) (h : ∀ j ∈ Icc 2 (s.card+1), ‖psum s z j‖ ≤ ε) :
    ‖psum s z 1‖^(s.card+1)/(Nat.factorial (s.card+1):ℝ) ≤
      Real.exp ‖psum s z 1‖ * ((1+ε)^(s.card+1)-1) ∧
    ‖∑ k ∈ range (s.card+1), (-psum s z 1)^k/(k ! : ℂ)‖ ≤
      (s.card+1:ℕ) * (Real.exp ‖psum s z 1‖ * ((1+ε)^(s.card+1)-1)) := by
  have hz : (rootPoly s z).coeff (s.card+1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le (rootPoly_deg s z))
  have h0 : Polynomial.eval (1:ℂ) (rootPoly s z) = 0 := by
    obtain ⟨j,hj,hj1⟩ := hroot
    rw [rootPoly,Polynomial.eval_prod]
    exact Finset.prod_eq_zero hj (by simp [hj1])
  have hsum : ∑ k ∈ range (s.card+1), (rootPoly s z).coeff k = 0 := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (rootPoly_deg s z))] at h0
    simpa using h0
  constructor
  · have hc := coefficient_error s z he h (k := s.card+1) le_rfl
    simpa only [hz,zero_sub,norm_neg,norm_div,norm_pow,Complex.norm_natCast] using hc
  · calc
      _ = ‖∑ k ∈ range (s.card+1), ((rootPoly s z).coeff k - (-psum s z 1)^k/(k ! : ℂ))‖ := by
        rw [Finset.sum_sub_distrib,hsum,zero_sub,norm_neg]
      _ ≤ ∑ k ∈ range (s.card+1), ‖(rootPoly s z).coeff k - (-psum s z 1)^k/(k ! : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (s.card+1), Real.exp ‖psum s z 1‖ * ((1+ε)^(s.card+1)-1) :=
        Finset.sum_le_sum fun k hk => coefficient_error s z he h (le_of_lt (mem_range.mp hk))
      _ = _ := by simp

end

end PowerSumLower973

open Filter

open scoped Topology

namespace PowerSumLower973

noncomputable section

def alpha : ℝ := 0.2784

def beta : ℝ := 0.5728

def mainBase : ℝ := alpha * Real.exp (1-alpha)

def tailBase : ℝ := alpha * Real.exp (1+alpha)

theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem alpha_lt_one : alpha < 1 := by norm_num [alpha]
theorem beta_pos : 0 < beta := by norm_num [beta]
theorem beta_lt_one : beta < 1 := by norm_num [beta]
theorem inv_bound_lt_beta : ((1.746:ℝ)⁻¹) < beta := by norm_num [beta]

theorem tailBase_lt_one : tailBase < 1 := by
  have h := Real.exp_bound' (x := alpha) alpha_pos.le alpha_lt_one.le (n := 8) (by decide)
  have ha : Real.exp alpha ≤ 1.3211 := h.trans (by norm_num [alpha,Finset.sum_range_succ,Nat.factorial])
  rw [tailBase,Real.exp_add]
  have hb := mul_le_mul Real.exp_one_lt_d9.le ha (Real.exp_nonneg _) (by norm_num)
  have hc := mul_le_mul_of_nonneg_left hb alpha_pos.le
  exact hc.trans_lt (by norm_num [alpha])

theorem beta_lt_mainBase : beta < mainBase := by
  have h := Real.sum_le_exp_of_nonneg (x := 1-alpha) (by linarith [alpha_lt_one]) 8
  have ha : (2.0577:ℝ) ≤ Real.exp (1-alpha) := (by norm_num [alpha,Finset.sum_range_succ,Nat.factorial]
    : (2.0577:ℝ) ≤ ∑ j ∈ range 8, (1-alpha)^j/(j ! : ℝ)).trans h
  exact (by norm_num [alpha,beta] : beta < alpha*2.0577).trans_le
    (mul_le_mul_of_nonneg_left ha alpha_pos.le)

theorem beta_mul_exp_lt_one : beta * Real.exp (2*alpha) < 1 := by
  have h := Real.exp_bound' (x := 2*alpha) (by positivity [alpha_pos]) (by norm_num [alpha])
    (n := 8) (by decide)
  have ha : Real.exp (2*alpha) ≤ 1.7452 := h.trans (by norm_num [alpha,Finset.sum_range_succ,Nat.factorial])
  exact (mul_le_mul_of_nonneg_left ha beta_pos.le).trans_lt (by norm_num [beta])

private theorem factorial_upper {n : ℕ} (hn : 0 < n) :
    (n ! : ℝ) ≤ 6*(n:ℝ)*((n:ℝ)/Real.exp 1)^n := by
  have h₀ := Stirling.stirlingSeq'_antitone (Nat.zero_le (n-1))
  have h₁ : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    simpa [Function.comp_apply, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)] using h₀
  rw [Stirling.stirlingSeq,Stirling.stirlingSeq_one] at h₁
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 < Real.sqrt (2*(n:ℝ)) * ((n:ℝ)/Real.exp 1)^n := by positivity
  have h := (div_le_iff₀ hq).mp h₁
  have hs : Real.sqrt (2*(n:ℝ)) ≤ 2*n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have he : Real.exp 1/Real.sqrt 2 ≤ 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have ht : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    linarith [Real.exp_one_lt_three]
  calc
    _ ≤ _ := h
    _ ≤ 3 * (2*(n:ℝ)*((n:ℝ)/Real.exp 1)^n) := by gcongr
    _ = _ := by ring

private theorem factorial_lower {n : ℕ} (hn : 0 < n) :
    ((n:ℝ)/Real.exp 1)^n ≤ (n ! : ℝ) := by
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ 2*Real.pi*(n:ℝ) := by
    nlinarith only [Real.pi_gt_three, hN, mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi)
      (sub_nonneg.mpr hN)]
  have hs : 1 ≤ Real.sqrt (2*Real.pi*(n:ℝ)) := Real.one_le_sqrt.mpr hp
  have hh := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ ((n:ℝ)/Real.exp 1)^n)
  rw [one_mul] at hh
  exact hh.trans (Stirling.le_factorial_stirling n)

private def expTerm (A : ℝ) (n : ℕ) : ℝ := A^n/(n ! : ℝ)

private theorem expTerm_succ (A : ℝ) (n : ℕ) :
    expTerm A (n+1) = expTerm A n * (A / ((n:ℝ)+1)) := by
  simp only [expTerm,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ,div_mul_div_comm]
  ring

private theorem expTerm_nonneg {A : ℝ} (hA : 0 ≤ A) (n : ℕ) : 0 ≤ expTerm A n := by
  unfold expTerm
  positivity

private theorem tail_term_le {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (h : A ≤ alpha*(N:ℝ))
    (k : ℕ) : expTerm A (k+N) ≤ expTerm A N * alpha^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k+1+N=k+N+1 by omega,expTerm_succ,pow_succ,← mul_assoc]
    have hdiv : A / (((k+N:ℕ):ℝ)+1) ≤ alpha := by
      apply (div_le_iff₀ (by positivity)).mpr
      exact h.trans (mul_le_mul_of_nonneg_left (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
        alpha_pos.le)
    exact mul_le_mul ih hdiv (div_nonneg hA (by positivity))
      (mul_nonneg (expTerm_nonneg hA _) (pow_nonneg alpha_pos.le _))

private theorem exp_tail_bound {A : ℝ} (hA : 0 ≤ A) {N : ℕ} (h : A ≤ alpha*(N:ℝ)) :
    Real.exp A - ∑ j ∈ range N, expTerm A j ≤ expTerm A N/(1-alpha) := by
  have hf : Summable (expTerm A) := Real.summable_pow_div_factorial A
  have he : (∑' n, expTerm A n) = Real.exp A := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    rfl
  have hh := hf.sum_add_tsum_nat_add N
  have hleft : Real.exp A - ∑ j ∈ range N, expTerm A j = ∑' k, expTerm A (k+N) := by
    rw [← he,← hh]
    ring
  rw [hleft]
  have hsm := ((summable_geometric_of_lt_one alpha_pos.le alpha_lt_one).mul_left (expTerm A N))
  calc
    _ ≤ ∑' k, expTerm A N * alpha^k :=
      ((summable_nat_add_iff N).mpr hf).tsum_le_tsum (fun k => tail_term_le hA h k) hsm
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one alpha_pos.le alpha_lt_one,div_eq_mul_inv]

end

end PowerSumLower973

namespace PowerSumLower973

noncomputable section

private theorem error_pow_le (N : ℕ) {ε : ℝ} (he : 0 ≤ ε) (h : (N:ℝ)*ε ≤ 1) :
    (1+ε)^N-1 ≤ 2*(N:ℝ)*ε := by
  have hPos : 0 ≤ (N:ℝ)*ε := by positivity
  have hAbs : |(N:ℝ)*ε| ≤ 1 := by rwa [abs_of_nonneg hPos]
  have he' := (le_abs_self _).trans (Real.abs_exp_sub_one_le hAbs)
  rw [abs_of_nonneg hPos] at he'
  have hpow : (1+ε)^N ≤ Real.exp ((N:ℝ)*ε) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp ε) _
  linarith

private theorem exp_weighted_mono (n : ℕ) :
    MonotoneOn (fun x : ℝ => Real.exp (-x)*x^(n+1)) (Set.Icc 0 (n:ℝ)) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hzero | hxpos
  · subst x
    simpa using (mul_nonneg (Real.exp_nonneg (-y)) (pow_nonneg hy.1 (n+1)))
  · have hypos := hxpos.trans_le hxy
    have hN : 0 ≤ ((n+1:ℕ):ℝ) := by positivity
    have hfactor : 1 ≤ ((n+1:ℕ):ℝ)/y := (one_le_div hypos).mpr (by push_cast; linarith [hy.2])
    have hlog : ((n+1:ℕ):ℝ)*Real.log (x/y) ≤ x-y := calc
      _ ≤ ((n+1:ℕ):ℝ)*(x/y-1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hxpos hypos)) hN
      _ = (((n+1:ℕ):ℝ)/y)*(x-y) := by field_simp [hypos.ne']
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonpos_right hfactor (sub_nonpos.mpr hxy)
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_nat_mul,Real.exp_log (div_pos hxpos hypos),div_pow,Real.exp_sub] at he
    have hh := (div_le_div_iff₀ (pow_pos hypos (n+1)) (Real.exp_pos y)).mp he
    have hh' : x^(n+1)/Real.exp x ≤ y^(n+1)/Real.exp y :=
      (div_le_div_iff₀ (Real.exp_pos x) (Real.exp_pos y)).mpr (by simpa only [mul_comm] using hh)
    simpa only [Real.exp_neg,div_eq_mul_inv,mul_comm] using hh'

private theorem mainExponent {n : ℕ} (hn : 0 < n) {A : ℝ}
    (hlo : alpha*(n:ℝ) ≤ A) (hhi : A ≤ n) :
    alpha/(12*(n:ℝ))*mainBase^n ≤ Real.exp (-A)*expTerm A (n+1) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hF : 0 < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hk : ((alpha*Real.exp 1)^n)/(6*(n:ℝ)) ≤ expTerm (alpha*(n:ℝ)) n := by
    unfold expTerm
    apply (div_le_div_iff₀ (by positivity) hF).mpr
    calc
      _ ≤ (alpha*Real.exp 1)^n*(6*(n:ℝ)*((n:ℝ)/Real.exp 1)^n) :=
        mul_le_mul_of_nonneg_left (factorial_upper hn) (by positivity [alpha_pos])
      _ = _ := by
        rw [show (alpha*Real.exp 1)^n*(6*(n:ℝ)*((n:ℝ)/Real.exp 1)^n) =
          6*(n:ℝ)*((alpha*Real.exp 1)^n*((n:ℝ)/Real.exp 1)^n) by ring,← mul_pow]
        have hp : (alpha*Real.exp 1)*((n:ℝ)/Real.exp 1) = alpha*(n:ℝ) := by
          field_simp [Real.exp_ne_zero]
        rw [hp,mul_comm]
  have hRatio : alpha/2 ≤ (alpha*(n:ℝ))/((n:ℝ)+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [mul_nonneg alpha_pos.le (sub_nonneg.mpr hn1)]
  have hLower : alpha/(12*(n:ℝ))*(alpha*Real.exp 1)^n ≤
      expTerm (alpha*(n:ℝ)) (n+1) := calc
    _ = (((alpha*Real.exp 1)^n)/(6*(n:ℝ)))*(alpha/2) := by ring
    _ ≤ expTerm (alpha*(n:ℝ)) n * (alpha*(n:ℝ)/((n:ℝ)+1)) :=
      mul_le_mul hk hRatio (by positivity [alpha_pos]) (expTerm_nonneg (by positivity [alpha_pos]) _)
    _ = _ := (expTerm_succ _ _).symm
  have hrewrite :
      mainBase = Real.exp (-alpha)*(alpha*Real.exp 1) := by
    rw [mainBase,mul_left_comm,← Real.exp_add]
    congr 2
    ring
  have hMon := exp_weighted_mono n
    (show alpha*(n:ℝ) ∈ Set.Icc 0 (n:ℝ) from
      ⟨by positivity [alpha_pos],by simpa only [one_mul] using mul_le_mul_of_nonneg_right alpha_lt_one.le hnR.le⟩)
    (show A ∈ Set.Icc 0 (n:ℝ) from ⟨(by positivity [alpha_pos] : 0 ≤ alpha*(n:ℝ)).trans hlo,hhi⟩)
    hlo
  calc
    _ = Real.exp (- (alpha*(n:ℝ)))*(alpha/(12*(n:ℝ))*(alpha*Real.exp 1)^n) := by
      rw [hrewrite,mul_pow,show -(alpha*(n:ℝ))=(n:ℝ)*(-alpha) by ring,Real.exp_nat_mul]
      ring
    _ ≤ Real.exp (-(alpha*(n:ℝ)))*expTerm (alpha*(n:ℝ)) (n+1) :=
      mul_le_mul_of_nonneg_left hLower (Real.exp_nonneg _)
    _ ≤ _ := by
      simpa only [expTerm, ← mul_div_assoc] using
        div_le_div_of_nonneg_right hMon (by positivity : 0 ≤ (Nat.factorial (n+1):ℝ))

private theorem eventually_small_partial :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℂ, ‖w‖ ≤ alpha*(n:ℝ) →
      Real.exp (-‖w‖)/2 ≤ ‖∑ k ∈ range (n+1), w^k/(k ! : ℂ)‖ := by
  let C := alpha*Real.exp 1/(1-alpha)
  have hT : Tendsto (fun n : ℕ => C*tailBase^n) atTop (𝓝 0) := by
    have h0 : 0 ≤ tailBase := by unfold tailBase; positivity [alpha_pos]
    have hC : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero] using hC.mul (tendsto_pow_atTop_nhds_zero_of_lt_one h0 tailBase_lt_one)
  filter_upwards [hT (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with n hN w hw
  let A := ‖w‖
  let P := ∑ k ∈ range (n+1), w^k/(k ! : ℂ)
  have hA : 0 ≤ A := norm_nonneg _
  have hB : A ≤ alpha*((n+1:ℕ):ℝ) := hw.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast n.le_succ) alpha_pos.le)
  have hpow : expTerm A (n+1) ≤ (alpha*Real.exp 1)^(n+1) := by
    unfold expTerm
    have hF : (0:ℝ) < (Nat.factorial (n+1):ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    refine (div_le_iff₀ hF).mpr ?_
    calc
      _ ≤ (alpha*((n+1:ℕ):ℝ))^(n+1) := pow_le_pow_left₀ hA hB _
      _ = (alpha*Real.exp 1)^(n+1)*((((n+1:ℕ):ℝ)/Real.exp 1)^(n+1)) := by
        rw [← mul_pow]
        congr 1
        field_simp [Real.exp_ne_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_lower (by omega)) (by positivity [alpha_pos])
  have hD : ‖Complex.exp w-P‖ ≤ expTerm A (n+1)/(1-alpha) :=
    (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum w (n+1)).trans (exp_tail_bound hA hB)
  have hDt : Real.exp A * ‖Complex.exp w-P‖ ≤ C*tailBase^n := calc
    _ ≤ Real.exp (alpha*(n:ℝ))*((alpha*Real.exp 1)^(n+1)/(1-alpha)) :=
      mul_le_mul (Real.exp_le_exp.mpr hw) (hD.trans (div_le_div_of_nonneg_right hpow
        (sub_nonneg.mpr alpha_lt_one.le))) (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      have he : tailBase = Real.exp alpha*(alpha*Real.exp 1) := by rw [tailBase,Real.exp_add]; ring
      rw [show alpha*(n:ℝ)=(n:ℝ)*alpha by ring,Real.exp_nat_mul,pow_succ,he,mul_pow]
      unfold C
      ring
  have hTail : ‖Complex.exp w-P‖ ≤ Real.exp (-A)/2 := by
    apply (mul_le_mul_iff_of_pos_left (Real.exp_pos A)).mp
    have ht : Real.exp A*(Real.exp (-A)/2)=1/2 := by rw [← mul_div_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero]
    rw [ht]
    exact hDt.trans (le_of_lt hN)
  have hE : Real.exp (-A) ≤ ‖Complex.exp w‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((neg_abs_le _).trans' (neg_le_neg (Complex.abs_re_le_norm w)))
  have hTriangle := norm_add_le (Complex.exp w-P) P
  rw [sub_add_cancel] at hTriangle
  linarith

end

end PowerSumLower973

namespace PowerSumLower973

noncomputable section

private theorem tendsto_shift_pow_mul_geo (p : ℕ) {q : ℝ} (hq : 0 < q) (h1 : q<1) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*q^n) atTop (𝓝 0) := by
  have hNorm : ‖q‖ < 1 := by simpa only [Real.norm_of_nonneg hq.le] using h1
  have hS := (summable_pow_mul_geometric_of_norm_lt_one p hNorm).tendsto_atTop_zero
  have hShift := hS.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun _ : ℕ => q⁻¹) atTop (𝓝 q⁻¹) := tendsto_const_nhds
  have he (n : ℕ) : q⁻¹ * (((n+1:ℕ):ℝ)^p*q^(n+1)) = ((n:ℝ)+1)^p*q^n := by
    push_cast
    rw [pow_succ]
    rw [show q⁻¹ * (((n:ℝ)+1)^p*(q^n*q)) =
       (q⁻¹*q)*(((n:ℝ)+1)^p*q^n) by ring,inv_mul_cancel₀ hq.ne',one_mul]
  simpa only [Function.comp_apply,mul_zero,he] using hc.mul hShift

private theorem eventually_numerics :
    ∀ᶠ n : ℕ in atTop, ((n:ℝ)+1)*beta^n ≤ 1 ∧
      24*((n:ℝ)+1)^2*(beta/mainBase)^n < alpha ∧
      4*((n:ℝ)+1)^2*(beta*Real.exp (2*alpha))^n < 1 := by
  have hMain : 0 < mainBase := beta_pos.trans beta_lt_mainBase
  have q1 : beta/mainBase < 1 := (div_lt_one₀ hMain).mpr beta_lt_mainBase
  have q2 : 0 < beta*Real.exp (2*alpha) := mul_pos beta_pos (Real.exp_pos _)
  have hA := tendsto_shift_pow_mul_geo 1 beta_pos beta_lt_one
  have hB0 := tendsto_shift_pow_mul_geo 2 (div_pos beta_pos hMain) q1
  have hC0 := tendsto_shift_pow_mul_geo 2 q2 beta_mul_exp_lt_one
  have hB : Tendsto (fun n : ℕ => 24*((n:ℝ)+1)^2*(beta/mainBase)^n) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (24:ℝ)) atTop (𝓝 24) := tendsto_const_nhds
    simpa only [←mul_assoc,mul_zero] using hc.mul hB0
  have hC : Tendsto (fun n : ℕ => 4*((n:ℝ)+1)^2*(beta*Real.exp (2*alpha))^n) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (4:ℝ)) atTop (𝓝 4) := tendsto_const_nhds
    simpa only [←mul_assoc,mul_zero] using hc.mul hC0
  filter_upwards [hA (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),hB (Iio_mem_nhds alpha_pos),
    hC (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with n h₁ h₂ h₃
  have hh₁ : ((n:ℝ)+1)^1*beta^n < 1 := h₁
  exact ⟨by simpa only [pow_one] using hh₁.le,h₂,h₃⟩

/-- At the chosen exponential threshold, the first missing coefficient and the value at 1
cannot both be compatible with the perturbed exponential series. -/
theorem eventually_no_small_certificate :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℂ, ‖w‖ ≤ n →
      ‖w‖^(n+1)/(Nat.factorial (n+1):ℝ) ≤ Real.exp ‖w‖*((1+beta^n)^(n+1)-1) →
      ‖∑ k ∈ range (n+1), w^k/(k ! : ℂ)‖ ≤
        ((n+1:ℕ):ℝ)*(Real.exp ‖w‖*((1+beta^n)^(n+1)-1)) →
      False := by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_small_partial,eventually_numerics]
    with n hn hPartial hNum w hw hcoef hsum
  let A := ‖w‖
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hE := error_pow_le (n+1) (pow_nonneg beta_pos.le n)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hNum.1)
  have hC : expTerm A (n+1) ≤ Real.exp A*(2*((n:ℝ)+1)*beta^n) :=
    hcoef.trans (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using hE)
      (Real.exp_nonneg _))
  by_cases hlarge : alpha*(n:ℝ) ≤ A
  · have h := mul_le_mul_of_nonneg_left hC (Real.exp_nonneg (-A))
    have hOne : Real.exp (-A)*Real.exp A = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    rw [← mul_assoc,hOne,one_mul] at h
    have hComp : alpha/(12*(n:ℝ))*mainBase^n ≤ 2*((n:ℝ)+1)*beta^n :=
      (mainExponent hn hlarge hw).trans h
    rw [div_mul_eq_mul_div] at hComp
    have h₁ := (div_le_iff₀ (by positivity : 0 < 12*(n:ℝ))).mp hComp
    have hm : 0 < mainBase := beta_pos.trans beta_lt_mainBase
    have h₂ := (le_div_iff₀ (pow_pos hm n)).mpr h₁
    have h₃ : alpha ≤ 24*(n:ℝ)*((n:ℝ)+1)*(beta/mainBase)^n := by
      calc
        _ ≤ _ := h₂
        _ = _ := by rw [div_pow]; ring
    have h₄ : 24*(n:ℝ)*((n:ℝ)+1)*(beta/mainBase)^n ≤
        24*((n:ℝ)+1)^2*(beta/mainBase)^n := by
      have hp : 0 ≤ (beta/mainBase)^n := pow_nonneg (div_nonneg beta_pos.le hm.le) _
      have hx : (n:ℝ)*((n:ℝ)+1) ≤ ((n:ℝ)+1)^2 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      calc
        _ = (24*((n:ℝ)*((n:ℝ)+1)))*(beta/mainBase)^n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by norm_num)) hp
    exact (not_lt_of_ge (h₃.trans h₄)) hNum.2.1
  · have hsmall : A ≤ alpha*(n:ℝ) := le_of_not_ge hlarge
    have hLow := hPartial w hsmall
    have hHigh := hsum.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE
      (Real.exp_nonneg A)) (by positivity))
    have hMul := mul_le_mul_of_nonneg_left (hLow.trans hHigh) (by positivity : 0 ≤ 2*Real.exp A)
    have hOne : 2*Real.exp A*(Real.exp (-A)/2)=1 := by
      rw [← mul_div_assoc, mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
      norm_num
    rw [hOne] at hMul
    have hExp : Real.exp (2*A) ≤ (Real.exp (2*alpha))^n := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left hsmall
        (by norm_num : (0:ℝ) ≤ 2)
    have h₁ : 1 ≤ 4*((n:ℝ)+1)^2*beta^n*Real.exp (2*A) := by
      calc
        _ ≤ _ := hMul
        _ = _ := by
          push_cast
          rw [show 2*A=A+A by ring,Real.exp_add]
          ring
    have h₂ : 4*((n:ℝ)+1)^2*beta^n*Real.exp (2*A) ≤
        4*((n:ℝ)+1)^2*(beta*Real.exp (2*alpha))^n := by
      rw [mul_pow,← mul_assoc]
      exact mul_le_mul_of_nonneg_left hExp (by positivity [beta_pos])
    exact (not_lt_of_ge (h₁.trans h₂)) hNum.2.2

end

end PowerSumLower973

namespace PowerSumLower973

noncomputable section

theorem eventually_tuple_lower :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℕ→ℂ,
      (∀ j ∈ Icc 1 n, ‖z j‖≤1) → (∃ j ∈ Icc 1 n, ‖z j‖=1) →
      ∃ k ∈ Icc 2 (n+1), beta^n < ‖∑ j ∈ Icc 1 n, z j^k‖ := by
  filter_upwards [eventually_no_small_certificate] with n hn z hNorm hRoot
  by_contra! hsmall
  let s : Finset ℕ := Icc 1 n
  have hs : s.card = n := by simp [s,Nat.card_Icc]
  obtain ⟨i,hi,hunit⟩ := hRoot
  have hi₀ : z i ≠ 0 := by intro he; rw [he,norm_zero] at hunit; norm_num at hunit
  let u (j : ℕ) := (z i)⁻¹*z j
  have hu₁ : u i=1 := inv_mul_cancel₀ hi₀
  have huNorm (j : ℕ) : ‖u j‖=‖z j‖ := by simp only [u,norm_mul,norm_inv,hunit,inv_one,one_mul]
  have hrot (k : ℕ) : ‖psum s u k‖=‖psum s z k‖ := by
    unfold psum
    simp_rw [u,mul_pow]
    rw [← Finset.mul_sum,norm_mul,norm_pow,norm_inv,hunit,inv_one,one_pow,one_mul]
  have hA : ‖psum s u 1‖ ≤ n := calc
    _ ≤ ∑ j ∈ s, ‖u j^1‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, 1 := by
      refine Finset.sum_le_sum fun j hj => ?_
      simpa only [pow_one,huNorm] using hNorm j hj
    _ = _ := by simp [hs]
  have hUsed (k : ℕ) (hk : k ∈ Icc 2 (s.card+1)) : ‖psum s u k‖ ≤ beta^n := by
    rw [hrot]
    exact hsmall k (by simpa only [hs] using hk)
  obtain ⟨hc,hp⟩ := lower_certificate s u (pow_nonneg beta_pos.le n) ⟨i,hi,hu₁⟩ hUsed
  exact hn (-psum s u 1) (by simpa only [norm_neg] using hA)
    (by simpa only [norm_neg,hs] using hc) (by simpa only [norm_neg,hs] using hp)

theorem eventually_lower_glb :
    ∀ᶠ n : ℕ in atTop, ∀ M₂ : ℝ,
      IsGLB { M | ∃ z : ℕ → ℂ,
        (∀ j ∈ Icc 1 n, ‖z j‖ ≤ 1) ∧
        (∃ j ∈ Icc 1 n, ‖z j‖ = 1) ∧
        (∃ k ∈ Icc 2 (n + 1), M = ‖∑ j ∈ Icc 1 n, z j ^ k‖ ∧
          ∀ m ∈ Icc 2 (n + 1), ‖∑ j ∈ Icc 1 n, z j ^ m‖ ≤ M) } M₂ →
      (1.746 : ℝ) ^ (-(n : ℝ)) < M₂ := by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_tuple_lower] with n hn htuple M₂ hM
  have h₁ : (1.746:ℝ)^(-(n:ℝ)) = ((1.746:ℝ)⁻¹)^n := by
    rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,inv_pow]
  have h₂ : ((1.746:ℝ)⁻¹)^n < beta^n := pow_lt_pow_left₀ inv_bound_lt_beta (by norm_num) hn.ne'
  rw [h₁]
  apply h₂.trans_le
  apply hM.2
  rintro M ⟨z,hN,hU,k,hk,hkM,hMmax⟩
  obtain ⟨j,hj,hjL⟩ := htuple z hN hU
  exact (hjL.trans_le (hMmax j hj)).le

end

end PowerSumLower973

open Finset Polynomial

namespace Erdos973Upper

noncomputable def elementary {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k * ((univ : Finset (Fin n)).val.map z).esymm k

noncomputable def powerSum {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ i, z i ^ k

theorem newton {n : ℕ} (z : Fin n → ℂ) {k : ℕ} (hk : 0 < k) :
    powerSum z k = -(k : ℂ) * elementary z k -
      ∑ a ∈ (antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
        elementary z a.1 * powerSum z a.2 := by
  classical
  have h := congrArg (MvPolynomial.eval z)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k hk)
  simp only [powerSum, elementary, Finset.esymm_map_val]
  simpa [MvPolynomial.psum, MvPolynomial.esymm,
    pow_succ (-1 : ℂ) k, mul_assoc, mul_left_comm, mul_comm] using h

theorem powerSums_of_coefficients {n : ℕ} (z : Fin n → ℂ) (b s : ℕ → ℂ)
    (hb : ∀ k ≤ n + 1, elementary z k = b k)
    (hs : ∀ k, 0 < k → k ≤ n + 1 → s k = -(k : ℂ) * b k -
      ∑ a ∈ (antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k), b a.1 * s a.2) :
    ∀ k, 0 < k → k ≤ n + 1 → powerSum z k = s k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hpos hle
    rw [newton z hpos, hs k hpos hle, hb k hle]
    congr 1
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨hsum, hfst⟩ := Finset.mem_filter.mp ha
    have hadd := HasAntidiagonal.mem_antidiagonal.mp hsum
    have ha0 : 0 < a.1 := hfst.1
    have hal : a.1 < k := hfst.2
    rw [hb a.1 (by omega), ih a.2 (by omega) (by omega) (by omega)]

theorem tuple_of_coefficients (n : ℕ) (b : ℕ → ℂ) (hzero : b 0 = 1)
    (hsum : ∑ k ∈ range (n + 1), b k = 0) :
    ∃ z : Fin n → ℂ, (∃ j, z j = 1) ∧ ∀ k ≤ n, elementary z k = b k := by
  classical
  let p : ℂ[X] := ∑ j ∈ range (n + 1), monomial (n - j) (b j)
  have hcoeff (k : ℕ) (hk : k ≤ n) : p.coeff (n - k) = b k := by
    simp only [p, finsetSum_coeff]
    rw [sum_eq_single k]
    · simp
    · intro a ha hak
      rw [coeff_monomial, if_neg]
      have := mem_range.mp ha
      omega
    · simp [mem_range, hk]
  have hcn : p.coeff n = 1 := by simpa [hzero] using hcoeff 0 (Nat.zero_le n)
  have hdeg_le : p.natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (natDegree_monomial_le _).trans (Nat.sub_le n j)
  have hdeg : p.natDegree = n :=
    le_antisymm hdeg_le (le_natDegree_of_ne_zero (by rw [hcn]; exact one_ne_zero))
  have hmonic := monic_of_natDegree_le_of_coeff_eq_one n hdeg_le hcn
  have hsplit := IsAlgClosed.splits p
  let l := p.roots.toList
  have hcard : l.length = n := by
    rw [Multiset.length_toList, ← hsplit.natDegree_eq_card_roots, hdeg]
  let z : Fin n → ℂ := fun j => l.get (j.cast hcard.symm)
  have hz : List.ofFn z = l := by
    apply List.ext_getElem
    · simp [hcard]
    · intro i hi hil
      simp [z]
  have hmap : (univ : Finset (Fin n)).val.map z = p.roots := by
    rw [Fin.univ_val_map, hz, Multiset.coe_toList]
  refine ⟨z, ?_, fun k hk => ?_⟩
  · have heval : p.eval 1 = 0 := by
      simpa [p, eval_finsetSum] using hsum
    have hmem := (mem_roots hmonic.ne_zero).mpr heval
    rw [← hmap] at hmem
    rcases Multiset.mem_map.mp hmem with ⟨j, -, hj⟩
    exact ⟨j, hj⟩
  · have hcv := coeff_eq_esymm_roots_of_splits hsplit (k := n - k) (by omega)
    rw [hmonic.leadingCoeff, one_mul, hdeg, Nat.sub_sub_self hk, hcoeff k hk] at hcv
    rw [elementary, hmap, hcv]

theorem newton_of_derivative (f spectrum : PowerSeries ℂ)
    (hzero : PowerSeries.coeff 0 f = 1)
    (N : ℕ)
    (hderiv : ∀ k < N,
      PowerSeries.coeff k (PowerSeries.derivative ℂ f) =
        -PowerSeries.coeff k (f * spectrum)) :
    ∀ k, 0 < k → k ≤ N →
      PowerSeries.coeff (k - 1) spectrum = -(k : ℂ) * PowerSeries.coeff k f -
        ∑ a ∈ (antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
          PowerSeries.coeff a.1 f * PowerSeries.coeff (a.2 - 1) spectrum := by
  intro k hk hle
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have h := hderiv m (by omega)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
  have hfilter :
      (∑ a ∈ (antidiagonal (m + 1)).filter (fun a => a.1 ∈ Set.Ioo 0 (m + 1)),
        PowerSeries.coeff a.1 f * PowerSeries.coeff (a.2 - 1) spectrum) =
      ∑ a ∈ (antidiagonal m).filter (fun a => 0 < a.1),
        PowerSeries.coeff a.1 f * PowerSeries.coeff a.2 spectrum := by
    refine sum_bij (fun a _ => (a.1, a.2 - 1)) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha, hfst⟩ := mem_filter.mp ha
      have heq := HasAntidiagonal.mem_antidiagonal.mp ha
      have hlt : a.1 < m + 1 := hfst.2
      exact mem_filter.mpr ⟨HasAntidiagonal.mem_antidiagonal.mpr (by simp; omega), hfst.1⟩
    · intro a ha b hb hab
      have hea := HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp ha).1
      have heb := HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp hb).1
      have hfst := congrArg Prod.fst hab
      exact Prod.ext hfst (by omega)
    · intro b hb
      obtain ⟨hb, hfst⟩ := mem_filter.mp hb
      have heq := HasAntidiagonal.mem_antidiagonal.mp hb
      refine ⟨(b.1, b.2 + 1), mem_filter.mpr ⟨?_, ?_⟩, by simp⟩
      · exact HasAntidiagonal.mem_antidiagonal.mpr (by simp; omega)
      · exact ⟨hfst, by simp; omega⟩
    · intros
      rfl
  have hrest : (antidiagonal m).filter (fun a : ℕ × ℕ => ¬ 0 < a.1) = {(0, m)} := by
    ext a
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, mem_singleton, not_lt, Nat.le_zero]
    constructor
    · rintro ⟨hs, h0⟩
      exact Prod.ext h0 (by omega)
    · rintro rfl
      simp
  rw [hfilter]
  have hsum := sum_filter_add_sum_filter_not (antidiagonal m) (fun a => 0 < a.1)
    (fun a => PowerSeries.coeff a.1 f * PowerSeries.coeff a.2 spectrum)
  rw [hrest, sum_singleton, hzero, one_mul] at hsum
  rw [← hsum] at h
  push_cast at h ⊢
  linear_combination h

theorem normalized_tuple {n : ℕ} (z : Fin n → ℂ) (hone : ∃ j, z j = 1) (B : ℝ)
    (hB : ∀ k ∈ Icc 2 (n + 1), ‖powerSum z k‖ < B) :
    ∃ w : ℕ → ℂ,
      (∀ j ∈ Icc 1 n, ‖w j‖ ≤ 1) ∧ (∃ j ∈ Icc 1 n, ‖w j‖ = 1) ∧
      ∀ k ∈ Icc 2 (n + 1), ‖∑ j ∈ Icc 1 n, w j ^ k‖ < B := by
  classical
  obtain ⟨i, hi⟩ := hone
  obtain ⟨p, -, hp⟩ := exists_max_image (univ : Finset (Fin n)) (fun j => ‖z j‖)
    ⟨i, mem_univ i⟩
  have hpmax : ∀ j, ‖z j‖ ≤ ‖z p‖ := fun j => hp j (mem_univ j)
  have hpone : 1 ≤ ‖z p‖ := by simpa [hi] using hpmax i
  have hp0 : z p ≠ 0 := by
    intro h
    simp [h] at hpone
    linarith
  have hindex (j : ℕ) (hj : j ∈ Icc 1 n) : j - 1 < n := by
    have := mem_Icc.mp hj
    omega
  let w (j : ℕ) : ℂ := if hj : j ∈ Icc 1 n then z ⟨j - 1, hindex j hj⟩ / z p else 0
  have hw (j : Fin n) : w (j.val + 1) = z j / z p := by
    have hj : j.val + 1 ∈ Icc 1 n := mem_Icc.mpr ⟨by omega, by omega⟩
    simp [w]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j hj
    simp only [w, dif_pos hj, norm_div, div_le_one₀ (norm_pos_iff.mpr hp0)]
    exact hpmax _
  · exact ⟨p.val + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by simp [hw, hp0]⟩
  · intro k hk
    have hsum :
        ∑ j ∈ Icc 1 n, w j ^ k = ∑ j : Fin n, (z j / z p) ^ k := by
      symm
      refine sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
      · intro j _
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j _ l _ h
        exact Fin.ext (by omega)
      · intro j hj
        refine ⟨⟨j - 1, hindex j hj⟩, mem_univ _, ?_⟩
        change j - 1 + 1 = j
        have := mem_Icc.mp hj
        omega
      · intro j _
        rw [hw]
    rw [hsum]
    simp only [div_pow, ← sum_div, norm_div, norm_pow]
    change ‖powerSum z k‖ / ‖z p‖ ^ k < B
    refine lt_of_le_of_lt ?_ (hB k hk)
    exact div_le_self (norm_nonneg _) (one_le_pow₀ hpone)

section Perturbation

open PowerSeries

noncomputable def taylor (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale (-a) (PowerSeries.exp ℂ)

theorem coeff_taylor (a : ℂ) (j : ℕ) :
    PowerSeries.coeff j (taylor a) = (-a) ^ j / j.factorial := by
  simp [taylor, PowerSeries.coeff_rescale, div_eq_mul_inv]

theorem derivative_taylor (a : ℂ) :
    PowerSeries.derivative ℂ (taylor a) = PowerSeries.C (-a) * taylor a := by
  ext j
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, coeff_taylor, coeff_taylor,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  have h1 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  have h2 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  field_simp

theorem perturbation_derivative (N k : ℕ) (hk : 0 < k) (hN : N ≤ k + (k - 1))
    (a : ℂ) (v : PowerSeries ℂ) :
    let P := (PowerSeries.X : PowerSeries ℂ) ^ k * v
    let f := taylor a * (1 - P)
    let s := PowerSeries.C a + PowerSeries.derivative ℂ P
    ∀ j < N, PowerSeries.coeff j (PowerSeries.derivative ℂ f) =
      -PowerSeries.coeff j (f * s) := by
  intro P f s j hj
  have hprod :
      PowerSeries.derivative ℂ f + f * s =
        -(taylor a * P * PowerSeries.derivative ℂ P) := by
    dsimp only [f, s]
    simp only [Derivation.leibniz, smul_eq_mul, derivative_taylor, map_sub,
      PowerSeries.derivative_one, zero_sub, map_neg]
    ring
  have hp : PowerSeries.derivative ℂ P =
      PowerSeries.X ^ (k - 1) *
        ((k : PowerSeries ℂ) * v + PowerSeries.X * PowerSeries.derivative ℂ v) := by
    dsimp only [P]
    simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, mul_one]
    have he : (PowerSeries.X : PowerSeries ℂ) ^ k =
        PowerSeries.X ^ (k - 1) * PowerSeries.X := by
      rw [← pow_succ]
      congr 1
      omega
    conv_lhs => rw [he]
    ring
  have hvanish : PowerSeries.coeff j (taylor a * P * PowerSeries.derivative ℂ P) = 0 := by
    rw [hp]
    dsimp only [P]
    have hf :
        taylor a * (PowerSeries.X ^ k * v) *
            (PowerSeries.X ^ (k - 1) *
              ((k : PowerSeries ℂ) * v + PowerSeries.X * PowerSeries.derivative ℂ v)) =
          PowerSeries.X ^ (k + (k - 1)) *
            (taylor a * v * ((k : PowerSeries ℂ) * v +
              PowerSeries.X * PowerSeries.derivative ℂ v)) := by
      rw [pow_add]
      ring
    rw [hf, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have he := congrArg (PowerSeries.coeff j) hprod
  rw [map_add, map_neg, hvanish, neg_zero] at he
  exact eq_neg_of_add_eq_zero_left he

end Perturbation

theorem upper_bound_of_series (n : ℕ) (hn : 1 ≤ n) (f spectrum : PowerSeries ℂ)
    (hzero : PowerSeries.coeff 0 f = 1)
    (hhigh : PowerSeries.coeff (n + 1) f = 0)
    (hsum : ∑ k ∈ range (n + 1), PowerSeries.coeff k f = 0)
    (hderiv : ∀ k < n + 1,
      PowerSeries.coeff k (PowerSeries.derivative ℂ f) =
        -PowerSeries.coeff k (f * spectrum))
    (B : ℝ) (hsmall : ∀ k ∈ Icc 2 (n + 1), ‖PowerSeries.coeff (k - 1) spectrum‖ < B)
    (M₂ : ℝ)
    (hglb : IsGLB { M | ∃ z : ℕ → ℂ,
      (∀ j ∈ Icc 1 n, ‖z j‖ ≤ 1) ∧
      (∃ j ∈ Icc 1 n, ‖z j‖ = 1) ∧
      (∃ k ∈ Icc 2 (n + 1), M = ‖∑ j ∈ Icc 1 n, z j ^ k‖ ∧
        ∀ m ∈ Icc 2 (n + 1), ‖∑ j ∈ Icc 1 n, z j ^ m‖ ≤ M) } M₂) :
    M₂ < B := by
  classical
  obtain ⟨z, hroot, hcoeff⟩ := tuple_of_coefficients n (fun k => PowerSeries.coeff k f)
    hzero hsum
  have hcoeff' : ∀ k ≤ n + 1, elementary z k = PowerSeries.coeff k f := by
    intro k hk
    obtain hl | rfl : k ≤ n ∨ k = n + 1 := by omega
    · exact hcoeff k hl
    · have hempty : (univ : Finset (Fin n)).powersetCard (n + 1) = ∅ :=
        powersetCard_eq_empty.mpr (by simp)
      rw [hhigh, elementary, esymm_map_val, hempty, sum_empty, mul_zero]
  have hps := powerSums_of_coefficients z (fun k => PowerSeries.coeff k f)
    (fun k => PowerSeries.coeff (k - 1) spectrum) hcoeff'
    (newton_of_derivative f spectrum hzero (n + 1) hderiv)
  obtain ⟨w, hnorm, hmax, hw⟩ := normalized_tuple z hroot B (by
    intro k hk
    have hkm := mem_Icc.mp hk
    rw [hps k (by omega) hkm.2]
    exact hsmall k hk)
  obtain ⟨k, hk, hkm⟩ := exists_max_image (Icc 2 (n + 1))
    (fun k => ‖∑ j ∈ Icc 1 n, w j ^ k‖) ⟨2, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hmem : ‖∑ j ∈ Icc 1 n, w j ^ k‖ ∈ { M | ∃ z : ℕ → ℂ,
      (∀ j ∈ Icc 1 n, ‖z j‖ ≤ 1) ∧
      (∃ j ∈ Icc 1 n, ‖z j‖ = 1) ∧
      (∃ k ∈ Icc 2 (n + 1), M = ‖∑ j ∈ Icc 1 n, z j ^ k‖ ∧
        ∀ m ∈ Icc 2 (n + 1), ‖∑ j ∈ Icc 1 n, z j ^ m‖ ≤ M) } :=
    ⟨w, hnorm, hmax, k, hk, rfl, hkm⟩
  exact lt_of_le_of_lt (hglb.1 hmem) (hw k hk)

section TwoTerms

open PowerSeries

noncomputable def perturb (k : ℕ) (t u : ℂ) : PowerSeries ℂ :=
  PowerSeries.X ^ k * (PowerSeries.C t + PowerSeries.C u * PowerSeries.X)

noncomputable def candidate (a : ℂ) (k : ℕ) (t u : ℂ) : PowerSeries ℂ :=
  taylor a * (1 - perturb k t u)

theorem coeff_perturb (k : ℕ) (t u : ℂ) (j : ℕ) :
    PowerSeries.coeff j (perturb k t u) =
      (if j = k then t else 0) + (if j = k + 1 then u else 0) := by
  have h : perturb k t u = PowerSeries.C t * PowerSeries.X ^ k +
      PowerSeries.C u * PowerSeries.X ^ (k + 1) := by
    rw [perturb, pow_succ]
    ring
  rw [h, map_add, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul_X_pow]

theorem coeff_candidate (a : ℂ) (k : ℕ) (t u : ℂ) (j : ℕ) :
    PowerSeries.coeff j (candidate a k t u) = PowerSeries.coeff j (taylor a) -
      t * (if k ≤ j then PowerSeries.coeff (j - k) (taylor a) else 0) -
      u * (if k + 1 ≤ j then PowerSeries.coeff (j - (k + 1)) (taylor a) else 0) := by
  have h : candidate a k t u = taylor a -
      PowerSeries.C t * (PowerSeries.X ^ k * taylor a) -
      PowerSeries.C u * (PowerSeries.X ^ (k + 1) * taylor a) := by
    rw [candidate, perturb, pow_succ]
    ring
  rw [h, map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']

private theorem sum_shift (g : ℕ → ℂ) (n k : ℕ) :
    (∑ j ∈ range (n + 1), if k ≤ j then g (j - k) else 0) =
      ∑ j ∈ range (n + 1 - k), g j := by
  rw [← sum_filter]
  refine sum_bij (fun j _ => j - k) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj, hjk⟩ := mem_filter.mp hj
    exact mem_range.mpr (by have := mem_range.mp hj; omega)
  · intro j hj l hl h
    have hjk := (mem_filter.mp hj).2
    have hlk := (mem_filter.mp hl).2
    omega
  · intro j hj
    have h := mem_range.mp hj
    exact ⟨k + j, mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩, by omega⟩
  · intros
    rfl

theorem sum_candidate (a : ℂ) (n k : ℕ) (t u : ℂ) :
    (∑ j ∈ range (n + 1), PowerSeries.coeff j (candidate a k t u)) =
      (∑ j ∈ range (n + 1), PowerSeries.coeff j (taylor a)) -
      t * (∑ j ∈ range (n + 1 - k), PowerSeries.coeff j (taylor a)) -
      u * (∑ j ∈ range (n - k), PowerSeries.coeff j (taylor a)) := by
  simp_rw [coeff_candidate]
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [sum_shift (fun j => PowerSeries.coeff j (taylor a)) n k,
    sum_shift (fun j => PowerSeries.coeff j (taylor a)) n (k + 1)]
  have hidx : n + 1 - (k + 1) = n - k := by omega
  rw [hidx]

theorem coeff_spectrum_of_two_terms (a t u : ℂ) (j k : ℕ) (hj : 2 ≤ j) :
    PowerSeries.coeff (j - 1) (PowerSeries.C a + PowerSeries.derivative ℂ (perturb k t u)) =
      ((if j = k then t else 0) + (if j = k + 1 then u else 0)) * (j : ℂ) := by
  rw [map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add,
    PowerSeries.coeff_derivative, Nat.sub_add_cancel (by omega), coeff_perturb]
  have h : ((j - 1 : ℕ) : ℂ) + 1 = (j : ℂ) := by
    rw [← Nat.cast_one (R := ℂ), ← Nat.cast_add, Nat.sub_add_cancel (by omega)]
  rw [h]

theorem coeff_spectrum_small (a t u : ℂ) (k j : ℕ) (hj : 2 ≤ j) {B : ℝ}
    (hB : 0 < B) (ht : (k : ℝ) * ‖t‖ < B) (hu : ((k : ℝ) + 1) * ‖u‖ < B) :
    ‖PowerSeries.coeff (j - 1) (PowerSeries.C a + PowerSeries.derivative ℂ (perturb k t u))‖ < B := by
  rw [coeff_spectrum_of_two_terms a t u j k hj]
  split_ifs with h₁ h₂ h₂
  · omega
  · subst j
    simpa [norm_mul, mul_comm] using ht
  · subst j
    rw [zero_add, norm_mul, Complex.norm_natCast, Nat.cast_add, Nat.cast_one, mul_comm]
    exact hu
  · simpa using hB

theorem upper_bound_of_two_terms (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hsize : n + 1 ≤ k + (k - 1)) (a t u : ℂ) (B : ℝ)
    (hB : 0 < B) (ht : (k : ℝ) * ‖t‖ < B) (hu : ((k : ℝ) + 1) * ‖u‖ < B)
    (hhigh : PowerSeries.coeff (n + 1) (taylor a) =
      t * PowerSeries.coeff (n + 1 - k) (taylor a) +
      u * PowerSeries.coeff (n - k) (taylor a))
    (hsum : (∑ j ∈ range (n + 1), PowerSeries.coeff j (taylor a)) =
      t * (∑ j ∈ range (n + 1 - k), PowerSeries.coeff j (taylor a)) +
      u * (∑ j ∈ range (n - k), PowerSeries.coeff j (taylor a)))
    (M₂ : ℝ)
    (hglb : IsGLB { M | ∃ z : ℕ → ℂ,
      (∀ j ∈ Icc 1 n, ‖z j‖ ≤ 1) ∧
      (∃ j ∈ Icc 1 n, ‖z j‖ = 1) ∧
      (∃ k ∈ Icc 2 (n + 1), M = ‖∑ j ∈ Icc 1 n, z j ^ k‖ ∧
        ∀ m ∈ Icc 2 (n + 1), ‖∑ j ∈ Icc 1 n, z j ^ m‖ ≤ M) } M₂) :
    M₂ < B := by
  have hkpos : 0 < k := by omega
  refine upper_bound_of_series n hn (candidate a k t u)
    (PowerSeries.C a + PowerSeries.derivative ℂ (perturb k t u))
    ?_ ?_ ?_ ?_ B ?_ M₂ hglb
  · rw [coeff_candidate a k t u 0, if_neg (by omega), if_neg (by omega), coeff_taylor]
    simp
  · have hidx : n + 1 - (k + 1) = n - k := by omega
    rw [coeff_candidate, if_pos (by omega), if_pos (by omega), hidx, hhigh]
    ring
  · rw [sum_candidate, hsum]
    ring
  · exact perturbation_derivative (n + 1) k hkpos hsize a
      (PowerSeries.C t + PowerSeries.C u * PowerSeries.X)
  · intro j hj
    exact coeff_spectrum_small a t u k j (mem_Icc.mp hj).1 hB ht hu

end TwoTerms

end Erdos973Upper

open Finset intervalIntegral

namespace Erdos973Upper

noncomputable def expCoeff (a : ℝ) (j : ℕ) : ℝ := (-a) ^ j / j.factorial

noncomputable def expPartial (a : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), expCoeff a i

noncomputable def moment (a : ℝ) (j : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ j * Real.exp (a * (x - 1))

theorem expCoeff_succ (a : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * expCoeff a (j + 1) = -a * expCoeff a j := by
  rw [expCoeff, expCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  have h₁ : (j : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_rescaled_exp (a x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (a * (x - 1)))
      (a * Real.exp (a * (x - 1))) x := by
  have h := (((hasDerivAt_id x).sub_const (1 : ℝ)).const_mul a).exp
  simpa [mul_comm] using h

private theorem continuous_moment_integrand (a : ℝ) (j : ℕ) :
    Continuous (fun x : ℝ => x ^ j * Real.exp (a * (x - 1))) := by fun_prop

theorem moment_zero (a : ℝ) : a * moment a 0 = 1 - Real.exp (-a) := by
  have hi : IntervalIntegrable (fun x : ℝ => a * Real.exp (a * (x - 1)))
      MeasureTheory.volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable 0 1
  have h := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_rescaled_exp a x) hi
  simpa [moment, ← integral_const_mul] using h

theorem moment_succ (a : ℝ) (j : ℕ) :
    a * moment a (j + 1) = 1 - ((j : ℝ) + 1) * moment a j := by
  have hDeriv (x : ℝ) :
      HasDerivAt (fun x : ℝ => x ^ (j + 1) * Real.exp (a * (x - 1)))
        (((j : ℝ) + 1) * (x ^ j * Real.exp (a * (x - 1))) +
          a * (x ^ (j + 1) * Real.exp (a * (x - 1)))) x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm]
      using (hasDerivAt_pow (j + 1) x).fun_mul (hasDerivAt_rescaled_exp a x)
  have h₁ := ((continuous_moment_integrand a j).const_mul ((j : ℝ) + 1)).intervalIntegrable
    (μ := MeasureTheory.volume) (0 : ℝ) 1
  have h₂ := ((continuous_moment_integrand a (j + 1)).const_mul a).intervalIntegrable
    (μ := MeasureTheory.volume) (0 : ℝ) 1
  have hi := integral_eq_sub_of_hasDerivAt (fun x _ => hDeriv x) (h₁.add h₂)
  rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul] at hi
  simp only [one_pow, sub_self, mul_zero, Real.exp_zero, mul_one, zero_pow (Nat.succ_ne_zero j),
    zero_mul, sub_zero] at hi
  exact eq_sub_of_add_eq (by simpa [moment, add_comm] using hi)

theorem partial_remainder (a : ℝ) (j : ℕ) :
    expPartial a j = Real.exp (-a) - expCoeff a (j + 1) * (((j : ℝ) + 1) * moment a j) := by
  induction j with
  | zero =>
    have hz := moment_zero a
    simp [expPartial, expCoeff] at ⊢
    nlinarith
  | succ j ih =>
    have hr := expCoeff_succ a (j + 1)
    have hm := moment_succ a j
    rw [expPartial, sum_range_succ, ← expPartial, ih]
    linear_combination moment a (j + 1) * hr - expCoeff a (j + 1) * hm

theorem moment_nonneg (a : ℝ) (j : ℕ) : 0 ≤ moment a j := by
  apply integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro x hx
  exact mul_nonneg (pow_nonneg hx.1 _) (Real.exp_nonneg _)

theorem moment_term_le_one {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ((j : ℝ) + 1) * moment a j ≤ 1 := by
  have h := mul_nonneg ha (moment_nonneg a (j + 1))
  rw [moment_succ] at h
  linarith

theorem expPartial_abs_le {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    |expPartial a j| ≤ Real.exp (-a) + |expCoeff a (j + 1)| := by
  rw [partial_remainder]
  rw [sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  have hp : 0 ≤ ((j : ℝ) + 1) * moment a j :=
    mul_nonneg (by positivity) (moment_nonneg a j)
  rw [abs_neg, abs_of_nonneg (Real.exp_nonneg _), abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ Real.exp (-a) + |expCoeff a (j + 1)| * 1 := by gcongr; exact moment_term_le_one ha j
    _ = _ := by rw [mul_one]

theorem moment_gap (m : ℕ) (hm : 1 ≤ m) :
    1 / (64 * (m : ℝ)) ≤ (m : ℝ) * (moment m m - moment m (m + 1)) := by
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  let s : ℝ := 1 - 1 / (2 * (m : ℝ))
  let t : ℝ := 1 - 1 / (4 * (m : ℝ))
  let c : ℝ := 1 / (16 * (m : ℝ))
  let g (x : ℝ) := (1 - x) * x ^ m * Real.exp ((m : ℝ) * (x - 1))
  have hs : 0 ≤ s := by
    dsimp [s]
    have : (1 : ℝ) / (2 * (m : ℝ)) ≤ 1 := (div_le_one₀ (by positivity)).2 (by linarith)
    linarith
  have hst : s ≤ t := by
    dsimp [s, t]
    have : (1 : ℝ) / (4 * (m : ℝ)) ≤ 1 / (2 * (m : ℝ)) := by gcongr; linarith
    linarith
  have ht : t ≤ 1 := sub_le_self _ (by positivity)
  have hc : Continuous g := by
    dsimp [g]
    fun_prop
  have hgi (p q : ℝ) : IntervalIntegrable g MeasureTheory.volume p q :=
    hc.intervalIntegrable p q
  have hn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1.le _))
      (Real.exp_nonneg _)
  have hlower (x : ℝ) (hx : x ∈ Set.Icc s t) : c ≤ g x := by
    have he : -(1 / 2 : ℝ) ≤ (m : ℝ) * (x - 1) := by
      have h := mul_le_mul_of_nonneg_left hx.1 hm0.le
      have heq : (m : ℝ) * s = (m : ℝ) - 1 / 2 := by dsimp [s]; field_simp
      rw [heq] at h
      linarith
    have h₁ : 1 / (4 * (m : ℝ)) ≤ 1 - x := by
      have hx' := hx.2
      dsimp [t] at hx'
      linarith
    have h₂ : (1 / 2 : ℝ) ≤ x ^ m := by
      have h := one_add_mul_sub_le_pow (show -1 ≤ x by linarith [hs.trans hx.1]) m
      linarith
    have h₃ : (1 / 2 : ℝ) ≤ Real.exp ((m : ℝ) * (x - 1)) :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    calc
      c = (1 / (4 * (m : ℝ))) * (1 / 2) * (1 / 2) := by dsimp [c]; ring
      _ ≤ g x := by
        have hx₀ : 0 ≤ 1 - x := sub_nonneg.mpr (hx.2.trans ht)
        have hx₁ : 0 ≤ x := hs.trans hx.1
        dsimp [g]
        gcongr
  have hsmall :
      (∫ _x in s..t, c) ≤ ∫ x in s..t, g x :=
    integral_mono_on hst (intervalIntegrable_const) (hgi s t) hlower
  have hlarge :
      (∫ x in s..t, g x) ≤ ∫ x in (0 : ℝ)..1, g x :=
    integral_mono_interval hs hst ht hn (hgi 0 1)
  have hconst : (∫ _x in s..t, c) * (m : ℝ) = 1 / (64 * (m : ℝ)) := by
    rw [integral_const, smul_eq_mul]
    dsimp [s, t, c]
    field_simp
    ring
  have hsplit : (∫ x in (0 : ℝ)..1, g x) = moment m m - moment m (m + 1) := by
    have hg : g = fun x : ℝ => x ^ m * Real.exp ((m : ℝ) * (x - 1)) -
        x ^ (m + 1) * Real.exp ((m : ℝ) * (x - 1)) := by
      funext x
      dsimp [g]
      rw [pow_succ]
      ring
    rw [hg, integral_sub ((continuous_moment_integrand m m).intervalIntegrable 0 1)
      ((continuous_moment_integrand m (m + 1)).intervalIntegrable 0 1)]
    rfl
  rw [← hsplit, ← hconst, mul_comm (m : ℝ)]
  exact mul_le_mul_of_nonneg_right (hsmall.trans hlarge) hm0.le

private theorem expCoeff_ne_zero {a : ℝ} (ha : 0 < a) (j : ℕ) :
    expCoeff a j ≠ 0 := by
  unfold expCoeff
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha.ne')) (by positivity)

theorem ratio_gap (m : ℕ) (hm : 1 ≤ m) (heven : Even m) :
    1 / (64 * (m : ℝ)) ≤
      expPartial m (m - 1) / expCoeff m m -
        expPartial m m / expCoeff m (m + 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have ha : 0 < expCoeff m m := by
    rw [expCoeff, heven.neg_pow]
    positivity
  have hb : expCoeff m (m + 1) < 0 := by
    obtain ⟨j, hj⟩ := heven
    have hodd : Odd (m + 1) := ⟨j, by omega⟩
    rw [expCoeff, hodd.neg_pow, neg_div]
    exact neg_neg_of_pos (by positivity)
  have hstep : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by exact_mod_cast hstep
  have hp := partial_remainder (m : ℝ) (m - 1)
  rw [hstep, hcast] at hp
  have hi := moment_succ (m : ℝ) (m - 1)
  rw [hstep, hcast] at hi
  have hj := moment_succ (m : ℝ) m
  have heq :
      expPartial m (m - 1) / expCoeff m m - expPartial m m / expCoeff m (m + 1) =
        Real.exp (-(m : ℝ)) / expCoeff m m - Real.exp (-(m : ℝ)) / expCoeff m (m + 1) +
        (m : ℝ) * (moment m m - moment m (m + 1)) := by
    rw [hp, partial_remainder (m : ℝ) m, sub_div, sub_div, mul_div_cancel_left₀ _ ha.ne',
      mul_div_cancel_left₀ _ hb.ne]
    linear_combination hj - hi
  rw [heq]
  have hleft : 0 ≤ Real.exp (-(m : ℝ)) / expCoeff m m := by positivity
  have hright : Real.exp (-(m : ℝ)) / expCoeff m (m + 1) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hb.le
  linarith [moment_gap m hm]

theorem solve_two_by_two
    (a b p q A B E d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hE : 0 ≤ E) (hd : 0 < d)
    (hgap : d ≤ q / b - p / a) (hp : |p / a| ≤ 2) (hq : |q / b| ≤ 2)
    (hA : |A| ≤ E) (hB : |B| ≤ 2 * E) :
    ∃ t u : ℝ, t * a + u * b = A ∧ t * p + u * q = B ∧
      |t| ≤ 4 * E / d / |a| ∧ |u| ≤ 4 * E / d / |b| := by
  let r := p / a
  let s := q / b
  let x := (s * A - B) / (s - r)
  let y := (B - r * A) / (s - r)
  have hpos : 0 < s - r := hd.trans_le hgap
  have hx : x + y = A := by
    dsimp [x, y]
    field_simp
    ring
  have hy : r * x + s * y = B := by
    dsimp [x, y]
    field_simp
    ring
  have hxn : |s * A - B| ≤ 4 * E := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul]
    have h := mul_le_mul hq hA (abs_nonneg _) (by norm_num)
    linarith
  have hyn : |B - r * A| ≤ 4 * E := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul]
    have h := mul_le_mul hp hA (abs_nonneg _) (by norm_num)
    linarith
  have hxabs : |x| ≤ 4 * E / d := by
    dsimp [x]
    rw [abs_div, abs_of_pos hpos]
    exact (div_le_div_of_nonneg_right hxn hpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hd hgap)
  have hyabs : |y| ≤ 4 * E / d := by
    dsimp [y]
    rw [abs_div, abs_of_pos hpos]
    exact (div_le_div_of_nonneg_right hyn hpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) hd hgap)
  refine ⟨x / a, y / b, ?_, ?_, ?_, ?_⟩
  · simpa only [div_mul_cancel₀ _ ha, div_mul_cancel₀ _ hb] using hx
  · convert hy using 1
    dsimp [r, s]
    ring
  · rw [abs_div]
    exact div_le_div_of_nonneg_right hxabs (abs_nonneg _)
  · rw [abs_div]
    exact div_le_div_of_nonneg_right hyabs (abs_nonneg _)

theorem abs_expCoeff (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    |expCoeff a j| = a ^ j / j.factorial := by
  rw [expCoeff, abs_div, abs_pow, abs_neg, abs_of_nonneg ha, abs_of_pos (by positivity)]

theorem abs_expCoeff_succ (m : ℕ) (hm : 1 ≤ m) :
    |expCoeff m m| / 2 ≤ |expCoeff m (m + 1)| := by
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have h := congrArg abs (expCoeff_succ (m : ℝ) m)
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m),
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1)] at h
  have hp := abs_nonneg (expCoeff m m)
  have hq := abs_nonneg (expCoeff m (m + 1))
  have hmono := mul_le_mul_of_nonneg_right (show (m : ℝ) + 1 ≤ 2 * m by linarith) hq
  have hprod : 0 ≤ (m : ℝ) * (2 * |expCoeff m (m + 1)| - |expCoeff m m|) := by
    linarith
  have h' := nonneg_of_mul_nonneg_right hprod (show (0 : ℝ) < m by linarith)
  linarith

theorem abs_partial_ratio_le {a : ℝ} (ha : 0 ≤ a) (j : ℕ)
    (hcoeff : Real.exp (-a) ≤ |expCoeff a (j + 1)|) :
    |expPartial a j / expCoeff a (j + 1)| ≤ 2 := by
  rw [abs_div, div_le_iff₀ ((Real.exp_pos _).trans_le hcoeff)]
  linarith [expPartial_abs_le ha j]

theorem small_two_terms (n m : ℕ) (hm : 1 ≤ m) (heven : Even m)
    (hhigh : (m : ℝ) ^ (n + 1) / (n + 1).factorial ≤ Real.exp (-(m : ℝ)))
    (K : ℝ) (hK : 0 < K)
    (hstirling : Real.exp (m : ℝ) ≤ K * (m : ℝ) * ((m : ℝ) ^ m / m.factorial)) :
    ∃ t u : ℝ,
      t * expCoeff m (m + 1) + u * expCoeff m m = expCoeff m (n + 1) ∧
      t * expPartial m m + u * expPartial m (m - 1) = expPartial m n ∧
      |t| ≤ 512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ)) ∧
      |u| ≤ 512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ)) := by
  have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hExp := Real.exp_pos (-(m : ℝ))
  have hexp_half : Real.exp (-(m : ℝ)) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith [Real.add_one_le_exp (m : ℝ)]
  have hmcoeff : 1 ≤ |expCoeff m m| := by
    rw [abs_expCoeff _ hm0.le, le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast Nat.factorial_le_pow m
  have hsucc := abs_expCoeff_succ m hm
  have hhalf : (1 / 2 : ℝ) ≤ |expCoeff m (m + 1)| := by linarith
  have hr := abs_partial_ratio_le (a := (m : ℝ)) hm0.le m (hexp_half.trans hhalf)
  have hidx : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hs := abs_partial_ratio_le (a := (m : ℝ)) hm0.le (m - 1)
    (by rw [hidx]; linarith)
  rw [hidx] at hs
  have hA : |expCoeff (m : ℝ) (n + 1)| ≤ Real.exp (-(m : ℝ)) := by
    rwa [abs_expCoeff _ hm0.le]
  have hB : |expPartial (m : ℝ) n| ≤ 2 * Real.exp (-(m : ℝ)) := by
    linarith [expPartial_abs_le hm0.le n]
  obtain ⟨t, u, ht, hu, htB, huB⟩ :=
    solve_two_by_two _ _ _ _ _ _ _ _ (expCoeff_ne_zero hm0 _) (expCoeff_ne_zero hm0 _)
      hExp.le (by positivity) (ratio_gap m hm heven) hr hs hA hB
  rw [← abs_expCoeff _ hm0.le] at hstirling
  have hfix (a : ℝ) (ha : 0 < a) (hb : |expCoeff m m| / 2 ≤ a) :
      4 * Real.exp (-(m : ℝ)) / (1 / (64 * (m : ℝ))) / a ≤
        512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ)) := by
    have hprod : Real.exp (m : ℝ) ≤ (2 * K * (m : ℝ)) * a := by
      refine hstirling.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * K * (m : ℝ) by positivity)]
    have hr := (div_le_iff₀ ha).mpr hprod
    have hom : Real.exp (-2 * (m : ℝ)) =
        Real.exp (-(m : ℝ)) * Real.exp (-(m : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have inv_bound : 1 / a ≤ 2 * K * (m : ℝ) * Real.exp (-(m : ℝ)) := by
      calc
        1 / a = (Real.exp (m : ℝ) / a) * Real.exp (-(m : ℝ)) := by
          rw [Real.exp_neg]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hr hExp.le
    rw [hom, div_div_eq_mul_div, div_one, div_eq_mul_inv]
    calc
      (4 * Real.exp (-↑m) * (64 * ↑m)) * a⁻¹
          ≤ (4 * Real.exp (-↑m) * (64 * ↑m)) * (2 * K * ↑m * Real.exp (-↑m)) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using inv_bound) (by positivity)
      _ = _ := by ring
  exact ⟨t, u, ht, hu, htB.trans (hfix _ (by linarith) hsucc),
    huB.trans (hfix _ (by linarith) (by linarith))⟩

end Erdos973Upper

/- Scalar estimates for the equal-power-sum construction in the upper bound. -/

open Filter Finset
open scoped Topology

namespace M2UpperScalar

noncomputable def m (n : ℕ) : ℕ := 2 * ⌊(0.1392 : ℝ)*n⌋₊

theorem m_even (n : ℕ) : Even (m n) := by
  refine ⟨⌊(0.1392 : ℝ)*n⌋₊,?_⟩
  simp only [m, two_mul]

theorem m_bounds (n : ℕ) :
    (m n : ℝ) ≤ (0.2784 : ℝ)*n ∧ (0.2784 : ℝ)*n < (m n : ℝ)+2 := by
  have hle := Nat.floor_le (show 0 ≤ (0.1392 : ℝ)*n by positivity)
  have hlt := Nat.lt_floor_add_one ((0.1392 : ℝ)*n)
  push_cast [m]
  constructor <;> linarith

theorem numeric_tail : (0.2784 : ℝ)*Real.exp (1+0.2784) < 1 := by
  have h : Real.exp (0.6392 : ℝ) ≤ 1.895 := by
    refine (Real.exp_bound' (x := 0.6392) (by norm_num) (by norm_num) (n := 8) (by decide)).trans ?_
    norm_num [Finset.sum_range_succ]
  have hx := Real.exp_pos (0.6392 : ℝ)
  rw [show (1+0.2784 : ℝ)=0.6392+0.6392 by norm_num, Real.exp_add]
  nlinarith [mul_le_mul h h hx.le (show (0:ℝ)≤1.895 by norm_num)]

theorem numeric_rate : (1.745 : ℝ) < Real.exp (0.5568 : ℝ) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (x := (0.5568 : ℝ)) (by norm_num) 8)
  norm_num [Finset.sum_range_succ]

theorem exponential_tail (n : ℕ) :
    (m n : ℝ)^(n+1)/((n+1).factorial : ℝ) ≤ Real.exp (-(m n : ℝ)) := by
  let N := n+1
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hN_le : (n : ℝ) ≤ N := by dsimp [N]; push_cast; linarith
  have hN_sqrt : 1 ≤ Real.sqrt (2*Real.pi*(N : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    simpa only [one_mul] using mul_le_mul hp hN1 zero_le_one (by positivity)
  have hpos : 0 < (N : ℝ)/Real.exp 1 := div_pos hN (Real.exp_pos _)
  have hf : ((N : ℝ)/Real.exp 1)^N ≤ (N.factorial : ℝ) :=
    (le_mul_of_one_le_left (by positivity) hN_sqrt).trans (Stirling.le_factorial_stirling N)
  have hm : (m n : ℝ) ≤ (0.2784 : ℝ)*N :=
    (m_bounds n).1.trans (mul_le_mul_of_nonneg_left hN_le (by norm_num))
  have hlead : (0.2784 : ℝ)*Real.exp 1 ≤ Real.exp (-0.2784) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _), mul_assoc, ← Real.exp_add]
    exact numeric_tail.le
  have hfrac : (m n : ℝ)/((N : ℝ)/Real.exp 1) ≤ Real.exp (-0.2784) := by
    apply le_trans ?_ hlead
    rw [div_div_eq_mul_div, div_le_iff₀ hN]
    calc
      (m n : ℝ)*Real.exp 1 ≤ ((0.2784 : ℝ)*N)*Real.exp 1 :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
      _ = (0.2784 : ℝ)*Real.exp 1*N := by ring
  change (m n : ℝ)^N/(N.factorial : ℝ) ≤ _
  calc
    _ ≤ (m n : ℝ)^N/((N : ℝ)/Real.exp 1)^N :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hpos _) hf
    _ = ((m n : ℝ)/((N : ℝ)/Real.exp 1))^N := by rw [← div_pow]
    _ ≤ Real.exp (-0.2784)^N := pow_le_pow_left₀ (by positivity) hfrac _
    _ = Real.exp ((N : ℝ)*(-0.2784)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(m n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The chosen even index is large enough, and leaves room for the two corrections. -/
theorem eventual_indices :
    ∀ᶠ n : ℕ in atTop, 1 ≤ m n ∧ m n ≤ n ∧
      n+1 ≤ (n-m n)+((n-m n)-1) ∧
      (m n : ℝ)^(n+1)/((n+1).factorial : ℝ) ≤ Real.exp (-(m n : ℝ)) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
  have hn' : (8 : ℝ)≤n := by exact_mod_cast hn
  have hpos : 1 ≤ ⌊(0.1392 : ℝ)*n⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hm1 : 1 ≤ m n := by unfold m; omega
  have h2 : (2 : ℝ)*(m n : ℝ)+2≤n := by linarith [(m_bounds n).1]
  have h2' : 2*m n+2≤n := by exact_mod_cast h2
  refine ⟨hm1,by omega,by omega,exponential_tail n⟩

/-- Stirling's bounded factor gives a linear prefactor in this ratio. -/
theorem exists_factorial_ratio :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (n : ℝ) ≤ K*(n : ℝ)*(n : ℝ)^n/(n.factorial : ℝ) := by
  let K := 2*Stirling.stirlingSeq 1
  have hK : 0 < K := mul_pos (by norm_num) (Stirling.stirlingSeq'_pos 0)
  refine ⟨K,hK,?_⟩
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hden : 0 < Real.sqrt (2*(n : ℝ))*((n : ℝ)/Real.exp 1)^n := by positivity
  unfold Stirling.stirlingSeq at hseq
  have hseq' :
      (n.factorial : ℝ) ≤ Stirling.stirlingSeq 1 * (Real.sqrt (2*(n : ℝ))*((n : ℝ)/Real.exp 1)^n) := by
    change (n.factorial : ℝ)/(Real.sqrt (2*(n : ℝ))*((n : ℝ)/Real.exp 1)^n) ≤
      Stirling.stirlingSeq 1 at hseq
    exact (div_le_iff₀ hden).mp hseq
  have hsqrt : Real.sqrt (2*(n : ℝ)) ≤ 2*n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hfac :
      (n.factorial : ℝ) ≤ K*(n : ℝ)*((n : ℝ)/Real.exp 1)^n := by
    calc
      _ ≤ Stirling.stirlingSeq 1 * (Real.sqrt (2*(n : ℝ))*((n : ℝ)/Real.exp 1)^n) := hseq'
      _ ≤ Stirling.stirlingSeq 1 * (2*(n : ℝ)*((n : ℝ)/Real.exp 1)^n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt (by positivity))
          (Stirling.stirlingSeq'_pos 0).le
      _ = _ := by dsimp [K]; ring
  rw [div_pow, ← Real.exp_nat_mul, mul_one, ← mul_div_assoc] at hfac
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n)), mul_comm]
  exact (le_div_iff₀ (Real.exp_pos _)).mp hfac

/-- The polynomial factor is absorbed by the strict gap in the exponential rate. -/
theorem eventual_rate (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      ((n : ℝ)+1)*C*(m n : ℝ)^2*Real.exp (-2*(m n : ℝ)) <
        (1.745 : ℝ)^(-(n : ℝ)) := by
  let δ := (0.5568 : ℝ)-Real.log 1.745
  have hδ : 0 < δ := sub_pos.mpr ((Real.log_lt_iff_lt_exp (by norm_num)).mpr numeric_rate)
  have hlim : Tendsto
      (fun n : ℕ => (n : ℝ)^3*Real.exp (-δ*(n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.rpow_natCast, Nat.cast_ofNat] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 δ hδ).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim' : Tendsto
      (fun n : ℕ => (2*C*Real.exp 4)*((n : ℝ)^3*Real.exp (-δ*(n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2*C*Real.exp 4)
  filter_upwards [eventually_ge_atTop (1 : ℕ),hlim'.eventually_lt_const zero_lt_one] with n hn hsmall
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have hm : (m n : ℝ) ≤ n := (m_bounds n).1.trans (by nlinarith)
  have hm2 : (m n : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (by positivity) hm _
  have hpoly : ((n : ℝ)+1)*C*(m n : ℝ)^2 ≤ (2*C)*(n : ℝ)^3 := by
    calc
      _ ≤ (2*(n : ℝ))*C*(m n : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hC.le) (by positivity)
      _ ≤ (2*(n : ℝ))*C*(n : ℝ)^2 :=
        mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = _ := by ring
  have hexp : Real.exp (-2*(m n : ℝ))*Real.exp (Real.log 1.745*(n : ℝ)) ≤
      Real.exp 4*Real.exp (-δ*(n : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (m_bounds n).2
    dsimp [δ]
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : 0<(1.745 : ℝ))]
  apply (mul_lt_mul_iff_left₀ (Real.exp_pos (Real.log 1.745*(n : ℝ)))).mp
  rw [← Real.exp_add, show Real.log 1.745*(-(n : ℝ))+Real.log 1.745*(n : ℝ)=0 by ring,
    Real.exp_zero, mul_assoc]
  calc
    _ ≤ (2*C*(n : ℝ)^3)*(Real.exp 4*Real.exp (-δ*(n : ℝ))) :=
      mul_le_mul hpoly hexp (by positivity) (by positivity)
    _ = (2*C*Real.exp 4)*((n : ℝ)^3*Real.exp (-δ*(n : ℝ))) := by ring
    _ < 1 := hsmall

end M2UpperScalar

open Finset Filter in
theorem OMA.solution : type_of% @Erdos973.erdos_973.variants.m2_bounds := by
  obtain ⟨K, hK, hfactorial⟩ := M2UpperScalar.exists_factorial_ratio
  filter_upwards [PowerSumLower973.eventually_lower_glb, M2UpperScalar.eventual_indices,
    M2UpperScalar.eventual_rate (512 * K) (by positivity)] with n hl hi hrate M₂ hM
  refine ⟨hl M₂ hM, ?_⟩
  let m := M2UpperScalar.m n
  let k := n - m
  obtain ⟨hm, hmn, hsize, htail⟩ := hi
  have hm' : 1 ≤ m := hm
  have hmn' : m ≤ n := hmn
  have hk : k ≤ n := Nat.sub_le _ _
  have hn : 1 ≤ n := hm'.trans hmn'
  have hfact : Real.exp (m : ℝ) ≤ K * (m : ℝ) * ((m : ℝ) ^ m / m.factorial) := by
    rw [← mul_div_assoc]
    exact hfactorial m hm
  obtain ⟨t, u, ht, hu, htB, huB⟩ :=
    Erdos973Upper.small_two_terms n m hm' (M2UpperScalar.m_even n) htail K hK hfact
  have hcoeff (j : ℕ) :
      PowerSeries.coeff j (Erdos973Upper.taylor (m : ℂ)) =
        (Erdos973Upper.expCoeff (m : ℝ) j : ℂ) := by
    simp [Erdos973Upper.coeff_taylor, Erdos973Upper.expCoeff]
  have hsum (j : ℕ) :
      (∑ i ∈ range (j + 1), PowerSeries.coeff i (Erdos973Upper.taylor (m : ℂ))) =
        (Erdos973Upper.expPartial (m : ℝ) j : ℂ) := by
    simp [Erdos973Upper.expPartial, hcoeff]
  have hidx₁ : n + 1 - k = m + 1 := by dsimp [k]; omega
  have hidx₂ : n - k = m := by dsimp [k]; omega
  have hidx₃ : m - 1 + 1 = m := Nat.sub_add_cancel hm'
  have hsmall (x : ℝ) (hx : |x| ≤ 512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ))) :
      ((k : ℝ) + 1) * ‖(x : ℂ)‖ < (1.745 : ℝ) ^ (-(n : ℝ)) := by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine lt_of_le_of_lt ?_ hrate
    have hbound : 0 ≤ 512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ)) := by positivity
    calc
      _ ≤ ((k : ℝ) + 1) * (512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ ((n : ℝ) + 1) * (512 * K * (m : ℝ) ^ 2 * Real.exp (-2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hbound
      _ = _ := by change _ = ((n : ℝ) + 1) * (512 * K) * (m : ℝ) ^ 2 *
            Real.exp (-2 * (m : ℝ)); ring
  refine Erdos973Upper.upper_bound_of_two_terms n k hn hk hsize (m : ℂ) (t : ℂ) (u : ℂ)
    ((1.745 : ℝ) ^ (-(n : ℝ))) (by positivity) ?_ (hsmall u huB) ?_ ?_ M₂ hM
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      (hsmall t htB)
  · rw [hidx₁, hidx₂, hcoeff, hcoeff, hcoeff]
    exact_mod_cast ht.symm
  · have hprev := hsum (m - 1)
    rw [hidx₃] at hprev
    rw [hidx₁, hidx₂, hsum n, hsum m, hprev]
    exact_mod_cast hu.symm