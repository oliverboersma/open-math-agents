import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1
import Mathlib

/-! For the lcm of the integers up to N, the exponent of p is the integer
logarithm to base p of N. Separate the exact Euler factors from the tail
estimate: primes up to √N contribute O(√N/N), and larger primes contribute
O(∑_{k>√N} k⁻²). The change of height from theta to psi is absorbed below. -/
namespace OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H2_R1
open Real Filter Finset
open scoped ArithmeticFunction.sigma

def H1 : Prop := ∀ N : ℕ, 2 ≤ N →
  log ((σ 1 (Nat.lcmUpto N) : ℝ) / Nat.lcmUpto N) +
    log (∏ p ∈ Nat.primesLE N, (1-1/(p:ℝ))) =
    ∑ p ∈ Nat.primesLE N, log (1-1/(p:ℝ)^(p.log N + 1))

def H2 : Prop := ∃ K : ℝ, ∀ᶠ x : ℝ in atTop,
  -(∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1-1/(p:ℝ)^(p.log ⌊x⌋₊ + 1))) ≤ K/sqrt x

lemma logs {u v : ℝ} (hu : exp 1 ≤ u) (hv : u ≤ v) :
    log (log v) - log (log u) ≤ (v-u)/u := by
  have up : 0 < u := (exp_pos _).trans_le hu
  have vp := up.trans_le hv
  have lu : 1 ≤ log u := (le_log_iff_exp_le up).mpr hu
  have lvp : 0 < log v := by linarith [log_le_log up hv]
  have lup : 0 < log u := by linarith
  have a := log_le_sub_one_of_pos (div_pos vp up)
  rw [log_div vp.ne' up.ne'] at a
  have b := log_le_sub_one_of_pos (div_pos lvp lup)
  rw [log_div lvp.ne' lup.ne'] at b
  have s : log v / log u - 1 = (log v-log u)/log u := by field_simp
  rw [s] at b
  have h := div_le_self (sub_nonneg.mpr (log_le_log up hv)) lu
  have e : v/u-1=(v-u)/u := by field_simp
  linarith

private lemma localFactor (p : ℝ) (hp : 1<p) (k : ℕ) :
    (∑ i ∈ range (k+1), p^i) / p^k * (1-1/p) = 1-1/p^(k+1) := by
  have h := geom_sum_mul p (k+1)
  have pn : p ≠ 0 := by linarith
  rw [pow_succ] at h ⊢
  field_simp
  nlinarith

private theorem exactFactors : H1 := by
  intro N _
  let S := Nat.primesLE N
  have prime (p : ℕ) (h : p ∈ S) : (1:ℝ)<p := by
    exact_mod_cast (Nat.prime_of_mem_primesLE h).one_lt
  have pos₁ (p : ℕ) (h : p ∈ S) : 0 < (1-1/(p:ℝ)) := by
    have hp := prime p h
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp)
  have pos₂ (p : ℕ) (h : p ∈ S) : 0 < 1-1/(p:ℝ)^(p.log N+1) := by
    have hp := prime p h
    have a := one_lt_pow₀ hp (Nat.succ_ne_zero (p.log N))
    exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans a)).mpr a)
  have sigma : (σ 1 (Nat.lcmUpto N) : ℝ) = ∏ p ∈ S, ∑ i ∈ range (p.log N+1), (p:ℝ)^i := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (Nat.lcmUpto_ne_zero N), Nat.primeFactors_lcmUpto]
    push_cast
    apply prod_congr rfl
    intro p hp
    simp [Nat.factorization_lcmUpto N (Nat.prime_of_mem_primesLE hp)]
  have lcm : (Nat.lcmUpto N : ℝ) = ∏ p ∈ S, (p:ℝ)^(p.log N) := by
    exact_mod_cast Nat.lcmUpto_eq_prod_pow_log N
  have ratio : 0 < (σ 1 (Nat.lcmUpto N) : ℝ) / Nat.lcmUpto N := by
    apply div_pos
    · exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (Nat.lcmUpto_ne_zero N)
    · exact_mod_cast Nat.lcmUpto_pos N
  rw [← log_mul ratio.ne' (prod_pos pos₁).ne', ← log_prod (fun p h => (pos₂ p h).ne')]
  apply congrArg log
  rw [sigma,lcm,← prod_div_distrib,← prod_mul_distrib]
  exact prod_congr rfl fun p h => localFactor _ (prime _ h) _

private lemma logLoss {A : ℝ} (hA : 2 ≤ A) : -log (1-1/A) ≤ 2/A := by
  have pos : 0 < 1-1/A := by
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have h := log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [log_inv] at h
  apply h.trans
  have e : (1-1/A)⁻¹ - 1 = 1/(A-1) := by
    have h₁ : A ≠ 0 := by linarith
    have h₂ : A-1 ≠ 0 := by linarith
    rw [show 1-1/A = (A-1)/A by field_simp, inv_div]
    field_simp
    <;> ring
  rw [e,div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

private lemma telescope (m : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (1/(m+i)-1/(m+i+1)) = 1/m-1/(m+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih];push_cast;ring_nf

private theorem tailEstimate : H2 := by
  refine ⟨24,?_⟩
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx
  let m : ℝ := ⌊sqrt x⌋₊
  let N := ⌊x⌋₊
  have sq := sq_sqrt (by linarith : 0≤x)
  have sm := sqrt_nonneg x
  have ml : m ≤ sqrt x := Nat.floor_le sm
  have mu : sqrt x < m+1 := Nat.lt_floor_add_one _
  have mp : 0 < m := by nlinarith
  have nonneg (i : ℕ) : 0 ≤ 1/(m+i)-1/(m+i+1) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [← sum_neg_distrib]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, 12 * (1/(m+p)-1/(m+p+1)) := by
      apply sum_le_sum
      intro p h
      have ph := Nat.prime_of_mem_primesLE h
      have p2 : (2:ℝ)≤p := by exact_mod_cast ph.two_le
      let A := (p:ℝ)^(p.log N+1)
      have nx := Nat.lt_pow_succ_log_self ph.one_lt N
      have nA : (N:ℝ)+1 ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.succ_le_of_lt nx)
      have xx : x < (N:ℝ)+1 := Nat.lt_floor_add_one _
      have kp : 0 < p.log N := Nat.log_pos_iff.mpr ⟨Nat.le_of_mem_primesLE h,ph.one_lt⟩
      have pA : (p:ℝ)^2 ≤ A := by
        dsimp only [A]
        exact pow_le_pow_right₀ (by linarith) (Nat.succ_le_succ kp)
      have den : (m+p)*(m+p+1) ≤ 6*A := by
        by_cases small : (p:ℝ) ≤ sqrt x
        · have a : m+p ≤ 2*sqrt x := by linarith
          have b : m+p+1 ≤ 3*sqrt x := by nlinarith
          nlinarith [mul_le_mul a b (by positivity) (by positivity)]
        · have a : m+p ≤ 2*p := by linarith
          have b : m+p+1 ≤ 3*p := by linarith
          nlinarith [mul_le_mul a b (by positivity) (by positivity)]
      apply (logLoss (A:=A) (by linarith)).trans
      have pos : 0 < m+(p:ℝ) := by positivity
      have pos' : 0 < m+(p:ℝ)+1 := by positivity
      have e : 12 * (1/(m+p)-1/(m+p+1)) = 12 / ((m+p)*(m+p+1)) := by field_simp;ring
      rw [e, div_le_div_iff₀ (by linarith) (mul_pos pos pos')]
      linarith
    _ ≤ ∑ p ∈ range (N+1), 12 * (1/(m+p)-1/(m+p+1)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun p h => mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE h))
      · exact fun p _ _ => mul_nonneg (by norm_num) (nonneg p)
    _ ≤ 24 / sqrt x := by
      rw [← mul_sum,telescope]
      have h : 0 ≤ 1/(m+((N+1:ℕ):ℝ)) := by positivity
      have r : 12/m ≤ 24/sqrt x := by
        rw [div_le_div_iff₀ mp (sqrt_pos.2 (by linarith))]
        nlinarith
      apply le_trans _ r
      calc _ ≤ 12*(1/m) := mul_le_mul_of_nonneg_left (sub_le_self _ h) (by norm_num)
           _ = _ := by ring

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1.H2 := by
  rintro factors ⟨K,tail⟩ b hb bh ε he
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := 32*|C|+|K|+1
  have decay := (tendsto_rpow_atTop (show 0<(1/2:ℝ)-b by linarith)).eventually_ge_atTop (D/ε)
  have large := tendsto_sqrt_atTop.eventually_ge_atTop (32*|C|)
  filter_upwards [tail,decay,large,eventually_ge_atTop (128:ℝ)] with x ht hd hl hx
  let N := ⌊x⌋₊
  have xp : 0<x := by linarith
  have hp : 0<sqrt x := sqrt_pos.2 xp
  have sq := sq_sqrt xp.le
  have n40 : 40 ≤ N := Nat.le_floor (by push_cast; linarith)
  have psi : Chebyshev.psi x = log (Nat.lcmUpto N) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have height := OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1.height n40
  have xf := Nat.lt_floor_add_one x
  change x < (N:ℝ)+1 at xf
  have loss := hC x
  have small := mul_le_mul_of_nonneg_right hl hp.le
  have theta : x/32 ≤ Chebyshev.theta x := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) hp.le]
  have tp : 0 < Chebyshev.theta x := by linarith
  have te : exp 1 ≤ Chebyshev.theta x := by linarith [exp_one_lt_three]
  have cmp := logs te (Chebyshev.theta_le_psi x)
  have ratio : (Chebyshev.psi x-Chebyshev.theta x)/Chebyshev.theta x ≤ 32*|C|/sqrt x := by
    rw [div_le_div_iff₀ tp hp]
    calc _ ≤ C*sqrt x*sqrt x := mul_le_mul_of_nonneg_right loss hp.le
         _ ≤ |C| * x := by nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) xp.le, congrArg (C*·) sq]
         _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left theta (abs_nonneg C)]
  have poweq : x^(1/2-b:ℝ)=sqrt x*x^(-b) := by rw [sqrt_eq_rpow,←rpow_add xp] <;> ring_nf
  change D/ε ≤ x^(1/2-b:ℝ) at hd
  rw [poweq,div_le_iff₀ he] at hd
  have allowed : (32*|C|+K)/sqrt x ≤ ε*x^(-b) := by
    rw [div_le_iff₀ hp]
    dsimp [D] at hd
    linarith [le_abs_self K]
  have Ppos : 0 < ∏ p ∈ Nat.primesLE N, (1-1/(p:ℝ)) := by
    apply prod_pos
    intro p h
    have p1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr p1)
  have F := factors N (by omega)
  change -log (exp eulerMascheroniConstant * log (Chebyshev.theta x) * _) - _ ≤ _
  rw [log_mul (mul_pos (exp_pos _) (log_pos (by linarith))).ne' Ppos.ne',
    log_mul (exp_pos _).ne' (log_pos (by linarith : 1 < Chebyshev.theta x)).ne',log_exp]
  have combined := cmp.trans ratio
  rw [psi] at combined
  rw [add_div] at allowed
  linarith

end OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H2_R1

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1.H2 := OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H2_R1.main OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H2_R1.exactFactors OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H2_R1.tailEstimate
