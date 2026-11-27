import FormalConjectures.ErdosProblems.«977»
import Mathlib

/-! Li Lai, On the largest prime divisor of n! + 1, arXiv:2103.14894.
Use a multiplicative interval [N,(1+d)N]. Its factorials contribute
at least (1-o(1)) N log N per integer. If every largest prime factor
were small, all of that weight would be carried by primes between N and
λ(1+d)N. Applying Lai's local valuation bound on this same interval
and letting d tend to zero recovers 1+9 log 2. -/
namespace OMA.R_Erdos977_erdos_977_variants_lai_R1

open Finset Filter Real
open scoped Classical Topology

/-- The upper half of the prime number theorem on fixed proportional intervals. -/
def H1 : Prop := ∀ b : ℝ, 1<b → ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop,
  (((Ioc N ⌊b*N⌋₊).filter Nat.Prime).card:ℝ)*log N ≤ (b-1+δ)*N

/-- Lai's bound on the sum of the p-adic orders, on a fixed proportional interval.
This is the local estimate obtained by summing Lemma 2.7 over geometric layers. -/
def H2 : Prop := ∀ d : ℝ, 0<d → d<1 → ∀ η : ℝ, 0<η → ∀ᶠ N : ℕ in atTop,
  let T := Icc N ⌊(1+d)*N⌋₊
  ∀ p : ℕ, p.Prime → N<p →
    (∑ n ∈ T, ((n.factorial+1).factorization p : ℝ)*log p) ≤
      (1/(9*log 2)+η)*T.card*(log N)^2

lemma primeDecomposition {m : ℕ} (hn : m ≠ 0) (P : Finset ℕ) (sub : m.primeFactors ⊆ P) :
    log m = ∑ p ∈ P,(m.factorization p:ℝ)*log p := by
  have eq := congrArg (fun n : ℕ => (n:ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  push_cast at eq
  calc
    log m = log (∏ p ∈ m.primeFactors,(p:ℝ)^m.factorization p) := congrArg log eq
    _ = ∑ p ∈ m.primeFactors,(m.factorization p:ℝ)*log p := by
      rw [Real.log_prod]
      · simp only [log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
    _ = _ := sum_subset sub fun p _ hp => by
      have h : p ∉ m.factorization.support := by simpa using hp
      simp [Finsupp.notMem_support_iff.mp h]

lemma factorialMass (δ : ℝ) (hd : 0<δ) :
    ∀ᶠ N : ℕ in atTop, ∀ n ≥ N,
      (1-δ)*N*log N ≤ log (n.factorial+1:ℕ) := by
  have grow := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (1/δ)
  filter_upwards [grow,eventually_ge_atTop 2] with N hlog hN
  intro n hn
  have h1 : N ≠ 0 := by omega
  have st := Stirling.le_log_factorial_stirling h1
  have l0 : 0 ≤ log (2*π) := log_nonneg (by linarith [Real.pi_gt_three])
  have hδ : 1 ≤ δ*log N := by
    have := (div_le_iff₀ hd).mp (show 1/δ ≤ log N from hlog)
    linarith
  have inc : (N.factorial:ℝ) ≤ (n.factorial+1:ℕ) := by
    exact_mod_cast (Nat.factorial_le hn).trans (Nat.le_succ _)
  have incr := log_le_log (by exact_mod_cast Nat.factorial_pos N) inc
  nlinarith only [incr,st,l0,Real.log_natCast_nonneg N,
    mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α:=ℝ) N)]

lemma slack (C L : ℝ) (hL : 0<L) (hC : C<1+L) :
    ∃ a : ℝ, 1<a ∧ C<a ∧ ∃ d : ℝ, 0<d ∧ d<1 ∧
      (1/L+d)*(a*(1+d)-1+d)<1-d := by
  let a := (max C 1 + (1+L))/2
  have hm : max C 1 < 1+L := max_lt hC (by linarith)
  have av : max C 1<a := by dsimp [a];linarith
  have al : a<1+L := by dsimp [a];linarith
  refine ⟨a,(le_max_right ..).trans_lt av,(le_max_left ..).trans_lt av,?_⟩
  have init : (1/L+0)*(a*(1+0)-1+0)<1-0 := by
    simp only [add_zero,sub_zero,one_mul,mul_one,one_div]
    rw [←div_eq_inv_mul,div_lt_iff₀ hL]
    linarith
  have u : Continuous (fun z : ℝ => (1/L+z)*(a*(1+z)-1+z)) := by fun_prop
  have v : Continuous (fun z : ℝ => 1-z) := by fun_prop
  have ev : ∀ᶠ z : ℝ in 𝓝 0,(1/L+z)*(a*(1+z)-1+z)<1-z := u.continuousAt.eventually_lt v.continuousAt init
  obtain ⟨e,he,ball⟩ := Metric.eventually_nhds_iff.mp ev
  let z := min (e/2) (1/2)
  have z0 : 0<z := lt_min (by positivity) (by norm_num)
  refine ⟨z,z0,lt_of_le_of_lt (min_le_right ..) (by norm_num),ball ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_pos z0]
  exact (min_le_left ..).trans_lt (by linarith)

theorem main : H1 → H2 → type_of% @Erdos977.erdos_977.variants.lai := by
  classical
  intro count valu C hC
  let L := 9*log 2
  have hL : 0<L := by dsimp [L];positivity
  obtain ⟨a,ha,hCa,d,hd,hd1,hslack⟩ := slack C L hL hC
  let b := a*(1+d)
  have hb : 1<b := by dsimp [b];nlinarith only [ha,hd,mul_pos (lt_trans zero_lt_one ha) hd]
  by_contra h
  have bad := not_frequently.mp h
  obtain ⟨M,hM⟩ := eventually_atTop.mp bad
  have ev := (count b hb d hd).and ((valu d hd hd1 d hd).and (factorialMass d hd))
  obtain ⟨N,⟨hcount,hval,hfac⟩,hN⟩ := (ev.and (eventually_ge_atTop (M+2))).exists
  let T := Icc N ⌊(1+d)*N⌋₊
  let P := (Ioc N ⌊b*N⌋₊).filter Nat.Prime
  have hnp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have logp : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have Tpos : (0:ℝ)<T.card := by
    exact_mod_cast (card_pos.mpr ⟨N,mem_Icc.mpr ⟨le_rfl,Nat.le_floor (by nlinarith [mul_pos hd hnp])⟩⟩ : 0<T.card)
  have hsup (n : ℕ) (hn : n ∈ T) : (n.factorial+1).primeFactors ⊆ P := by
    obtain ⟨hnN,hn'⟩ := mem_Icc.mp hn
    intro p hp
    obtain ⟨pr,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
    have nlt : n<p := by
      by_contra! h
      have one := (Nat.dvd_add_right (Nat.dvd_factorial pr.pos h)).mp dvd
      exact pr.not_dvd_one one
    have maxb := not_lt.mp (hM n (by omega))
    have lp := Nat.le_maxPrimeFac nz pr dvd
    have nu : (n:ℝ) ≤ (1+d)*N := (Nat.le_floor_iff (by positivity)).mp hn'
    have up : (p:ℝ) ≤ b*N := calc
      _ ≤ (Nat.maxPrimeFac (n.factorial+1):ℝ) := by exact_mod_cast lp
      _ ≤ C*n := maxb
      _ ≤ a*n := mul_le_mul_of_nonneg_right hCa.le (Nat.cast_nonneg _)
      _ ≤ b*N := by dsimp [b];rw [mul_assoc];exact mul_le_mul_of_nonneg_left nu (by linarith)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnN.trans_lt nlt,Nat.le_floor up⟩,pr⟩
  let F (n p : ℕ) : ℝ := ((n.factorial+1).factorization p:ℝ)*log p
  have lower : (T.card:ℝ)*((1-d)*N*log N) ≤ ∑ p ∈ P,∑ n ∈ T,F n p := by
    rw [sum_comm]
    calc
      _ = ∑ n ∈ T,(1-d)*N*log N := by simp
      _ ≤ _ := sum_le_sum fun n hn => (hfac n (mem_Icc.mp hn).1).trans
        (primeDecomposition (by omega) P (hsup n hn)).le
  have upper : (∑ p ∈ P,∑ n ∈ T,F n p) ≤
      P.card*((1/L+d)*T.card*(log N)^2) := by
    calc
      _ ≤ ∑ p ∈ P, (1/L+d)*T.card*(log N)^2 := sum_le_sum fun p hp =>
        hval p (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).1
      _ = _ := by simp
  have coef : 0 ≤ (1/L+d)*(T.card:ℝ)*log N := by positivity
  have cap := mul_le_mul_of_nonneg_right (show (P.card:ℝ)*log N ≤ (b-1+d)*N from hcount) coef
  have scale : 0<(T.card:ℝ)*N*log N := by positivity
  have strict := mul_lt_mul_of_pos_right hslack scale
  change (1/L+d)*(b-1+d)*_ < _ at strict
  linarith only [lower,upper,cap,strict]

end OMA.R_Erdos977_erdos_977_variants_lai_R1

