import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1
import Mathlib

-- Step Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1.H2: hypothesis H2 of reduction
-- Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1
-- Credit: @ivillar

/-!
`∑_{d ∣ L} cos(s(log d - y))` is the real part of `e^{-isy} ∑_{d ∣ L} d^{is}`, and `d ↦ d^{is}`
is multiplicative, so `∑_{d ∣ L} d^{is} = ∏_{p^e ∥ L} ∑_{j ≤ e} p^{ijs}`. Each factor has norm at
most `e + 1`; a prime `p ∈ (√k, k]` divides `L = lcm(1..k)` exactly once and its factor
`1 + p^{is}` has norm `2 |cos(s log p / 2)|`. Hence the sum is at most
`d(L) ∏_{p ∈ (√k, k]} |cos(s log p / 2)| ≤ d(L) exp(-∑ (1 - |cos|))`, using `x ≤ e^{x-1}`.
-/

open Finset Real ArithmeticFunction

namespace OMA.Erdos1099Fourier

noncomputable def chi (s : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d = 0 then 0 else ((d : ℂ) ^ ((s : ℂ) * Complex.I)), by simp⟩

theorem chi_apply (s : ℝ) {d : ℕ} (hd : d ≠ 0) : chi s d = (d : ℂ) ^ ((s : ℂ) * Complex.I) := by
  simp [chi, hd]

theorem chi_mult (s : ℝ) : (chi s).IsMultiplicative := by
  refine ⟨by simp [chi], ?_⟩
  intro m n _
  by_cases hm : m = 0
  · simp [chi, hm]
  by_cases hn : n = 0
  · simp [chi, hn]
  rw [chi_apply s (mul_ne_zero hm hn), chi_apply s hm, chi_apply s hn]
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n _

theorem norm_chi (s : ℝ) {d : ℕ} (hd : 0 < d) : ‖chi s d‖ = 1 := by
  rw [chi_apply s hd.ne', Complex.norm_natCast_cpow_of_pos hd]
  simp

theorem chi_eq_exp (s : ℝ) {d : ℕ} (hd : 0 < d) :
    chi s d = Complex.exp (((s * Real.log d : ℝ) : ℂ) * Complex.I) := by
  rw [chi_apply s hd.ne', Complex.cpow_def_of_ne_zero (by exact_mod_cast hd.ne'),
    ← Complex.natCast_log]
  push_cast
  ring_nf

theorem G_prime_pow (s : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (chi s * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (p ^ e) = ∑ x ∈ range (e + 1), chi s (p ^ x) := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]

theorem norm_G_le (s : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖(chi s * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (p ^ e)‖ ≤ (e : ℝ) + 1 := by
  rw [G_prime_pow s hp]
  calc ‖∑ x ∈ range (e + 1), chi s (p ^ x)‖ ≤ ∑ x ∈ range (e + 1), ‖chi s (p ^ x)‖ :=
        norm_sum_le _ _
    _ = ∑ _x ∈ range (e + 1), (1 : ℝ) :=
        sum_congr rfl (fun x _ => norm_chi s (pow_pos hp.pos x))
    _ = (e : ℝ) + 1 := by simp

theorem norm_G_prime (s : ℝ) {p : ℕ} (hp : p.Prime) :
    ‖(chi s * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (p ^ 1)‖ = 2 * |Real.cos (s * Real.log p / 2)| := by
  rw [G_prime_pow s hp, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    chi_apply s one_ne_zero, Nat.cast_one, Complex.one_cpow, chi_eq_exp s hp.pos]
  set θ := s * Real.log p with hθ
  have h : (1 : ℂ) + Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (2 * Complex.cos ((θ / 2 : ℝ) : ℂ)) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    have e1 : ((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I := by
      push_cast
      ring
    have e2 : ((θ / 2 : ℝ) : ℂ) * Complex.I + -((θ / 2 : ℝ) : ℂ) * Complex.I = 0 := by ring
    rw [e1, e2, Complex.exp_zero, add_comm]
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

end OMA.Erdos1099Fourier

open OMA.Erdos1099Fourier in
theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H2
  intro loss k hk s y
  show |∑ d ∈ (Nat.lcmUpto k).divisors, Real.cos (s * (Real.log d - y))| ≤
    ((Nat.lcmUpto k).divisors.card : ℝ) *
      Real.exp (-(∑ p ∈ (Ioc k.sqrt k).filter Nat.Prime, (1 - |Real.cos (s * Real.log p / 2)|)))
  set L := Nat.lcmUpto k with hLdef
  have hL : L ≠ 0 := Nat.lcmUpto_ne_zero k
  set P := (Ioc k.sqrt k).filter Nat.Prime with hPdef
  set G := chi s * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) with hGdef
  have hGmult : G.IsMultiplicative := (chi_mult s).mul isMultiplicative_zeta.natCast
  -- step A
  have hA : |∑ d ∈ L.divisors, Real.cos (s * (Real.log d - y))| ≤ ‖G L‖ := by
    have hsum : (∑ d ∈ L.divisors, Real.cos (s * (Real.log d - y))) =
        (Complex.exp (((-(s * y)) : ℝ) * Complex.I) * G L).re := by
      rw [hGdef, coe_mul_zeta_apply, Finset.mul_sum, Complex.re_sum]
      apply sum_congr rfl
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [chi_eq_exp s hd0, ← Complex.exp_add]
      have e : ((-(s * y) : ℝ) : ℂ) * Complex.I + ((s * Real.log d : ℝ) : ℂ) * Complex.I =
          ((s * (Real.log d - y) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [e, Complex.exp_ofReal_mul_I_re]
    rw [hsum]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- step B
  have hprod : G L = ∏ p ∈ L.primeFactors, G (p ^ L.factorization p) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization G hGmult hL, Finsupp.prod,
      Nat.support_factorization]
  let w : ℕ → ℝ := fun p => if p ∈ P then |Real.cos (s * Real.log p / 2)| else 1
  have hPsub : P ⊆ L.primeFactors := by
    intro p hp
    rw [hLdef, Nat.primeFactors_lcmUpto, Nat.mem_primesLE]
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_Ioc.mp h1).2, h2⟩
  have hfac : ∀ p ∈ L.primeFactors,
      ‖G (p ^ L.factorization p)‖ ≤ ((L.factorization p : ℕ) + 1 : ℝ) * w p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hpP : p ∈ P
    · obtain ⟨h1, _⟩ := Finset.mem_filter.mp hpP
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp h1
      have he : L.factorization p = 1 := by
        rw [hLdef, Nat.factorization_lcmUpto k hpp, Nat.log_eq_one_iff']
        refine ⟨hhi, ?_⟩
        have := Nat.sqrt_lt'.mp hlo
        nlinarith
      rw [he, norm_G_prime s hpp]
      simp only [w, if_pos hpP]
      norm_num
    · simp only [w, if_neg hpP, mul_one]
      exact norm_G_le s hpp _
  have hB : ‖G L‖ ≤ (L.divisors.card : ℝ) * ∏ p ∈ P, |Real.cos (s * Real.log p / 2)| := by
    rw [hprod, norm_prod]
    calc ∏ p ∈ L.primeFactors, ‖G (p ^ L.factorization p)‖
        ≤ ∏ p ∈ L.primeFactors, (((L.factorization p : ℕ) + 1 : ℝ) * w p) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
      _ = (∏ p ∈ L.primeFactors, ((L.factorization p : ℕ) + 1 : ℝ)) *
            ∏ p ∈ L.primeFactors, w p := Finset.prod_mul_distrib
      _ = (L.divisors.card : ℝ) * ∏ p ∈ P, |Real.cos (s * Real.log p / 2)| := by
          congr 1
          · rw [Nat.card_divisors hL]
            push_cast
            rfl
          · simp only [w]
            rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hPsub]
  -- step C
  have hC : ∏ p ∈ P, |Real.cos (s * Real.log p / 2)| ≤
      Real.exp (-(∑ p ∈ P, (1 - |Real.cos (s * Real.log p / 2)|))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro p _
    have := Real.add_one_le_exp (-(1 - |Real.cos (s * Real.log p / 2)|))
    linarith
  have hD : (0 : ℝ) ≤ L.divisors.card := Nat.cast_nonneg _
  calc |∑ d ∈ L.divisors, Real.cos (s * (Real.log d - y))| ≤ ‖G L‖ := hA
    _ ≤ (L.divisors.card : ℝ) * ∏ p ∈ P, |Real.cos (s * Real.log p / 2)| := hB
    _ ≤ (L.divisors.card : ℝ) * Real.exp (-(∑ p ∈ P, (1 - |Real.cos (s * Real.log p / 2)|))) :=
        mul_le_mul_of_nonneg_left hC hD
