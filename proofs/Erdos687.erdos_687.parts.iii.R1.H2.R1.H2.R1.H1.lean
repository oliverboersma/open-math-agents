import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1
import Mathlib

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1
-- Credit: @ivillar
-- H1 := ∃ c₀ > 0, ∀ x ≥ 2, c₀ / log x ≤ ∏_{p ≤ x prime} (1 - 1/p)   (a Mertens-type lower bound)
--
-- Proof outline (elementary, discrete):
--  1. Legendre: ∑_{p ≤ n} ⌊n/p⌋ log p ≤ log n! (via ∑_{d ∣ m} Λ d = log m), with log n! ≤ n log n
--     and Chebyshev θ(n) ≤ n log 4 (Mathlib) gives A(n) := ∑_{p ≤ n} log p / p ≤ log n + log 4.
--  2. Summation by parts as an induction on n: with G(n) := ∑_{p ≤ n} -log(1 - 1/p),
--     G(n) - A(n)/log n ≤ log log n - log log 2 + log 4/log 2 - log 4/log n + 1 - 1/n,
--     using 1 - 1/t ≤ log t to telescope log log n, and -log(1 - 1/p) ≤ 1/p + 1/(p(p-1)).
--  3. Hence G(x) ≤ log log x + C, and exponentiating gives the product bound with c₀ = exp(-C).

open Real Finset

namespace OMA.Mertens687
lemma log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ m ∈ Finset.Ioc 0 n, Real.log m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Ioc_succ_top (by omega)]
    push_cast
    ring

lemma sum_floor_log_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
  rw [log_factorial_eq]
  have key : ∀ m ∈ Finset.Ioc 0 n,
      ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p
        ≤ Real.log m := by
    intro m hm
    have hm0 : m ≠ 0 := by
      simp only [Finset.mem_Ioc] at hm
      omega
    rw [← ArithmeticFunction.vonMangoldt_sum]
    calc ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p
        = ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m),
            ArithmeticFunction.vonMangoldt p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime hp.1.2]
      _ ≤ ∑ i ∈ m.divisors, ArithmeticFunction.vonMangoldt i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp
            simp only [Nat.mem_divisors]
            exact ⟨hp.2, hm0⟩
          · intro i _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
  calc ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p
      = ∑ m ∈ Finset.Ioc 0 n,
          ∑ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (· ∣ m), Real.log p := by
        simp_rw [Finset.sum_filter (s := (Finset.range (n + 1)).filter Nat.Prime)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ m ∈ Finset.Ioc 0 n, Real.log m := Finset.sum_le_sum key

lemma theta_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h1 := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h1
  exact h1

lemma A_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log n + Real.log 4 := by
  have h1 := sum_floor_log_le n
  have h2 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have hle := Nat.factorial_le_pow n
    have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
          apply Real.log_le_log hpos
          exact_mod_cast hle
      _ = n * Real.log n := by rw [Real.log_pow]
  have h3 := theta_le n
  have h4 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n / p : ℕ) : ℝ) * Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
    have hdm := Nat.div_add_mod n p
    have hmod := Nat.mod_lt n hp'.pos
    have e1 : (n : ℝ) = p * (n / p : ℕ) + (n % p : ℕ) := by exact_mod_cast hdm.symm
    have e2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast hmod
    nlinarith
  have h5 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((n : ℝ) / p - 1) * Real.log p
      = n * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
        - ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h6 : (n : ℝ) * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p
      ≤ n * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left h6 hn'

lemma filter_succ (n : ℕ) :
    (Finset.range (n + 1 + 1)).filter Nat.Prime
      = if (n + 1).Prime then insert (n + 1) ((Finset.range (n + 1)).filter Nat.Prime)
        else (Finset.range (n + 1)).filter Nat.Prime := by
  rw [Finset.range_add_one (n := n + 1), Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (Finset.range (n + 1)).filter Nat.Prime := by
  simp

lemma step_bound (n : ℕ) (hn : 1 ≤ n) :
    -Real.log (1 - ((n + 1 : ℕ) : ℝ)⁻¹) - 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) - 1 / (n + 1 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  have e : (1 : ℝ) - ((n : ℝ) + 1)⁻¹ = n / (n + 1) := by field_simp; ring
  rw [e, Real.log_div hn'.ne' (by positivity)]
  have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  rw [Real.log_div (by positivity) hn'.ne'] at h
  have e2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by
    field_simp
    ring
  rw [e2] at h
  linarith

lemma main_ind (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
      - (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p) / Real.log n
      ≤ Real.log (Real.log n) - Real.log (Real.log 2) + Real.log 4 / Real.log 2
        - Real.log 4 / Real.log n + 1 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hP : (Finset.range (2 + 1)).filter Nat.Prime = {2} := by decide
    rw [hP, Finset.sum_singleton, Finset.sum_singleton]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlt : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    push_cast
    have e1 : (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    rw [e1, Real.log_inv]
    have e2 : Real.log 2 / 2 / Real.log 2 = 1 / 2 := by field_simp
    rw [e2]
    linarith
  | succ n hn ih =>
    set S := (Finset.range (n + 1)).filter Nat.Prime with hS
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hL' : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hLL : Real.log n < Real.log ((n : ℝ) + 1) := Real.log_lt_log (by linarith) (by linarith)
    have hA := A_le n (by omega)
    have hA0 : 0 ≤ ∑ p ∈ S, Real.log p / p := by
      apply Finset.sum_nonneg
      intro p hp
      have hp' : p.Prime := (Finset.mem_filter.mp hp).2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)) (Nat.cast_nonneg p)
    -- the increment
    have hinc : ∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
        - (∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, Real.log p / p) / Real.log ((n : ℝ) + 1)
        ≤ ∑ p ∈ S, -Real.log (1 - (p : ℝ)⁻¹) - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
          + (1 / (n : ℝ) - 1 / (n + 1 : ℝ)) := by
      rw [filter_succ]
      split_ifs with hpr
      · rw [Finset.sum_insert (not_mem_filter n), Finset.sum_insert (not_mem_filter n)]
        have hsb := step_bound n (by omega)
        have e : Real.log (((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) / Real.log ((n : ℝ) + 1)
            = 1 / ((n + 1 : ℕ) : ℝ) := by
          push_cast
          field_simp
        rw [add_div, e]
        linarith
      · have : (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / (n + 1 : ℝ) := by
          rw [div_sub_div _ _ (by positivity) (by positivity)]
          apply div_nonneg <;> nlinarith
        linarith
    -- the change of logarithm in the denominator
    have hden : (∑ p ∈ S, Real.log p / p) / Real.log n - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
        ≤ Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)
          + Real.log 4 / Real.log n - Real.log 4 / Real.log ((n : ℝ) + 1) := by
      have hd : 0 ≤ 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ hL.ne' hL'.ne']
        apply div_nonneg <;> nlinarith
      have h1 : (∑ p ∈ S, Real.log p / p) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))
          ≤ (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hA hd
      have h2 : 1 - (Real.log ((n : ℝ) + 1) / Real.log n)⁻¹ ≤ Real.log (Real.log ((n : ℝ) + 1) / Real.log n) :=
        Real.one_sub_inv_le_log_of_pos (by positivity)
      rw [Real.log_div hL'.ne' hL.ne', inv_div] at h2
      have e3 : (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))
          = (1 - Real.log n / Real.log ((n : ℝ) + 1)) + (Real.log 4 / Real.log n - Real.log 4 / Real.log ((n : ℝ) + 1)) := by
        field_simp
      have e4 : (∑ p ∈ S, Real.log p / p) / Real.log n - (∑ p ∈ S, Real.log p / p) / Real.log ((n : ℝ) + 1)
          = (∑ p ∈ S, Real.log p / p) * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by ring
      rw [e4]
      linarith
    push_cast
    linarith

theorem mertens_lower : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →
    c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.exp (-(1 + Real.log 4 / Real.log 2
    + (-Real.log (Real.log 2) + Real.log 4 / Real.log 2 + 1))), Real.exp_pos _, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hind := main_ind x hx
  have hA := A_le x (by omega)
  have hL2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hAdiv : (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p / p) / Real.log x
      ≤ 1 + Real.log 4 / Real.log 2 := by
    rw [div_le_iff₀ hL]
    have h1 : Real.log 4 ≤ Real.log 4 / Real.log 2 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      nlinarith
    nlinarith
  have h4 : 0 ≤ Real.log 4 / Real.log x := div_nonneg hK hL.le
  have h5 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hG : ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹)
      ≤ Real.log (Real.log x) + (1 + Real.log 4 / Real.log 2
        + (-Real.log (Real.log 2) + Real.log 4 / Real.log 2 + 1)) := by
    linarith
  have hfac_pos : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    have h2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith
  have hprod_pos : 0 < ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hfac_pos
  have hlogprod : Real.log (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
      = -∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, -Real.log (1 - (p : ℝ)⁻¹) := by
    rw [Real.log_prod (fun p hp => (hfac_pos p hp).ne'), Finset.sum_neg_distrib, neg_neg]
  rw [← Real.log_le_log_iff (div_pos (Real.exp_pos _) hL) hprod_pos, hlogprod,
    Real.log_div (Real.exp_pos _).ne' hL.ne', Real.log_exp]
  linarith

end OMA.Mertens687

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1
  exact OMA.Mertens687.mertens_lower
