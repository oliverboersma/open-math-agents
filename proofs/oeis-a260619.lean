import OMAStatements.S_oeis_a260619
import Mathlib.Tactic

namespace HyperfactorialDerivativeProof

open Finset OMA.S_oeis_a260619

private def primeTerm (n p : ℕ) : ℕ := n.factorization p * (n / p)

private lemma term_zero {n p : ℕ} (hp : p ∉ n.primeFactors) : primeTerm n p = 0 := by
  have hz : n.factorization p = 0 := by
    rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
  simp [primeTerm, hz]

/-- The part of a prime's contribution inherited from a is scaled by b. -/
private lemma scale_term (a b p : ℕ) :
    a.factorization p * (a * b / p) = b * primeTerm a p := by
  by_cases h : p ∈ a.primeFactors
  · have hd := Nat.dvd_of_mem_primeFactors h
    rw [Nat.mul_comm a b, Nat.mul_div_assoc b hd]
    unfold primeTerm
    ring
  · have hz : a.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    simp [primeTerm, hz]

/-- Summation can be enlarged to the prime divisors of any multiple. -/
private lemma sum_over {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    ∑ p ∈ s, primeTerm n p = arithmeticDerivative n := by
  exact (sum_subset hs (fun p _ hp => term_zero hp)).symm

private lemma derivative_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    arithmeticDerivative (a * b) = b * arithmeticDerivative a + a * arithmeticDerivative b := by
  let s := a.primeFactors ∪ b.primeFactors
  have split (p : ℕ) : primeTerm (a * b) p = b * primeTerm a p + a * primeTerm b p := by
    change (a * b).factorization p * (a * b / p) = _
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply, add_mul, scale_term]
    congr 1
    rw [Nat.mul_comm a b, scale_term]
  have h : (a * b).primeFactors = s := Nat.primeFactors_mul ha hb
  calc
    arithmeticDerivative (a * b) = ∑ p ∈ s, primeTerm (a * b) p := by rw [← h]; rfl
    _ = ∑ p ∈ s, (b * primeTerm a p + a * primeTerm b p) := sum_congr rfl fun p _ => split p
    _ = b * arithmeticDerivative a + a * arithmeticDerivative b := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum,
        sum_over (show a.primeFactors ⊆ s from subset_union_left),
        sum_over (show b.primeFactors ⊆ s from subset_union_right)]

private lemma derivative_power (a : ℕ) (ha : a ≠ 0) (e : ℕ) :
    arithmeticDerivative (a ^ (e + 1)) = (e + 1) * a ^ e * arithmeticDerivative a := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ a (e + 1), derivative_mul (pow_ne_zero _ ha) ha, ih, pow_succ]
    ring

private lemma hyperfactorial_ne_zero (n : ℕ) : hyperfactorial n ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih => exact mul_ne_zero ih (pow_ne_zero _ (Nat.succ_ne_zero n))

end HyperfactorialDerivativeProof

open OMA.S_oeis_a260619 HyperfactorialDerivativeProof

theorem OMA.solution : type_of% @OMA.S_oeis_a260619.main := by
  intro n
  induction n with
  | zero => simp [hyperfactorial, derivativeSum, arithmeticDerivative]
  | succ n ih =>
    have step := derivative_power (n + 1) (Nat.succ_ne_zero n) n
    rw [show hyperfactorial (n + 1) = hyperfactorial n * (n + 1) ^ (n + 1) from rfl,
      derivative_mul (hyperfactorial_ne_zero n) (pow_ne_zero _ (Nat.succ_ne_zero n)),
      step, ih]
    simp only [derivativeSum, Finset.sum_range_succ, Nat.succ_eq_add_one, pow_succ]
    ring
