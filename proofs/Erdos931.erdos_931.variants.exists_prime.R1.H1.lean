import OMAReductions.R_Erdos931_erdos_931_variants_exists_prime_R1
import Mathlib

-- Step Erdos931.erdos_931.variants.exists_prime.R1.H1: hypothesis H1 of reduction Erdos931.erdos_931.variants.exists_prime.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! A prime in (n₂, n₂ + k₂] divides the second product, so it would divide some factor n₁ + i
of the first product, which is smaller than it. A common prime factor q divides some n₁ + i and
some n₂ + j, hence their positive difference, which is at most n₂ + k₂ - n₁ - 1. -/

open Finset

theorem OMA.solution : OMA.R_Erdos931_erdos_931_variants_exists_prime_R1.H1 := by
  intro k₁ k₂ n₁ n₂ hle heq
  have hne1 : (∏ i ∈ Icc 1 k₁, (n₁ + i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => by have := (mem_Icc.mp hi).1; omega
  have hne2 : (∏ j ∈ Icc 1 k₂, (n₂ + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => by have := (mem_Icc.mp hi).1; omega
  constructor
  · intro q hq h1 h2
    have hmem2 : q ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hq, ?_, hne2⟩
      have hj : q - n₂ ∈ Icc 1 k₂ := mem_Icc.mpr ⟨by omega, by omega⟩
      have := Finset.dvd_prod_of_mem (fun j => n₂ + j) hj
      rw [show n₂ + (q - n₂) = q by omega] at this
      exact this
    rw [← heq, Nat.mem_primeFactors] at hmem2
    obtain ⟨i, hi, hdvd⟩ := (hq.prime.dvd_finsetProd_iff _).mp hmem2.2.1
    have hi' := mem_Icc.mp hi
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro q hq1
    have hq2 : q ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := heq ▸ hq1
    rw [Nat.mem_primeFactors] at hq1 hq2
    obtain ⟨i, hi, hdi⟩ := (hq1.1.prime.dvd_finsetProd_iff _).mp hq1.2.1
    obtain ⟨j, hj, hdj⟩ := (hq1.1.prime.dvd_finsetProd_iff _).mp hq2.2.1
    have hi' := mem_Icc.mp hi
    have hj' := mem_Icc.mp hj
    have hsub : q ∣ (n₂ + j) - (n₁ + i) := Nat.dvd_sub hdj hdi
    have := Nat.le_of_dvd (by omega) hsub
    omega
