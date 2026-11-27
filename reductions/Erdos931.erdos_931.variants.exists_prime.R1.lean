import FormalConjectures.ErdosProblems.«931»
import Mathlib.Algebra.BigOperators.Associated

/-!
A counterexample has no primes anywhere from the first start through
the last entry of the second block. All common prime divisors are at
most the largest difference between entries of the two blocks.
-/

namespace OMA.R_Erdos931_erdos_931_variants_exists_prime_R1

open Finset

def H1 : Prop :=
  ∀ k₁ k₂ n₁ n₂ : ℕ, n₁ + k₁ ≤ n₂ →
    (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors →
    (∀ q : ℕ, q.Prime → n₂ < q → q ≤ n₂ + k₂ → False) ∧
    ∀ q ∈ (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors, q ≤ n₂ + k₂ - n₁ - 1

def H2 : Prop :=
  ∀ k₁ k₂ n₁ n₂ : ℕ, k₂ ≤ k₁ → 3 ≤ k₂ → n₁ + k₁ ≤ n₂ →
    (∀ q : ℕ, n₁ ≤ q → q ≤ n₂ + k₂ → ¬ q.Prime) →
    (∀ q ∈ (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors, q ≤ n₂ + k₂ - n₁ - 1) →
    (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors ≠
      (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors

section Proof

theorem main : H1 → H2 → type_of% @Erdos931.erdos_931.variants.exists_prime := by
  intro supportBound smoothBlocks k₁ k₂ n₁ n₂ hk hkmin hOrder hSupport
  by_contra hNoPrime
  obtain ⟨hRight, hSmall⟩ := supportBound k₁ k₂ n₁ n₂ hOrder hSupport
  have hGap (p : ℕ) (h₁ : n₁ ≤ p) (h₂ : p ≤ n₂ + k₂) : ¬ p.Prime := by
    intro hp
    by_cases hpn₂ : p ≤ n₂
    · exact hNoPrime ⟨p, hp, h₁, hpn₂⟩
    · exact hRight p hp (lt_of_not_ge hpn₂) h₂
  exact smoothBlocks k₁ k₂ n₁ n₂ hk hkmin hOrder hGap hSmall hSupport

end Proof

end OMA.R_Erdos931_erdos_931_variants_exists_prime_R1
