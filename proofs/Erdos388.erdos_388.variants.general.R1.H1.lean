import OMAReductions.R_Erdos388_erdos_388_variants_general_R1
import Mathlib

-- Step Erdos388.erdos_388.variants.general.R1.H1: hypothesis H1 of reduction Erdos388.erdos_388.variants.general.R1
-- Credit: @ivillar

/-!
Every prime in `(m₂, m₂ + k₂]` divides the second product, hence `a` times the first product,
whose factors are all at most `m₂`; so it divides `a`. Bertrand's postulate then bounds `k₂`.
-/
open Finset

namespace F2E388

theorem small : ∀ a b m₁ k₁ m₂ k₂ : ℕ, 0 < a → 0 < b → 2 < k₁ → 2 < k₂ → m₁ + k₁ ≤ m₂ →
    a * (∏ i ∈ Icc 1 k₁, (m₁ + i)) = b * (∏ j ∈ Icc 1 k₂, (m₂ + j)) →
    (m₂ < a → k₂ ≤ a * a ^ a) ∧
    (a ≤ m₂ → k₂ < m₂ ∧ ∀ p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors, p ≤ m₂) := by
  intro a b m₁ k₁ m₂ k₂ ha hb hk₁ hk₂ hm heq
  -- a prime dividing the second product divides `a` or is at most `m₂`
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) → p ∣ a ∨ p ≤ m₂ := by
    intro p hp hpd
    have h1 : p ∣ a * (∏ i ∈ Icc 1 k₁, (m₁ + i)) := heq ▸ Dvd.dvd.mul_left hpd b
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact Or.inl h
    · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
      have hi' := mem_Icc.mp hi
      have hle : p ≤ m₁ + i := Nat.le_of_dvd (by omega) hpi
      exact Or.inr (by omega)
  -- every prime in `(m₂, m₂ + k₂]` divides `a`
  have hstar : ∀ p : ℕ, p.Prime → m₂ < p → p ≤ m₂ + k₂ → p ∣ a := by
    intro p hp h1 h2
    have hmem : p - m₂ ∈ Icc 1 k₂ := mem_Icc.mpr ⟨by omega, by omega⟩
    have hpd : p ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) := by
      have h := dvd_prod_of_mem (fun j => m₂ + j) hmem
      have e : m₂ + (p - m₂) = p := by omega
      simpa [e] using h
    rcases hdiv p hp hpd with h | h
    · exact h
    · omega
  constructor
  · intro hlt
    by_contra hcon
    have hbig : a * a ^ a < k₂ := not_le.mp hcon
    have hsq : a * a ≤ a * a ^ a := by
      apply Nat.mul_le_mul_left
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ a := Nat.pow_le_pow_right ha ha
    have h2a : 2 * a ≤ k₂ := by nlinarith
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul a (by omega)
    have hpa : p ∣ a := hstar p hp (by omega) (by omega)
    have := Nat.le_of_dvd ha hpa
    omega
  · intro hle
    constructor
    · by_contra hcon
      have hk : m₂ ≤ k₂ := not_lt.mp hcon
      obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m₂ (by omega)
      have hpa : p ∣ a := hstar p hp hp1 (by omega)
      have := Nat.le_of_dvd ha hpa
      omega
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      rcases hdiv p hpp hpd with h | h
      · exact le_trans (Nat.le_of_dvd ha h) hle
      · exact h

end F2E388

theorem OMA.solution : OMA.R_Erdos388_erdos_388_variants_general_R1.H1 :=
  F2E388.small
