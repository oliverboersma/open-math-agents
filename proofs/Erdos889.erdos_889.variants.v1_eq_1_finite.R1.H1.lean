import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1
import Mathlib

-- Step Erdos889.erdos_889.variants.v1_eq_1_finite.R1.H1: hypothesis H1 of reduction
-- Erdos889.erdos_889.variants.v1_eq_1_finite.R1
-- Credit: @ivillar. For k >= 1 the new prime factors of n + k are those above k; once n <= k^2 two of
-- them would exceed n + k; and a prime P > n gives v(n, P - n) >= 1.

/-! The finite window characterising v_1(n) = 1. -/

open Finset Nat

namespace P7E889H1

/-- For `k ≥ 1`, the new prime factors of `n + k` are exactly those exceeding `k`. -/
lemma v_eq (n k : ℕ) :
    Erdos889.v n k = ((n + k).primeFactors.filter (fun p ↦ k < p)).card := by
  unfold Erdos889.v
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  constructor
  · intro h
    by_contra hle
    replace hle := not_lt.mp hle
    apply h (k - p) (Finset.mem_range.mpr (by have := hpp.two_le; omega))
    have : n + k = n + (k - p) + p := by have := hpp.two_le; omega
    rw [this] at hpd
    exact (Nat.dvd_add_left (dvd_refl p)).mp hpd
  · intro hkp i hi hdvd
    have hik := Finset.mem_range.mp hi
    have h1 : p ∣ (n + k) - (n + i) := Nat.dvd_sub hpd hdvd
    rw [show n + k - (n + i) = k - i by omega] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega

/-- Beyond the square-root window, `n + k` has at most one prime factor above `k`. -/
lemma card_le_one_of_large (n k : ℕ) (hk : n ≤ k ^ 2) :
    ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  obtain ⟨hp1, hpk⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq1, hqk⟩ := Finset.mem_filter.mp hq
  have hpP := Nat.prime_of_mem_primeFactors hp1
  have hqP := Nat.prime_of_mem_primeFactors hq1
  have hn0 : n + k ≠ 0 := (Nat.mem_primeFactors.mp hp1).2.2
  have hmul : p * q ∣ n + k :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hpP hqP).mpr hpq)
      (Nat.dvd_of_mem_primeFactors hp1) (Nat.dvd_of_mem_primeFactors hq1)
  have hle := Nat.le_of_dvd (by omega) hmul
  have : (k + 1) * (k + 1) ≤ p * q := Nat.mul_le_mul hpk hqk
  nlinarith

lemma exists_one (n : ℕ) (hn : 0 < n) : ∃ k, 1 ≤ k ∧ 1 ≤ Erdos889.v n k := by
  obtain ⟨P, hP, hPp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨P - n, by omega, ?_⟩
  rw [v_eq, show n + (P - n) = P by omega]
  apply Finset.card_pos.mpr
  refine ⟨P, Finset.mem_filter.mpr ⟨?_, by omega⟩⟩
  exact Nat.mem_primeFactors.mpr ⟨hPp, dvd_refl P, hPp.ne_zero⟩

end P7E889H1

open P7E889H1

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1.H1 := by
  unfold OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1.H1
  intro n hn
  have key : Erdos889.v_l 1 n = 1 ↔ ∀ k, 1 ≤ k → Erdos889.v n k ≤ 1 := by
    unfold Erdos889.v_l
    constructor
    · intro h k hk
      have : (Erdos889.v n k : ℕ∞) ≤ 1 := by
        rw [← h]
        exact le_iSup₂ (f := fun k (_ : k ≥ 1) => (Erdos889.v n k : ℕ∞)) k hk
      exact_mod_cast this
    · intro h
      apply le_antisymm
      · apply iSup₂_le
        intro k hk
        exact_mod_cast h k hk
      · obtain ⟨k, hk, hv⟩ := exists_one n hn
        calc (1 : ℕ∞) ≤ (Erdos889.v n k : ℕ∞) := by exact_mod_cast hv
          _ ≤ _ := le_iSup₂ (f := fun k (_ : k ≥ 1) => (Erdos889.v n k : ℕ∞)) k hk
  rw [key]
  constructor
  · intro h k hk _
    rw [← v_eq]
    exact h k hk
  · intro h k hk
    rw [v_eq]
    by_cases hkn : k ^ 2 < n
    · exact h k hk hkn
    · exact card_le_one_of_large n k (by omega)

