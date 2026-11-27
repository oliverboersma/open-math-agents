import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1
import Mathlib

-- Step Erdos820.erdos_820.variants.erdos_lower.R1.H2: hypothesis H2 of reduction Erdos820.erdos_820.variants.erdos_lower.R1
-- Credit: @ivillar

/-!
# The primes `p` with `p - 1 ∣ n` multiply to less than `H n ^ 2`

Take `k < l = H n` with `k ^ n - 1` and `l ^ n - 1` coprime. A prime `p` with `p - 1 ∣ n` dividing
neither `k` nor `l` would divide both `k ^ n - 1` and `l ^ n - 1` by Fermat's little theorem. So
every such prime divides `k * l`, hence so does their product, and `k * l < l ^ 2`.
-/

namespace Erdos820ProdStep

theorem prod_lt : ∀ n : ℕ, 1 ≤ n →
    (∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n), p) <
      Erdos820.H n ^ 2 := by
  intro n hn
  obtain ⟨k, hk2, hkl, hcop⟩ := Erdos820.H_spec hn
  have key : ∀ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n),
      p ∣ k * Erdos820.H n := by
    intro p hp
    obtain ⟨-, hpp, hdvd⟩ := Finset.mem_filter.mp hp
    by_contra hnd
    have hk : ¬ p ∣ k := fun h => hnd (h.mul_right _)
    have hl : ¬ p ∣ Erdos820.H n := fun h => hnd (h.mul_left _)
    have aux : ∀ a : ℕ, ¬ p ∣ a → p ∣ a ^ n - 1 := by
      intro a ha
      have hc : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hpp).mpr ha).symm
      have h1 : a ^ (p - 1) ≡ 1 [MOD p] := by
        have h := Nat.ModEq.pow_totient hc
        rwa [Nat.totient_prime hpp] at h
      obtain ⟨m, hm⟩ := hdvd
      have h2 : a ^ n ≡ 1 [MOD p] := by
        rw [hm, pow_mul]
        simpa using h1.pow m
      have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero p))
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ ha0)).mp h2.symm
    have h := Nat.dvd_gcd (aux k hk) (aux _ hl)
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h)
  have hdiv : (∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n), p) ∣
      k * Erdos820.H n :=
    Finset.prod_primes_dvd (k * Erdos820.H n)
      (fun p hp => (Finset.mem_filter.mp hp).2.1.prime) key
  have hl0 : 0 < Erdos820.H n := by omega
  calc (∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n), p)
      ≤ k * Erdos820.H n := Nat.le_of_dvd (Nat.mul_pos (by omega) hl0) hdiv
    _ < Erdos820.H n * Erdos820.H n := Nat.mul_lt_mul_of_pos_right hkl hl0
    _ = Erdos820.H n ^ 2 := (sq _).symm

end Erdos820ProdStep

theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H2 :=
  Erdos820ProdStep.prod_lt
