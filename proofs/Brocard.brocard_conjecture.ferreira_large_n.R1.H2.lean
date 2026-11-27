import OMAReductions.R_Brocard_brocard_conjecture_ferreira_large_n_R1
import Mathlib

-- Step Brocard.brocard_conjecture.ferreira_large_n.R1.H2: hypothesis H2 of reduction Brocard.brocard_conjecture.ferreira_large_n.R1
-- Credit: @ivillar

/-!
# Four primes between consecutive prime squares

Let `p < q` be consecutive primes with `p ≥ 3`, so `q ≥ p + 2`. The hypothesis at `x = p`,
`x = p + 1` (both halves) and `x = p + 2` gives primes in the four disjoint intervals
`(p², p(p+1))`, `(p(p+1), (p+1)²)`, `((p+1)², (p+1)(p+2))`, `((p+1)(p+2), (p+2)²)`, all inside
`(p², q²)`.
-/

namespace BrocardFourPrimesStep

theorem four_primes : ∀ X : ℕ,
  (∀ x ≥ X, (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)) →
  ∀ n : ℕ, 1 ≤ n → X ≤ n.nth Nat.Prime →
    4 ≤ ((Finset.Ioo ((n.nth Nat.Prime) ^ 2) (((n + 1).nth Nat.Prime) ^ 2)).filter
      Nat.Prime).card := by
  intro X hX n hn hXp
  have hpp : (n.nth Nat.Prime).Prime := Nat.prime_nth_prime n
  have hqp : ((n + 1).nth Nat.Prime).Prime := Nat.prime_nth_prime (n + 1)
  have hpq : n.nth Nat.Prime < (n + 1).nth Nat.Prime :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  have hp3 : 3 ≤ n.nth Nat.Prime := by
    have h1 : Nat.nth Nat.Prime 1 ≤ n.nth Nat.Prime :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hn
    rwa [Nat.nth_prime_one_eq_three] at h1
  generalize n.nth Nat.Prime = p at *
  generalize (n + 1).nth Nat.Prime = q at *
  have hq2 : p + 2 ≤ q := by
    by_contra hcon
    have hq1 : q = p + 1 := by omega
    have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left (by omega)
    have h2 : 2 ∣ q := by omega
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp h2
    omega
  obtain ⟨-, p1, hp1, hp1p⟩ := hX p hXp
  obtain ⟨⟨p2, hp2, hp2p⟩, p3, hp3', hp3p⟩ := hX (p + 1) (by omega)
  obtain ⟨⟨p4, hp4, hp4p⟩, -⟩ := hX (p + 2) (by omega)
  rw [Finset.mem_Ioo] at hp1 hp2 hp3' hp4
  have e1 : p * (p + 1) = p ^ 2 + p := by ring
  have e2 : (p + 1) * (p + 1 - 1) = p ^ 2 + p := by
    rw [Nat.add_sub_cancel]
    ring
  have e3 : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
  have e4 : (p + 1) * (p + 1 + 1) = p ^ 2 + 3 * p + 2 := by ring
  have e5 : (p + 2) * (p + 2 - 1) = p ^ 2 + 3 * p + 2 := by
    rw [show p + 2 - 1 = p + 1 by omega]
    ring
  have e6 : (p + 2) ^ 2 = p ^ 2 + 4 * p + 4 := by ring
  rw [e1] at hp1
  rw [e2, e3] at hp2
  rw [e3, e4] at hp3'
  rw [e5, e6] at hp4
  have hqq : p ^ 2 + 4 * p + 4 ≤ q ^ 2 := e6 ▸ Nat.pow_le_pow_left hq2 2
  have hsub : ({p1, p2, p3, p4} : Finset ℕ) ⊆ (Finset.Ioo (p ^ 2) (q ^ 2)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨hp1.1, by omega⟩, hp1p⟩
    · exact ⟨⟨by omega, by omega⟩, hp2p⟩
    · exact ⟨⟨by omega, by omega⟩, hp3p⟩
    · exact ⟨⟨by omega, by omega⟩, hp4p⟩
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · rw [Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  exact hcard ▸ Finset.card_le_card hsub

end BrocardFourPrimesStep

theorem OMA.solution : OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R1.H2 :=
  BrocardFourPrimesStep.four_primes
