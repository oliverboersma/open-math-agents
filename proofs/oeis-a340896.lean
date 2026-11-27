import OMAStatements.S_oeis_a340896
import Mathlib

namespace OMAA340896Helpers

theorem key (S : Finset ℕ) (f : ℕ → ℕ) :
    2 * (∏ p ∈ S, (f p + 1)) ≤ (∏ p ∈ S, (2 * f p + 1)) + 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hP : 1 ≤ ∏ p ∈ T, (f p + 1) := Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    nlinarith [Nat.mul_le_mul_left (2 * f a + 1) ih, Nat.mul_le_mul_left (f a) hP]

theorem strict (S : Finset ℕ) (f : ℕ → ℕ) (hS : 2 ≤ S.card) (hf : ∀ p ∈ S, 1 ≤ f p) :
    2 * (∏ p ∈ S, (f p + 1)) ≤ ∏ p ∈ S, (2 * f p + 1) := by
  obtain ⟨a, haS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hT : 1 ≤ (S.erase a).card := by rw [Finset.card_erase_of_mem haS]; omega
  obtain ⟨b, hbT⟩ : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
  have hb : 1 ≤ f b := hf b (Finset.mem_of_mem_erase hbT)
  have ha1 : 1 ≤ f a := hf a haS
  rw [← Finset.insert_erase haS, Finset.prod_insert (Finset.notMem_erase a S),
    Finset.prod_insert (Finset.notMem_erase a S)]
  have ih := key (S.erase a) f
  have hP2 : 2 ≤ ∏ p ∈ S.erase a, (f p + 1) := by
    have hd : f b + 1 ∣ ∏ p ∈ S.erase a, (f p + 1) := Finset.dvd_prod_of_mem _ hbT
    have hpos : 0 < ∏ p ∈ S.erase a, (f p + 1) := Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    have := Nat.le_of_dvd hpos hd
    omega
  nlinarith [Nat.mul_le_mul_left (2 * f a + 1) ih, Nat.mul_le_mul_left (f a) hP2]

theorem card_sq (n : ℕ) (hn : n ≠ 0) :
    (n ^ 2).divisors.card = ∏ p ∈ n.primeFactors, (2 * n.factorization p + 1) := by
  rw [Nat.card_divisors (pow_ne_zero 2 hn), Nat.primeFactors_pow n two_ne_zero]
  simp [Nat.factorization_pow]

end OMAA340896Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a340896.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  simp only [OMA.S_oeis_a340896.row, Set.mem_setOf_eq]
  have h1 : 0 < n ^ 2 := by positivity
  have h2 : n ∣ n ^ 2 := dvd_pow_self n two_ne_zero
  rw [OMAA340896Helpers.card_sq n hn0, Nat.card_divisors hn0]
  constructor
  · rintro ⟨-, -, h⟩
    by_contra hne
    have hc0 : n.primeFactors.card ≠ 0 := by
      intro hc
      rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at hc
      rcases hc with hc | hc
      · exact hn0 hc
      · exact hne ⟨2, 0, Nat.prime_two, by simp [hc]⟩
    have hc1 : n.primeFactors.card ≠ 1 := by
      intro hc
      rw [← isPrimePow_iff_card_primeFactors_eq_one, isPrimePow_nat_iff] at hc
      obtain ⟨p, k, hp, -, hk⟩ := hc
      exact hne ⟨p, k, hp, hk.symm⟩
    have hf : ∀ p ∈ n.primeFactors, 1 ≤ n.factorization p := by
      intro p hp
      rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
      omega
    have := OMAA340896Helpers.strict n.primeFactors n.factorization (by omega) hf
    omega
  · rintro ⟨p, e, hp, rfl⟩
    refine ⟨h1, h2, ?_⟩
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.primeFactors_prime_pow he.ne' hp]
      simp [hp.factorization_self]
      omega
