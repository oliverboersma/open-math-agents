import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R2.H2.R1.H1: hypothesis H1 of reduction Erdos1052.erdos_1052.R2.H2.R1
-- Credit: @ivillar. Uses Graham1052.core (Graham 1989), the accepted proof by @adammcarter
-- (proofs/Erdos1052.erdos_1052.R1.H1.lean) as inlined in the reduction file.
-- Strategy. For c = 9, u = 10 (2^a + 1). Then 5 divides the left side, so 5 is in S; removing 5
-- (factor 6 / 5) and adding 3 (factor 4 / 3) turns the c = 9 equation into Graham's balance
-- equation (2^a + 1) prod (p + 1) = 2^(a+1) prod p for T = (S minus 5) plus 3, hence a is 1, 2 or 6.

open Finset in
theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H1 := by
  unfold OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H1
  apply (Finset.range 10).finite_toSet.subset
  rintro a ⟨h5, S, -, -, hS, hE⟩
  have ha0 : a ≠ 0 := by omega
  have h2m : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  have hpf : (2 ^ a * 9).primeFactors = {2, 3} := by
    rw [Nat.primeFactors_mul h2m (by norm_num), Nat.primeFactors_prime_pow ha0 Nat.prime_two, h9,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    rfl
  have hf2 : (2 ^ a * 9).factorization 2 = a := by
    rw [Nat.factorization_mul h2m (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, h9,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_of_ne (by norm_num), add_zero]
  have hf3 : (2 ^ a * 9).factorization 3 = 2 := by
    rw [Nat.factorization_mul h2m (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_of_ne (by norm_num), h9,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  rw [hpf, Finset.prod_pair (by norm_num), hf2, hf3] at hE
  -- hE : (1 + 2 ^ a) * (1 + 3 ^ 2) * ∏ (1 + p) = 2 * (2 ^ a * 9) * ∏ p
  have hb2 : 2 ∣ 2 ^ a * 9 := dvd_mul_of_dvd_left (dvd_pow_self 2 ha0) 9
  have hb3 : 3 ∣ 2 ^ a * 9 := dvd_mul_of_dvd_right (by norm_num) _
  -- 5 ∈ S
  have h5S : 5 ∈ S := by
    have hd : 5 ∣ 2 * (2 ^ a * 9) * ∏ p ∈ S, p := by
      rw [← hE]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num) _) _
    have h5p : Nat.Prime 5 := by norm_num
    rcases (Nat.Prime.dvd_mul h5p).mp hd with h | h
    · exfalso
      rcases (Nat.Prime.dvd_mul h5p).mp h with h | h
      · omega
      · rcases (Nat.Prime.dvd_mul h5p).mp h with h | h
        · exact absurd (Nat.Prime.dvd_of_dvd_pow h5p h) (by norm_num)
        · omega
    · obtain ⟨p, hp, h5p'⟩ := (Prime.dvd_finsetProd_iff h5p.prime _).mp h
      have := (Nat.prime_dvd_prime_iff_eq h5p (hS p hp).1).mp h5p'
      exact this ▸ hp
  set T := S.erase 5 with hT
  have h3T : 3 ∉ T := fun h => (hS 3 (Finset.mem_of_mem_erase h)).2 hb3
  have hP : ∀ p ∈ insert 3 T, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨Nat.prime_three, by norm_num⟩
    · have := hS p (Finset.mem_of_mem_erase hp)
      exact ⟨this.1, fun h => this.2 (h ▸ hb2)⟩
  have e1 : ∏ p ∈ S, (1 + p) = 6 * ∏ p ∈ T, (p + 1) := by
    rw [← Finset.mul_prod_erase S _ h5S]
    congr 1
    exact Finset.prod_congr rfl fun p _ => add_comm 1 p
  have e2 : ∏ p ∈ S, p = 5 * ∏ p ∈ T, p := by
    rw [← Finset.mul_prod_erase S _ h5S]
  rw [e1, e2] at hE
  have E : (2 ^ a + 1) * ∏ p ∈ insert 3 T, (p + 1) = 2 ^ (a + 1) * ∏ p ∈ insert 3 T, p := by
    rw [Finset.prod_insert h3T, Finset.prod_insert h3T, pow_succ]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 15 by norm_num)
    calc 15 * ((2 ^ a + 1) * ((3 + 1) * ∏ p ∈ T, (p + 1)))
        = (1 + 2 ^ a) * (1 + 3 ^ 2) * (6 * ∏ p ∈ T, (p + 1)) := by ring
      _ = 2 * (2 ^ a * 9) * (5 * ∏ p ∈ T, p) := hE
      _ = 15 * (2 ^ a * 2 * (3 * ∏ p ∈ T, p)) := by ring
  rcases OMA.R_Erdos1052_erdos_1052_R2_H2_R1.Graham1052.core hP E (by omega) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
