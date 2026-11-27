import OMAReductions.R_Erdos779_erdos_779_R1
import Mathlib

-- Step Erdos779.erdos_779.R1.H2: hypothesis H2 of reduction Erdos779.erdos_779.R1
-- Credit: @ivillar. Witnesses p = 5, 7, 13, 23, 17, 19, 23, 37, 61, 67 for n = 1..10; the three
-- largest values P + p are certified prime with Lucas (Pratt) certificates via lucas_primality.

/-! Finite check of Deaconescu's prime pair for the first ten indices. -/

open Finset Nat

namespace P7E779H2


lemma nthp {k p : ℕ} (hp : p.Prime) (hc : Nat.count Nat.Prime p = k) : nth Nat.Prime k = p :=
  hc ▸ Nat.nth_count hp

lemma c0 : nth Nat.Prime 0 = 2 := nthp (by norm_num) (by decide)
lemma c1 : nth Nat.Prime 1 = 3 := nthp (by norm_num) (by decide)
lemma c2 : nth Nat.Prime 2 = 5 := nthp (by norm_num) (by decide)
lemma c3 : nth Nat.Prime 3 = 7 := nthp (by norm_num) (by decide)
lemma c4 : nth Nat.Prime 4 = 11 := nthp (by norm_num) (by decide)
lemma c5 : nth Nat.Prime 5 = 13 := nthp (by norm_num) (by decide)
lemma c6 : nth Nat.Prime 6 = 17 := nthp (by norm_num) (by decide)
lemma c7 : nth Nat.Prime 7 = 19 := nthp (by norm_num) (by decide)
lemma c8 : nth Nat.Prime 8 = 23 := nthp (by norm_num) (by decide)
lemma c9 : nth Nat.Prime 9 = 29 := nthp (by norm_num) (by decide)
lemma c10 : nth Nat.Prime 10 = 31 := nthp (by norm_num) (by decide)

lemma prime_2 : Nat.Prime 2 := by norm_num

lemma prime_3 : Nat.Prime 3 := by norm_num

lemma prime_5 : Nat.Prime 5 := by norm_num

lemma prime_11 : Nat.Prime 11 := by norm_num

lemma prime_37 : Nat.Prime 37 := by norm_num

lemma prime_223 : Nat.Prime 223 := by norm_num

lemma prime_263 : Nat.Prime 263 := by norm_num

lemma prime_311 : Nat.Prime 311 := by norm_num

lemma prime_2333 : Nat.Prime 2333 := by norm_num

lemma prime_2677 : Nat.Prime 2677 := by norm_num

lemma prime_3821 : Nat.Prime 3821 := by norm_num

lemma prime_8951 : Nat.Prime 8951 := by norm_num

lemma prime_30047 : Nat.Prime 30047 := by norm_num

lemma prime_510529 : Nat.Prime 510529 := by norm_num

lemma prime_9699713 : Nat.Prime 9699713 := by norm_num

lemma prime_4885523 : Nat.Prime 4885523 := by norm_num

lemma prime_223092907 : Nat.Prime 223092907 := by
  apply lucas_primality 223092907 2
  · change (2 : ZMod 223092907) ^ 223092906 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (223092907 : ℕ) - 1 = 2 ^ 1 * (3 ^ 1 * (37 ^ 1 * (263 ^ 1 * (3821 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 223092907) ^ 111546453 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (2 : ZMod 223092907) ^ 74364302 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_37 h
      subst r
      change (2 : ZMod 223092907) ^ 6029538 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_263 h
      subst r
      change (2 : ZMod 223092907) ^ 848262 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3821 h
      subst r
      change (2 : ZMod 223092907) ^ 58386 ≠ 1
      reduce_mod_char
      decide

lemma prime_6469693291 : Nat.Prime 6469693291 := by
  apply lucas_primality 6469693291 3
  · change (3 : ZMod 6469693291) ^ 6469693290 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (6469693291 : ℕ) - 1 = 2 ^ 1 * (3 ^ 3 * (5 ^ 1 * (2677 ^ 1 * (8951 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (3 : ZMod 6469693291) ^ 3234846645 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (3 : ZMod 6469693291) ^ 2156564430 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_5 h
      subst r
      change (3 : ZMod 6469693291) ^ 1293938658 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2677 h
      subst r
      change (3 : ZMod 6469693291) ^ 2416770 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_8951 h
      subst r
      change (3 : ZMod 6469693291) ^ 722790 ≠ 1
      reduce_mod_char
      decide

lemma prime_200560490197 : Nat.Prime 200560490197 := by
  apply lucas_primality 200560490197 2
  · change (2 : ZMod 200560490197) ^ 200560490196 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (200560490197 : ℕ) - 1 = 2 ^ 2 * (3 ^ 1 * (11 ^ 1 * (311 ^ 1 * (4885523 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 200560490197) ^ 100280245098 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (2 : ZMod 200560490197) ^ 66853496732 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_11 h
      subst r
      change (2 : ZMod 200560490197) ^ 18232771836 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_311 h
      subst r
      change (2 : ZMod 200560490197) ^ 644889036 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_4885523 h
      subst r
      change (2 : ZMod 200560490197) ^ 41052 ≠ 1
      reduce_mod_char
      decide

end P7E779H2

open P7E779H2

theorem OMA.solution : OMA.R_Erdos779_erdos_779_R1.H2 := by
  unfold OMA.R_Erdos779_erdos_779_R1.H2
  intro n h1 h10
  interval_cases n <;> simp only [prod_range_succ, prod_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
  · exact ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨23, by norm_num, (by convert prime_2333 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, (by convert prime_30047 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨19, by norm_num, (by convert prime_510529 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨23, by norm_num, (by convert prime_9699713 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, (by convert prime_223092907 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨61, by norm_num, (by convert prime_6469693291 using 1; norm_num), by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, (by convert prime_200560490197 using 1; norm_num), by norm_num, by norm_num⟩

