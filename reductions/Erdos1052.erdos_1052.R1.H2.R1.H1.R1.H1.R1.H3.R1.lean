import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1
-- Credit: @adammcarter
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1 (3 is the only repeated
-- odd prime, its exponent e is above 200 and no odd multiple of the 100 values D100) by pushing
-- the exponent sieve of round 6 from 200 to 500.  Proving the two H proves the step.
--
-- Notation: n unitary perfect with 3 the only repeated odd prime, e = n.factorization 3,
-- a = padicValNat 2 n.  A number x is an ODD MULTIPLE of d when x mod 2d = d; then 3^d + 1
-- divides 3^e + 1 (for x = e).
--
-- PROVED BELOW (no hypothesis needed): for each of the 90 values d listed in H1 above 200
-- (201 <= d <= 500), e is no odd multiple of d (kill3_e<d>, collected in core3_residues_new).
-- Method (as in round 6): every odd prime of 3^d + 1 is a simple prime of n with source 3^e + 1,
-- and the odd primes of p + 1 for a simple prime p are again simple primes; the chains found give
-- an odd prime with two sources or a square, contradicting the balance equation
-- (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p.  Witness primes above 4.3 * 10^7 are
-- certified by the Lucas test.  Factorizations of 3^d + 1 were taken from factordb and checked
-- here: Lean re-checks every divisibility and primality.
-- Consequently 200 < e <= 500 forces e to be one of 359, 362, 446, 458, 487, 499 (exponent_sieve_new).
--
-- H1 (OPEN): e > 500, e no odd multiple of any of the 190 values listed, a no odd multiple of DA.
-- H2 (OPEN): e is one of 359, 362, 446, 458, 487, 499, a no odd multiple of DA.
-- No known unitary perfect number satisfies the hypotheses of H1 or H2 (90 has e = 2).
-- This narrows e; it does not bound a.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 above 500, e no odd multiple of any d in the first set (D100 and
-- the 90 new values), and a no odd multiple of any d in DA (the second set).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    500 < n.factorization 3 →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38,
        39, 41, 43, 44, 46, 47, 49, 52, 53, 55, 57, 58, 59, 61, 62, 64, 65, 67, 68, 71, 73, 74,
        76, 77, 79, 82, 83, 86, 89, 91, 92, 94, 95, 97, 101, 103, 106, 107, 109, 113, 116, 118,
        121, 122, 124, 127, 128, 131, 133, 134, 137, 139, 142, 143, 146, 148, 149, 151, 157,
        158, 163, 164, 166, 167, 169, 172, 173, 178, 179, 181, 188, 191, 193, 194, 197, 199,
        202, 206, 209, 211, 212, 214, 218, 223, 226, 227, 229, 233, 236, 239, 241, 244, 247,
        251, 254, 256, 257, 262, 263, 268, 269, 271, 274, 277, 278, 281, 283, 284, 292, 293,
        298, 302, 307, 311, 313, 314, 316, 317, 326, 331, 332, 334, 337, 346, 347, 349, 353,
        356, 358, 361, 367, 373, 379, 382, 383, 386, 388, 389, 394, 397, 398, 401, 404, 409,
        412, 419, 421, 422, 428, 431, 433, 436, 439, 443, 449, 452, 454, 457, 461, 463, 466,
        467, 478, 479, 482, 491} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 359, 362, 446, 458, 487, 499, and a no odd multiple of any d in DA.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 359 ∨ n.factorization 3 = 362 ∨ n.factorization 3 = 446 ∨ n.factorization 3 = 458 ∨ n.factorization 3 = 487 ∨ n.factorization 3 = 499) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

theorem prime_1189912513 : Nat.Prime 1189912513 := by
  refine lucas_primality 1189912513 (5 : ZMod 1189912513) ?_ (fun q hq hd => ?_)
  · rw [show 1189912513 - 1 = 1189912512 from by norm_num]
    reduce_mod_char
  · have e : 1189912513 - 1 = [2 ^ 6, 3 ^ 1, 43 ^ 1, 101 ^ 1, 1427 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1189912513 - 1) / 2 = 594956256 from by norm_num]
      have h2 : (5 : ZMod 1189912513) ^ 594956256 = ((1189912512 : ℕ) : ZMod 1189912513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1189912513 - 1) / 3 = 396637504 from by norm_num]
      have h2 : (5 : ZMod 1189912513) ^ 396637504 = ((809372861 : ℕ) : ZMod 1189912513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1189912513 - 1) / 43 = 27672384 from by norm_num]
      have h2 : (5 : ZMod 1189912513) ^ 27672384 = ((294487016 : ℕ) : ZMod 1189912513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1189912513 - 1) / 101 = 11781312 from by norm_num]
      have h2 : (5 : ZMod 1189912513) ^ 11781312 = ((879307714 : ℕ) : ZMod 1189912513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1189912513 - 1) / 1427 = 833856 from by norm_num]
      have h2 : (5 : ZMod 1189912513) ^ 833856 = ((605708692 : ℕ) : ZMod 1189912513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1522395676033 : Nat.Prime 1522395676033 := by
  refine lucas_primality 1522395676033 (10 : ZMod 1522395676033) ?_ (fun q hq hd => ?_)
  · rw [show 1522395676033 - 1 = 1522395676032 from by norm_num]
    reduce_mod_char
  · have e : 1522395676033 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 1, 11 ^ 1, 103 ^ 1, 499883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 2 = 761197838016 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 761197838016 = ((1522395676032 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 3 = 507465225344 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 507465225344 = ((220558719820 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 7 = 217485096576 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 217485096576 = ((773656745092 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 11 = 138399606912 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 138399606912 = ((1092813695899 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 103 = 14780540544 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 14780540544 = ((182310077647 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1522395676033 - 1) / 499883 = 3045504 from by norm_num]
      have h2 : (10 : ZMod 1522395676033) ^ 3045504 = ((566950246629 : ℕ) : ZMod 1522395676033) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1079398849 : Nat.Prime 1079398849 := by
  refine lucas_primality 1079398849 (23 : ZMod 1079398849) ?_ (fun q hq hd => ?_)
  · rw [show 1079398849 - 1 = 1079398848 from by norm_num]
    reduce_mod_char
  · have e : 1079398849 - 1 = [2 ^ 6, 3 ^ 1, 11 ^ 1, 53 ^ 1, 9643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1079398849 - 1) / 2 = 539699424 from by norm_num]
      have h2 : (23 : ZMod 1079398849) ^ 539699424 = ((1079398848 : ℕ) : ZMod 1079398849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1079398849 - 1) / 3 = 359799616 from by norm_num]
      have h2 : (23 : ZMod 1079398849) ^ 359799616 = ((558823754 : ℕ) : ZMod 1079398849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1079398849 - 1) / 11 = 98127168 from by norm_num]
      have h2 : (23 : ZMod 1079398849) ^ 98127168 = ((28051985 : ℕ) : ZMod 1079398849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1079398849 - 1) / 53 = 20366016 from by norm_num]
      have h2 : (23 : ZMod 1079398849) ^ 20366016 = ((388701650 : ℕ) : ZMod 1079398849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1079398849 - 1) / 9643 = 111936 from by norm_num]
      have h2 : (23 : ZMod 1079398849) ^ 111936 = ((162048567 : ℕ) : ZMod 1079398849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_74950313 : Nat.Prime 74950313 := by
  refine lucas_primality 74950313 (3 : ZMod 74950313) ?_ (fun q hq hd => ?_)
  · rw [show 74950313 - 1 = 74950312 from by norm_num]
    reduce_mod_char
  · have e : 74950313 - 1 = [2 ^ 3, 31 ^ 2, 9749 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74950313 - 1) / 2 = 37475156 from by norm_num]
      have h2 : (3 : ZMod 74950313) ^ 37475156 = ((74950312 : ℕ) : ZMod 74950313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74950313 - 1) / 31 = 2417752 from by norm_num]
      have h2 : (3 : ZMod 74950313) ^ 2417752 = ((58691563 : ℕ) : ZMod 74950313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (74950313 - 1) / 9749 = 7688 from by norm_num]
      have h2 : (3 : ZMod 74950313) ^ 7688 = ((57161086 : ℕ) : ZMod 74950313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_149900627 : Nat.Prime 149900627 := by
  refine lucas_primality 149900627 (2 : ZMod 149900627) ?_ (fun q hq hd => ?_)
  · rw [show 149900627 - 1 = 149900626 from by norm_num]
    reduce_mod_char
  · have e : 149900627 - 1 = [2 ^ 1, 74950313 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149900627 - 1) / 2 = 74950313 from by norm_num]
      have h2 : (2 : ZMod 149900627) ^ 74950313 = ((149900626 : ℕ) : ZMod 149900627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_74950313).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149900627 - 1) / 74950313 = 2 from by norm_num]
      have h2 : (2 : ZMod 149900627) ^ 2 = ((4 : ℕ) : ZMod 149900627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4032176417327894814764968543 : Nat.Prime 4032176417327894814764968543 := by
  refine lucas_primality 4032176417327894814764968543 (5 : ZMod 4032176417327894814764968543) ?_ (fun q hq hd => ?_)
  · rw [show 4032176417327894814764968543 - 1 = 4032176417327894814764968542 from by norm_num]
    reduce_mod_char
  · have e : 4032176417327894814764968543 - 1 = [2 ^ 1, 3 ^ 1, 229 ^ 1, 379 ^ 1, 733 ^ 1, 150077 ^ 1, 469561 ^ 1, 149900627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 2 = 2016088208663947407382484271 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 2016088208663947407382484271 = ((4032176417327894814764968542 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 3 = 1344058805775964938254989514 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 1344058805775964938254989514 = ((3061188880890187144461548183 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 229 = 17607757280907837619060998 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 17607757280907837619060998 = ((1833541943763726837030761181 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 379 = 10638987908516872862176698 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 10638987908516872862176698 = ((1479917599155344133641854313 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 733 = 5500922806722912434877174 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 5500922806722912434877174 = ((3841585313981125436415294695 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 150077 = 26867384191634259845046 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 26867384191634259845046 = ((763123736023822518262487074 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 469561 = 8587119495290057766222 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 8587119495290057766222 = ((3510296342167043757633660796 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_149900627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4032176417327894814764968543 - 1) / 149900627 = 26898996341942551146 from by norm_num]
      have h2 : (5 : ZMod 4032176417327894814764968543) ^ 26898996341942551146 = ((1790530719021578946911549278 : ℕ) : ZMod 4032176417327894814764968543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47135677 : Nat.Prime 47135677 := by
  refine lucas_primality 47135677 (2 : ZMod 47135677) ?_ (fun q hq hd => ?_)
  · rw [show 47135677 - 1 = 47135676 from by norm_num]
    reduce_mod_char
  · have e : 47135677 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 61 ^ 1, 9199 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47135677 - 1) / 2 = 23567838 from by norm_num]
      have h2 : (2 : ZMod 47135677) ^ 23567838 = ((47135676 : ℕ) : ZMod 47135677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47135677 - 1) / 3 = 15711892 from by norm_num]
      have h2 : (2 : ZMod 47135677) ^ 15711892 = ((35459124 : ℕ) : ZMod 47135677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47135677 - 1) / 7 = 6733668 from by norm_num]
      have h2 : (2 : ZMod 47135677) ^ 6733668 = ((5927697 : ℕ) : ZMod 47135677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47135677 - 1) / 61 = 772716 from by norm_num]
      have h2 : (2 : ZMod 47135677) ^ 772716 = ((39254487 : ℕ) : ZMod 47135677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47135677 - 1) / 9199 = 5124 from by norm_num]
      have h2 : (2 : ZMod 47135677) ^ 5124 = ((19897378 : ℕ) : ZMod 47135677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_42124768369936320790693 : Nat.Prime 42124768369936320790693 := by
  refine lucas_primality 42124768369936320790693 (2 : ZMod 42124768369936320790693) ?_ (fun q hq hd => ?_)
  · rw [show 42124768369936320790693 - 1 = 42124768369936320790692 from by norm_num]
    reduce_mod_char
  · have e : 42124768369936320790693 - 1 = [2 ^ 2, 3 ^ 2, 79 ^ 1, 239 ^ 1, 7549 ^ 1, 174169 ^ 1, 47135677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 2 = 21062384184968160395346 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 21062384184968160395346 = ((42124768369936320790692 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 3 = 14041589456645440263564 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 14041589456645440263564 = ((22150305710103629778003 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 79 = 533224916075143301148 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 533224916075143301148 = ((15085531315695758588144 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 239 = 176254260962076656028 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 176254260962076656028 = ((11208985935610236614172 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 7549 = 5580178615702254708 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 5580178615702254708 = ((801904064700566398520 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 174169 = 241861458525548868 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 241861458525548868 = ((29974621248388273828545 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47135677).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (42124768369936320790693 - 1) / 47135677 = 893691807374196 from by norm_num]
      have h2 : (2 : ZMod 42124768369936320790693) ^ 893691807374196 = ((5625177303481430072552 : ℕ) : ZMod 42124768369936320790693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_123450337 : Nat.Prime 123450337 := by
  refine lucas_primality 123450337 (7 : ZMod 123450337) ?_ (fun q hq hd => ?_)
  · rw [show 123450337 - 1 = 123450336 from by norm_num]
    reduce_mod_char
  · have e : 123450337 - 1 = [2 ^ 5, 3 ^ 2, 61 ^ 1, 7027 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123450337 - 1) / 2 = 61725168 from by norm_num]
      have h2 : (7 : ZMod 123450337) ^ 61725168 = ((123450336 : ℕ) : ZMod 123450337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123450337 - 1) / 3 = 41150112 from by norm_num]
      have h2 : (7 : ZMod 123450337) ^ 41150112 = ((5908230 : ℕ) : ZMod 123450337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123450337 - 1) / 61 = 2023776 from by norm_num]
      have h2 : (7 : ZMod 123450337) ^ 2023776 = ((17885624 : ℕ) : ZMod 123450337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123450337 - 1) / 7027 = 17568 from by norm_num]
      have h2 : (7 : ZMod 123450337) ^ 17568 = ((99329521 : ℕ) : ZMod 123450337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6936751667531821 : Nat.Prime 6936751667531821 := by
  refine lucas_primality 6936751667531821 (2 : ZMod 6936751667531821) ?_ (fun q hq hd => ?_)
  · rw [show 6936751667531821 - 1 = 6936751667531820 from by norm_num]
    reduce_mod_char
  · have e : 6936751667531821 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 23 ^ 1, 251 ^ 1, 557 ^ 1, 1289 ^ 1, 27893 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 2 = 3468375833765910 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 3468375833765910 = ((6936751667531820 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 3 = 2312250555843940 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 2312250555843940 = ((1634271444785631 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 5 = 1387350333506364 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 1387350333506364 = ((6733163775541462 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 23 = 301597898588340 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 301597898588340 = ((5969080472263838 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 251 = 27636460826820 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 27636460826820 = ((2127083746745382 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 557 = 12453773191260 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 12453773191260 = ((5090115044964583 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 1289 = 5381498578380 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 5381498578380 = ((1876898036211433 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6936751667531821 - 1) / 27893 = 248691487740 from by norm_num]
      have h2 : (2 : ZMod 6936751667531821) ^ 248691487740 = ((1290036679098272 : ℕ) : ZMod 6936751667531821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_220586933947 : Nat.Prime 220586933947 := by
  refine lucas_primality 220586933947 (5 : ZMod 220586933947) ?_ (fun q hq hd => ?_)
  · rw [show 220586933947 - 1 = 220586933946 from by norm_num]
    reduce_mod_char
  · have e : 220586933947 - 1 = [2 ^ 1, 3 ^ 1, 271 ^ 1, 3779 ^ 1, 35899 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220586933947 - 1) / 2 = 110293466973 from by norm_num]
      have h2 : (5 : ZMod 220586933947) ^ 110293466973 = ((220586933946 : ℕ) : ZMod 220586933947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220586933947 - 1) / 3 = 73528977982 from by norm_num]
      have h2 : (5 : ZMod 220586933947) ^ 73528977982 = ((96890876029 : ℕ) : ZMod 220586933947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220586933947 - 1) / 271 = 813973926 from by norm_num]
      have h2 : (5 : ZMod 220586933947) ^ 813973926 = ((729 : ℕ) : ZMod 220586933947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220586933947 - 1) / 3779 = 58371774 from by norm_num]
      have h2 : (5 : ZMod 220586933947) ^ 58371774 = ((201673285408 : ℕ) : ZMod 220586933947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (220586933947 - 1) / 35899 = 6144654 from by norm_num]
      have h2 : (5 : ZMod 220586933947) ^ 6144654 = ((20774786668 : ℕ) : ZMod 220586933947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49604567 : Nat.Prime 49604567 := by
  refine lucas_primality 49604567 (5 : ZMod 49604567) ?_ (fun q hq hd => ?_)
  · rw [show 49604567 - 1 = 49604566 from by norm_num]
    reduce_mod_char
  · have e : 49604567 - 1 = [2 ^ 1, 11 ^ 1, 223 ^ 1, 10111 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49604567 - 1) / 2 = 24802283 from by norm_num]
      have h2 : (5 : ZMod 49604567) ^ 24802283 = ((49604566 : ℕ) : ZMod 49604567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49604567 - 1) / 11 = 4509506 from by norm_num]
      have h2 : (5 : ZMod 49604567) ^ 4509506 = ((13852963 : ℕ) : ZMod 49604567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49604567 - 1) / 223 = 222442 from by norm_num]
      have h2 : (5 : ZMod 49604567) ^ 222442 = ((4099576 : ℕ) : ZMod 49604567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49604567 - 1) / 10111 = 4906 from by norm_num]
      have h2 : (5 : ZMod 49604567) ^ 4906 = ((39624291 : ℕ) : ZMod 49604567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4178391096679 : Nat.Prime 4178391096679 := by
  refine lucas_primality 4178391096679 (3 : ZMod 4178391096679) ?_ (fun q hq hd => ?_)
  · rw [show 4178391096679 - 1 = 4178391096678 from by norm_num]
    reduce_mod_char
  · have e : 4178391096679 - 1 = [2 ^ 1, 3 ^ 1, 101 ^ 1, 139 ^ 1, 49604567 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4178391096679 - 1) / 2 = 2089195548339 from by norm_num]
      have h2 : (3 : ZMod 4178391096679) ^ 2089195548339 = ((4178391096678 : ℕ) : ZMod 4178391096679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4178391096679 - 1) / 3 = 1392797032226 from by norm_num]
      have h2 : (3 : ZMod 4178391096679) ^ 1392797032226 = ((281385528615 : ℕ) : ZMod 4178391096679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4178391096679 - 1) / 101 = 41370208878 from by norm_num]
      have h2 : (3 : ZMod 4178391096679) ^ 41370208878 = ((2675179553603 : ℕ) : ZMod 4178391096679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4178391096679 - 1) / 139 = 30060367602 from by norm_num]
      have h2 : (3 : ZMod 4178391096679) ^ 30060367602 = ((3570278485667 : ℕ) : ZMod 4178391096679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_49604567).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4178391096679 - 1) / 49604567 = 84234 from by norm_num]
      have h2 : (3 : ZMod 4178391096679) ^ 84234 = ((2513160380019 : ℕ) : ZMod 4178391096679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43035232876181345838699618577 : Nat.Prime 43035232876181345838699618577 := by
  refine lucas_primality 43035232876181345838699618577 (35 : ZMod 43035232876181345838699618577) ?_ (fun q hq hd => ?_)
  · rw [show 43035232876181345838699618577 - 1 = 43035232876181345838699618576 from by norm_num]
    reduce_mod_char
  · have e : 43035232876181345838699618577 - 1 = [2 ^ 4, 3 ^ 1, 277 ^ 1, 27361 ^ 1, 28311449 ^ 1, 4178391096679 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 2 = 21517616438090672919349809288 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 21517616438090672919349809288 = ((43035232876181345838699618576 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 3 = 14345077625393781946233206192 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 14345077625393781946233206192 = ((42783236218571223993979538477 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 277 = 155361851538560815302164688 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 155361851538560815302164688 = ((4653435567777778715854651483 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 27361 = 1572867690368822259372816 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 1572867690368822259372816 = ((34069606585899955303158136995 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 28311449 = 1520064652154728846224 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 1520064652154728846224 = ((10375507461442574885751805645 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4178391096679).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43035232876181345838699618577 - 1) / 4178391096679 = 10299474577759344 from by norm_num]
      have h2 : (35 : ZMod 43035232876181345838699618577) ^ 10299474577759344 = ((24418011546328833986301997250 : ℕ) : ZMod 43035232876181345838699618577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4546491529 : Nat.Prime 4546491529 := by
  refine lucas_primality 4546491529 (7 : ZMod 4546491529) ?_ (fun q hq hd => ?_)
  · rw [show 4546491529 - 1 = 4546491528 from by norm_num]
    reduce_mod_char
  · have e : 4546491529 - 1 = [2 ^ 3, 3 ^ 1, 61 ^ 1, 3105527 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546491529 - 1) / 2 = 2273245764 from by norm_num]
      have h2 : (7 : ZMod 4546491529) ^ 2273245764 = ((4546491528 : ℕ) : ZMod 4546491529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546491529 - 1) / 3 = 1515497176 from by norm_num]
      have h2 : (7 : ZMod 4546491529) ^ 1515497176 = ((1060323265 : ℕ) : ZMod 4546491529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546491529 - 1) / 61 = 74532648 from by norm_num]
      have h2 : (7 : ZMod 4546491529) ^ 74532648 = ((1473144695 : ℕ) : ZMod 4546491529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4546491529 - 1) / 3105527 = 1464 from by norm_num]
      have h2 : (7 : ZMod 4546491529) ^ 1464 = ((1354276624 : ℕ) : ZMod 4546491529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81836847523 : Nat.Prime 81836847523 := by
  refine lucas_primality 81836847523 (2 : ZMod 81836847523) ?_ (fun q hq hd => ?_)
  · rw [show 81836847523 - 1 = 81836847522 from by norm_num]
    reduce_mod_char
  · have e : 81836847523 - 1 = [2 ^ 1, 3 ^ 2, 4546491529 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81836847523 - 1) / 2 = 40918423761 from by norm_num]
      have h2 : (2 : ZMod 81836847523) ^ 40918423761 = ((81836847522 : ℕ) : ZMod 81836847523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81836847523 - 1) / 3 = 27278949174 from by norm_num]
      have h2 : (2 : ZMod 81836847523) ^ 27278949174 = ((11377395199 : ℕ) : ZMod 81836847523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4546491529).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81836847523 - 1) / 4546491529 = 18 from by norm_num]
      have h2 : (2 : ZMod 81836847523) ^ 18 = ((262144 : ℕ) : ZMod 81836847523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3353336738929580410561 : Nat.Prime 3353336738929580410561 := by
  refine lucas_primality 3353336738929580410561 (23 : ZMod 3353336738929580410561) ?_ (fun q hq hd => ?_)
  · rw [show 3353336738929580410561 - 1 = 3353336738929580410560 from by norm_num]
    reduce_mod_char
  · have e : 3353336738929580410561 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 277 ^ 1, 22013 ^ 1, 81836847523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 2 = 1676668369464790205280 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 1676668369464790205280 = ((3353336738929580410560 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 3 = 1117778912976526803520 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 1117778912976526803520 = ((2697845041038234274934 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 5 = 670667347785916082112 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 670667347785916082112 = ((2428192837711278487934 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 7 = 479048105561368630080 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 479048105561368630080 = ((312590325449575666698 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 277 = 12105908804799929280 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 12105908804799929280 = ((1176019828462764988970 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 22013 = 152334381453213120 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 152334381453213120 = ((2579996234156055240591 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_81836847523).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3353336738929580410561 - 1) / 81836847523 = 40975878720 from by norm_num]
      have h2 : (23 : ZMod 3353336738929580410561) ^ 40975878720 = ((434606712606226891101 : ℕ) : ZMod 3353336738929580410561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_185195349641 : Nat.Prime 185195349641 := by
  refine lucas_primality 185195349641 (6 : ZMod 185195349641) ?_ (fun q hq hd => ?_)
  · rw [show 185195349641 - 1 = 185195349640 from by norm_num]
    reduce_mod_char
  · have e : 185195349641 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 1, 37 ^ 1, 53 ^ 1, 337283 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 2 = 92597674820 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 92597674820 = ((185195349640 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 5 = 37039069928 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 37039069928 = ((97728294908 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 7 = 26456478520 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 26456478520 = ((20840991612 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 37 = 5005279720 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 5005279720 = ((81301266015 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 53 = 3494251880 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 3494251880 = ((169269737226 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185195349641 - 1) / 337283 = 549080 from by norm_num]
      have h2 : (6 : ZMod 185195349641) ^ 549080 = ((142919718601 : ℕ) : ZMod 185195349641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_369879560116990841 : Nat.Prime 369879560116990841 := by
  refine lucas_primality 369879560116990841 (6 : ZMod 369879560116990841) ?_ (fun q hq hd => ?_)
  · rw [show 369879560116990841 - 1 = 369879560116990840 from by norm_num]
    reduce_mod_char
  · have e : 369879560116990841 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 2, 1019 ^ 1, 185195349641 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369879560116990841 - 1) / 2 = 184939780058495420 from by norm_num]
      have h2 : (6 : ZMod 369879560116990841) ^ 184939780058495420 = ((369879560116990840 : ℕ) : ZMod 369879560116990841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369879560116990841 - 1) / 5 = 73975912023398168 from by norm_num]
      have h2 : (6 : ZMod 369879560116990841) ^ 73975912023398168 = ((329184147542869750 : ℕ) : ZMod 369879560116990841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369879560116990841 - 1) / 7 = 52839937159570120 from by norm_num]
      have h2 : (6 : ZMod 369879560116990841) ^ 52839937159570120 = ((342738668407639096 : ℕ) : ZMod 369879560116990841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369879560116990841 - 1) / 1019 = 362982885296360 from by norm_num]
      have h2 : (6 : ZMod 369879560116990841) ^ 362982885296360 = ((84608777213966255 : ℕ) : ZMod 369879560116990841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_185195349641).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (369879560116990841 - 1) / 185195349641 = 1997240 from by norm_num]
      have h2 : (6 : ZMod 369879560116990841) ^ 1997240 = ((217478943436119602 : ℕ) : ZMod 369879560116990841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2664097031 : Nat.Prime 2664097031 := by
  refine lucas_primality 2664097031 (7 : ZMod 2664097031) ?_ (fun q hq hd => ?_)
  · rw [show 2664097031 - 1 = 2664097030 from by norm_num]
    reduce_mod_char
  · have e : 2664097031 - 1 = [2 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 521 ^ 1, 4297 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 2 = 1332048515 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 1332048515 = ((2664097030 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 5 = 532819406 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 532819406 = ((2187 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 7 = 380585290 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 380585290 = ((105753585 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 17 = 156711590 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 156711590 = ((2403494744 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 521 = 5113430 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 5113430 = ((1907340106 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2664097031 - 1) / 4297 = 619990 from by norm_num]
      have h2 : (7 : ZMod 2664097031) ^ 619990 = ((1348207134 : ℕ) : ZMod 2664097031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_94373861 : Nat.Prime 94373861 := by
  refine lucas_primality 94373861 (2 : ZMod 94373861) ?_ (fun q hq hd => ?_)
  · rw [show 94373861 - 1 = 94373860 from by norm_num]
    reduce_mod_char
  · have e : 94373861 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 1, 674099 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94373861 - 1) / 2 = 47186930 from by norm_num]
      have h2 : (2 : ZMod 94373861) ^ 47186930 = ((94373860 : ℕ) : ZMod 94373861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94373861 - 1) / 5 = 18874772 from by norm_num]
      have h2 : (2 : ZMod 94373861) ^ 18874772 = ((2305395 : ℕ) : ZMod 94373861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94373861 - 1) / 7 = 13481980 from by norm_num]
      have h2 : (2 : ZMod 94373861) ^ 13481980 = ((73625306 : ℕ) : ZMod 94373861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (94373861 - 1) / 674099 = 140 from by norm_num]
      have h2 : (2 : ZMod 94373861) ^ 140 = ((54892153 : ℕ) : ZMod 94373861) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 : Nat.Prime 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 := by
  refine lucas_primality 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ?_ (fun q hq hd => ?_)
  · rw [show 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1 = 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556200 from by norm_num]
    reduce_mod_char
  · have e : 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 2, 11 ^ 2, 29 ^ 1, 41 ^ 1, 61 ^ 1, 71 ^ 1, 281 ^ 1, 547 ^ 1, 1093 ^ 1, 1181 ^ 1, 16493 ^ 1, 18481 ^ 1, 430697 ^ 1, 647753 ^ 1, 28596961 ^ 1, 32839661 ^ 1, 42521761 ^ 1, 94373861 ^ 1, 2664097031 ^ 1, 374857981681 ^ 1, 369879560116990841 ^ 1, 3353336738929580410561 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 2 = 14722534789431806052394709066579628330574226937842016196631789187411927377600469459790690771873552677567439784248434741708329466278100 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 14722534789431806052394709066579628330574226937842016196631789187411927377600469459790690771873552677567439784248434741708329466278100 = ((29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556200 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 3 = 9815023192954537368263139377719752220382817958561344131087859458274618251733646306527127181249035118378293189498956494472219644185400 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 9815023192954537368263139377719752220382817958561344131087859458274618251733646306527127181249035118378293189498956494472219644185400 = ((9398681223266955568884336291512895498310041670215997912289397076201 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 5 = 5889013915772722420957883626631851332229690775136806478652715674964770951040187783916276308749421071026975913699373896683331786511240 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 5889013915772722420957883626631851332229690775136806478652715674964770951040187783916276308749421071026975913699373896683331786511240 = ((26357055401302162391267120820015635328002542744105747998749762275103299569220120135962111072689789074241350442622329635947984789637242 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 11 = 2676824507169419282253583466650841514649859443244002944842143488620350432290994447234671049431555032284989051681533589401514448414200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 2676824507169419282253583466650841514649859443244002944842143488620350432290994447234671049431555032284989051681533589401514448414200 = ((10190806865945215657300379603308765805670712375973914857761673383847629442602915347748024913635998727637953808590036884279469405549360 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 29 = 1015347226857365934647910970108939884867188064678759737698744081890477750179342721364875225646451908797754467879202395979884790777800 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 1015347226857365934647910970108939884867188064678759737698744081890477750179342721364875225646451908797754467879202395979884790777800 = ((4962786653121857633410581574716739993301908449498710311713490968909156544111689318889235180431530008412068626861367919289466984466409 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 41 = 718172428752771026946083369101445284418254972577659326664965326215215969639047290721497110823100130613045843134069987400406315428200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 718172428752771026946083369101445284418254972577659326664965326215215969639047290721497110823100130613045843134069987400406315428200 = ((16593307117181170910919143378005101187892224622964961010038338036837583235977746766215614811133451538518139943552428053947252228708107 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 61 = 482706058669895280406383903822282896084400883207934957266616038931538602544277687206252156454870579592375074893391303006830474304200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 482706058669895280406383903822282896084400883207934957266616038931538602544277687206252156454870579592375074893391303006830474304200 = ((8402227038939258312358640986706974525646795950725717425336011987381761660129681665606361657699155867679209054270030225650007739597045 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 71 = 414719289843149466264639692016327558607724702474422991454416596828504996552125900275794106249959230354012388288688302583333224402200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 414719289843149466264639692016327558607724702474422991454416596828504996552125900275794106249959230354012388288688302583333224402200 = ((19166409090455517434682098528695097739491079831372316645870358004612701318754869197340783598941358564617840288880901424319196820916922 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 281 = 104786724479941680088218569868894151819033643685708300331898855426419411940216864482496019728637385605462204870095620937425832500200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 104786724479941680088218569868894151819033643685708300331898855426419411940216864482496019728637385605462204870095620937425832500200 = ((29445069578863612104669816428788939846055297400257611581607934928452480612422440676182216979832532735184981694824946735657000420586838 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 547 = 53830108919311905127585773552393522232446899224285251175984603975911983099087639706730130792956316919807823708403783333485665324600 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 53830108919311905127585773552393522232446899224285251175984603975911983099087639706730130792956316919807823708403783333485665324600 = ((23547655659402291351146250884129205921523821671323936768462884790373960065603674647245267632892144331488691195656421569371855584602412 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 1093 = 26939679395117668897337070570136556872047990737130862207926421202949546894053923988638043498396253755841609852238672903400419883400 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 26939679395117668897337070570136556872047990737130862207926421202949546894053923988638043498396253755841609852238672903400419883400 = ((7738924350480309021377446535651810898485209926501064664873681400581903128643099357638603011119594583559166251661404475472926495610168 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 1181 = 24932319711146157582378846852802080153385651037835759858817593882153983704657865300238257022647845347277628762486765015594122720200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 24932319711146157582378846852802080153385651037835759858817593882153983704657865300238257022647845347277628762486765015594122720200 = ((18592005354165344409107032138529888384055861343023585387174209665985660921198390095390684472088780535383003294888594258956738900467151 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 16493 = 1785307074447560304661942529143227833696019758423818128494729786868602119396164367888278757275638474209354245346320832075223363400 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 1785307074447560304661942529143227833696019758423818128494729786868602119396164367888278757275638474209354245346320832075223363400 = ((4169531842299288047983412532183612272485747176487811123990966688093266323878173012800316573031958244173290609435976963830264971741644 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 18481 = 1593261705473925226166842602302865465134378760656026859653892017467878077766405439076964533507229335811637875033649125232220060200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 1593261705473925226166842602302865465134378760656026859653892017467878077766405439076964533507229335811637875033649125232220060200 = ((14903340109338493744458899243458783339245722532002361167748750677314798513609810570400117702310853180332075815908277506195071741766476 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 430697 = 68366089336270306282118097254355745828618388044690425968287632314188059715300870262809774722710177584554523408560703890244554600 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 68366089336270306282118097254355745828618388044690425968287632314188059715300870262809774722710177584554523408560703890244554600 = ((26557401087573629642004933142853881388398487026065053790073307062597733308926126963028188930043774463959862713784153616980887596555667 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 647753 = 45457249258380296354921425501941722633702127007800862972867093436578224655387067168475300838046454983820807574024156558775735400 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 45457249258380296354921425501941722633702127007800862972867093436578224655387067168475300838046454983820807574024156558775735400 = ((13839161504623265161543029818819758542586301673202679581841248345858647935216768405045834894121368269978234886613778984980779000292758 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 28596961 = 1029657297461209675559211278889363686622101344114293557041378570779736166902522926110273799504328636708455823977130628790124200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 1029657297461209675559211278889363686622101344114293557041378570779736166902522926110273799504328636708455823977130628790124200 = ((4802161028562663369145541440390958104115653644521054037873167873856017073250064699107960572814595419360570926044627455215800680350856 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 32839661 = 896631350088041776825571315524823982231377293318710945075333706240873033226528706236686838629275294746035276323250397847184200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 896631350088041776825571315524823982231377293318710945075333706240873033226528706236686838629275294746035276323250397847184200 = ((12302482648697251469612207382783556001223303160557373904000982565825988457311854173264107779385658703175967848714642719501881422361742 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 42521761 = 692470605318147856218594007269813135470764107716141680803473270423204127298512846624141026138289647861359259521186563355564200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 692470605318147856218594007269813135470764107716141680803473270423204127298512846624141026138289647861359259521186563355564200 = ((27604176342128560236590792320626872565114642386198454438020873215000288081493254937598025739842151962377942607016939774970842941665316 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_94373861).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 94373861 = 312004502802567462030502472852724089153758940472765360243802872225645772352165807008588761073864566748359268341229246553944200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 312004502802567462030502472852724089153758940472765360243802872225645772352165807008588761073864566748359268341229246553944200 = ((949577564507777867963047128688430365083253182919748441643803387965641474143199731247294587043649124084713336993478543919210005300728 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2664097031).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 2664097031 = 11052551478506419350005055477710660254532018160446661446417706838705551169994505699211291806641071758746642876498468453650200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 11052551478506419350005055477710660254532018160446661446417706838705551169994505699211291806641071758746642876498468453650200 = ((17952998766989231052500202594597439435493139560777182815859105999898338990002831947250669744905101689751346587128741797910149037824278 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_374857981681).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 374857981681 = 78549933622384599323618258493942063425812210952248384261511638170868847423150512632185047278556110449835049269390374620200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 78549933622384599323618258493942063425812210952248384261511638170868847423150512632185047278556110449835049269390374620200 = ((4044619161538455572129732063355467171080409720133040884105292056811599668696301327934500468773921508069439886140216045745180014221772 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_369879560116990841).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 369879560116990841 = 79607182320510765438005095861510452575494375787043570018217049395079459989441026786099844771464953092708723629268200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 79607182320510765438005095861510452575494375787043570018217049395079459989441026786099844771464953092708723629268200 = ((19161693836208195035369524269071555933379141095516398501997893254208027809443627254604477244871928907473571465862564200222376066057721 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3353336738929580410561).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 - 1) / 3353336738929580410561 = 8780826940828728484251842844655237056807919201557307359736987227910744717729703758313979819663637752214936204200 from by norm_num]
      have h2 : (14 : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) ^ 8780826940828728484251842844655237056807919201557307359736987227910744717729703758313979819663637752214936204200 = ((9478006026556162049275932439728031957740976244136554020690849575921371921644229253527046970471146672772637738415680397518182840510258 : ℕ) : ZMod 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_542985073109767895287 : Nat.Prime 542985073109767895287 := by
  refine lucas_primality 542985073109767895287 (5 : ZMod 542985073109767895287) ?_ (fun q hq hd => ?_)
  · rw [show 542985073109767895287 - 1 = 542985073109767895286 from by norm_num]
    reduce_mod_char
  · have e : 542985073109767895287 - 1 = [2 ^ 1, 3 ^ 1, 31 ^ 1, 283 ^ 1, 1669 ^ 1, 383587 ^ 1, 16112699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 2 = 271492536554883947643 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 271492536554883947643 = ((542985073109767895286 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 3 = 180995024369922631762 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 180995024369922631762 = ((25710014548502405525 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 31 = 17515647519669932106 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 17515647519669932106 = ((80717104413103570749 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 283 = 1918675169999179842 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 1918675169999179842 = ((213692042354948083215 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 1669 = 325335574062173694 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 325335574062173694 = ((455242613991839460065 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 383587 = 1415546077186578 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 1415546077186578 = ((148662522613418920273 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (542985073109767895287 - 1) / 16112699 = 33699200432514 from by norm_num]
      have h2 : (5 : ZMod 542985073109767895287) ^ 33699200432514 = ((84788233625186195391 : ℕ) : ZMod 542985073109767895287) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_65138399321 : Nat.Prime 65138399321 := by
  refine lucas_primality 65138399321 (6 : ZMod 65138399321) ?_ (fun q hq hd => ?_)
  · rw [show 65138399321 - 1 = 65138399320 from by norm_num]
    reduce_mod_char
  · have e : 65138399321 - 1 = [2 ^ 3, 5 ^ 1, 73 ^ 1, 22307671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65138399321 - 1) / 2 = 32569199660 from by norm_num]
      have h2 : (6 : ZMod 65138399321) ^ 32569199660 = ((65138399320 : ℕ) : ZMod 65138399321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65138399321 - 1) / 5 = 13027679864 from by norm_num]
      have h2 : (6 : ZMod 65138399321) ^ 13027679864 = ((28596162530 : ℕ) : ZMod 65138399321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65138399321 - 1) / 73 = 892306840 from by norm_num]
      have h2 : (6 : ZMod 65138399321) ^ 892306840 = ((28498363787 : ℕ) : ZMod 65138399321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65138399321 - 1) / 22307671 = 2920 from by norm_num]
      have h2 : (6 : ZMod 65138399321) ^ 2920 = ((41590404025 : ℕ) : ZMod 65138399321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3136609543672301 : Nat.Prime 3136609543672301 := by
  refine lucas_primality 3136609543672301 (2 : ZMod 3136609543672301) ?_ (fun q hq hd => ?_)
  · rw [show 3136609543672301 - 1 = 3136609543672300 from by norm_num]
    reduce_mod_char
  · have e : 3136609543672301 - 1 = [2 ^ 2, 5 ^ 2, 2758337 ^ 1, 11371379 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3136609543672301 - 1) / 2 = 1568304771836150 from by norm_num]
      have h2 : (2 : ZMod 3136609543672301) ^ 1568304771836150 = ((3136609543672300 : ℕ) : ZMod 3136609543672301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3136609543672301 - 1) / 5 = 627321908734460 from by norm_num]
      have h2 : (2 : ZMod 3136609543672301) ^ 627321908734460 = ((609948405814247 : ℕ) : ZMod 3136609543672301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3136609543672301 - 1) / 2758337 = 1137137900 from by norm_num]
      have h2 : (2 : ZMod 3136609543672301) ^ 1137137900 = ((2801877448485913 : ℕ) : ZMod 3136609543672301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3136609543672301 - 1) / 11371379 = 275833700 from by norm_num]
      have h2 : (2 : ZMod 3136609543672301) ^ 275833700 = ((152086930638183 : ℕ) : ZMod 3136609543672301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1869419288028691397 : Nat.Prime 1869419288028691397 := by
  refine lucas_primality 1869419288028691397 (2 : ZMod 1869419288028691397) ?_ (fun q hq hd => ?_)
  · rw [show 1869419288028691397 - 1 = 1869419288028691396 from by norm_num]
    reduce_mod_char
  · have e : 1869419288028691397 - 1 = [2 ^ 2, 149 ^ 1, 3136609543672301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1869419288028691397 - 1) / 2 = 934709644014345698 from by norm_num]
      have h2 : (2 : ZMod 1869419288028691397) ^ 934709644014345698 = ((1869419288028691396 : ℕ) : ZMod 1869419288028691397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1869419288028691397 - 1) / 149 = 12546438174689204 from by norm_num]
      have h2 : (2 : ZMod 1869419288028691397) ^ 12546438174689204 = ((471910798267568270 : ℕ) : ZMod 1869419288028691397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3136609543672301).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1869419288028691397 - 1) / 3136609543672301 = 596 from by norm_num]
      have h2 : (2 : ZMod 1869419288028691397) ^ 596 = ((992356546315210107 : ℕ) : ZMod 1869419288028691397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3252055223 : Nat.Prime 3252055223 := by
  refine lucas_primality 3252055223 (5 : ZMod 3252055223) ?_ (fun q hq hd => ?_)
  · rw [show 3252055223 - 1 = 3252055222 from by norm_num]
    reduce_mod_char
  · have e : 3252055223 - 1 = [2 ^ 1, 13 ^ 1, 17 ^ 1, 661 ^ 1, 11131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3252055223 - 1) / 2 = 1626027611 from by norm_num]
      have h2 : (5 : ZMod 3252055223) ^ 1626027611 = ((3252055222 : ℕ) : ZMod 3252055223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3252055223 - 1) / 13 = 250158094 from by norm_num]
      have h2 : (5 : ZMod 3252055223) ^ 250158094 = ((833867598 : ℕ) : ZMod 3252055223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3252055223 - 1) / 17 = 191297366 from by norm_num]
      have h2 : (5 : ZMod 3252055223) ^ 191297366 = ((1131074587 : ℕ) : ZMod 3252055223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3252055223 - 1) / 661 = 4919902 from by norm_num]
      have h2 : (5 : ZMod 3252055223) ^ 4919902 = ((1741851020 : ℕ) : ZMod 3252055223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3252055223 - 1) / 11131 = 292162 from by norm_num]
      have h2 : (5 : ZMod 3252055223) ^ 292162 = ((956113260 : ℕ) : ZMod 3252055223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138448913507025345101 : Nat.Prime 138448913507025345101 := by
  refine lucas_primality 138448913507025345101 (2 : ZMod 138448913507025345101) ?_ (fun q hq hd => ?_)
  · rw [show 138448913507025345101 - 1 = 138448913507025345100 from by norm_num]
    reduce_mod_char
  · have e : 138448913507025345101 - 1 = [2 ^ 2, 5 ^ 2, 151 ^ 1, 2819387 ^ 1, 3252055223 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138448913507025345101 - 1) / 2 = 69224456753512672550 from by norm_num]
      have h2 : (2 : ZMod 138448913507025345101) ^ 69224456753512672550 = ((138448913507025345100 : ℕ) : ZMod 138448913507025345101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138448913507025345101 - 1) / 5 = 27689782701405069020 from by norm_num]
      have h2 : (2 : ZMod 138448913507025345101) ^ 27689782701405069020 = ((97920571061921631182 : ℕ) : ZMod 138448913507025345101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138448913507025345101 - 1) / 151 = 916880221900830100 from by norm_num]
      have h2 : (2 : ZMod 138448913507025345101) ^ 916880221900830100 = ((21768848959198145682 : ℕ) : ZMod 138448913507025345101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138448913507025345101 - 1) / 2819387 = 49106033867300 from by norm_num]
      have h2 : (2 : ZMod 138448913507025345101) ^ 49106033867300 = ((87681359433205715771 : ℕ) : ZMod 138448913507025345101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3252055223).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138448913507025345101 - 1) / 3252055223 = 42572743700 from by norm_num]
      have h2 : (2 : ZMod 138448913507025345101) ^ 42572743700 = ((105614847827044589986 : ℕ) : ZMod 138448913507025345101) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_903476649197 : Nat.Prime 903476649197 := by
  refine lucas_primality 903476649197 (3 : ZMod 903476649197) ?_ (fun q hq hd => ?_)
  · rw [show 903476649197 - 1 = 903476649196 from by norm_num]
    reduce_mod_char
  · have e : 903476649197 - 1 = [2 ^ 2, 11 ^ 1, 2003 ^ 1, 10251403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (903476649197 - 1) / 2 = 451738324598 from by norm_num]
      have h2 : (3 : ZMod 903476649197) ^ 451738324598 = ((903476649196 : ℕ) : ZMod 903476649197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (903476649197 - 1) / 11 = 82134240836 from by norm_num]
      have h2 : (3 : ZMod 903476649197) ^ 82134240836 = ((374846380051 : ℕ) : ZMod 903476649197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (903476649197 - 1) / 2003 = 451061732 from by norm_num]
      have h2 : (3 : ZMod 903476649197) ^ 451061732 = ((548909356088 : ℕ) : ZMod 903476649197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (903476649197 - 1) / 10251403 = 88132 from by norm_num]
      have h2 : (3 : ZMod 903476649197) ^ 88132 = ((796625327256 : ℕ) : ZMod 903476649197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23074818917837557517 : Nat.Prime 23074818917837557517 := by
  refine lucas_primality 23074818917837557517 (2 : ZMod 23074818917837557517) ?_ (fun q hq hd => ?_)
  · rw [show 23074818917837557517 - 1 = 23074818917837557516 from by norm_num]
    reduce_mod_char
  · have e : 23074818917837557517 - 1 = [2 ^ 2, 19 ^ 2, 23 ^ 1, 769 ^ 1, 903476649197 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23074818917837557517 - 1) / 2 = 11537409458918778758 from by norm_num]
      have h2 : (2 : ZMod 23074818917837557517) ^ 11537409458918778758 = ((23074818917837557516 : ℕ) : ZMod 23074818917837557517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23074818917837557517 - 1) / 19 = 1214464153570397764 from by norm_num]
      have h2 : (2 : ZMod 23074818917837557517) ^ 1214464153570397764 = ((19343703549884509272 : ℕ) : ZMod 23074818917837557517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23074818917837557517 - 1) / 23 = 1003252996427719892 from by norm_num]
      have h2 : (2 : ZMod 23074818917837557517) ^ 1003252996427719892 = ((6485454353245045321 : ℕ) : ZMod 23074818917837557517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23074818917837557517 - 1) / 769 = 30006266473130764 from by norm_num]
      have h2 : (2 : ZMod 23074818917837557517) ^ 30006266473130764 = ((12378584697627372426 : ℕ) : ZMod 23074818917837557517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_903476649197).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23074818917837557517 - 1) / 903476649197 = 25540028 from by norm_num]
      have h2 : (2 : ZMod 23074818917837557517) ^ 25540028 = ((16674316971960554952 : ℕ) : ZMod 23074818917837557517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50727793 : Nat.Prime 50727793 := by
  refine lucas_primality 50727793 (5 : ZMod 50727793) ?_ (fun q hq hd => ?_)
  · rw [show 50727793 - 1 = 50727792 from by norm_num]
    reduce_mod_char
  · have e : 50727793 - 1 = [2 ^ 4, 3 ^ 1, 1056829 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50727793 - 1) / 2 = 25363896 from by norm_num]
      have h2 : (5 : ZMod 50727793) ^ 25363896 = ((50727792 : ℕ) : ZMod 50727793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50727793 - 1) / 3 = 16909264 from by norm_num]
      have h2 : (5 : ZMod 50727793) ^ 16909264 = ((6887594 : ℕ) : ZMod 50727793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50727793 - 1) / 1056829 = 48 from by norm_num]
      have h2 : (5 : ZMod 50727793) ^ 48 = ((858210 : ℕ) : ZMod 50727793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1281934384324308751 : Nat.Prime 1281934384324308751 := by
  refine lucas_primality 1281934384324308751 (3 : ZMod 1281934384324308751) ?_ (fun q hq hd => ?_)
  · rw [show 1281934384324308751 - 1 = 1281934384324308750 from by norm_num]
    reduce_mod_char
  · have e : 1281934384324308751 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 4, 7 ^ 1, 137 ^ 1, 7027 ^ 1, 50727793 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 2 = 640967192162154375 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 640967192162154375 = ((1281934384324308750 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 3 = 427311461441436250 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 427311461441436250 = ((796770904113326125 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 5 = 256386876864861750 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 256386876864861750 = ((853519766653823539 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 7 = 183133483474901250 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 183133483474901250 = ((71730749007745646 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 137 = 9357185287038750 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 9357185287038750 = ((916339430805132636 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 7027 = 182429825576250 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 182429825576250 = ((418933393195684701 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_50727793).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1281934384324308751 - 1) / 50727793 = 25270848750 from by norm_num]
      have h2 : (3 : ZMod 1281934384324308751) ^ 25270848750 = ((505855033475462892 : ℕ) : ZMod 1281934384324308751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_362738297 : Nat.Prime 362738297 := by
  refine lucas_primality 362738297 (5 : ZMod 362738297) ?_ (fun q hq hd => ?_)
  · rw [show 362738297 - 1 = 362738296 from by norm_num]
    reduce_mod_char
  · have e : 362738297 - 1 = [2 ^ 3, 79 ^ 1, 573953 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (362738297 - 1) / 2 = 181369148 from by norm_num]
      have h2 : (5 : ZMod 362738297) ^ 181369148 = ((362738296 : ℕ) : ZMod 362738297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (362738297 - 1) / 79 = 4591624 from by norm_num]
      have h2 : (5 : ZMod 362738297) ^ 4591624 = ((301119235 : ℕ) : ZMod 362738297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (362738297 - 1) / 573953 = 632 from by norm_num]
      have h2 : (5 : ZMod 362738297) ^ 632 = ((44845 : ℕ) : ZMod 362738297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_324725239 : Nat.Prime 324725239 := by
  refine lucas_primality 324725239 (3 : ZMod 324725239) ?_ (fun q hq hd => ?_)
  · rw [show 324725239 - 1 = 324725238 from by norm_num]
    reduce_mod_char
  · have e : 324725239 - 1 = [2 ^ 1, 3 ^ 2, 19 ^ 1, 29 ^ 2, 1129 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (324725239 - 1) / 2 = 162362619 from by norm_num]
      have h2 : (3 : ZMod 324725239) ^ 162362619 = ((324725238 : ℕ) : ZMod 324725239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (324725239 - 1) / 3 = 108241746 from by norm_num]
      have h2 : (3 : ZMod 324725239) ^ 108241746 = ((122374726 : ℕ) : ZMod 324725239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (324725239 - 1) / 19 = 17090802 from by norm_num]
      have h2 : (3 : ZMod 324725239) ^ 17090802 = ((214711096 : ℕ) : ZMod 324725239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (324725239 - 1) / 29 = 11197422 from by norm_num]
      have h2 : (3 : ZMod 324725239) ^ 11197422 = ((180507749 : ℕ) : ZMod 324725239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (324725239 - 1) / 1129 = 287622 from by norm_num]
      have h2 : (3 : ZMod 324725239) ^ 287622 = ((277382487 : ℕ) : ZMod 324725239) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9742146717540659659 : Nat.Prime 9742146717540659659 := by
  refine lucas_primality 9742146717540659659 (3 : ZMod 9742146717540659659) ?_ (fun q hq hd => ?_)
  · rw [show 9742146717540659659 - 1 = 9742146717540659658 from by norm_num]
    reduce_mod_char
  · have e : 9742146717540659659 - 1 = [2 ^ 1, 3 ^ 1, 487 ^ 1, 10267351 ^ 1, 324725239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9742146717540659659 - 1) / 2 = 4871073358770329829 from by norm_num]
      have h2 : (3 : ZMod 9742146717540659659) ^ 4871073358770329829 = ((9742146717540659658 : ℕ) : ZMod 9742146717540659659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9742146717540659659 - 1) / 3 = 3247382239180219886 from by norm_num]
      have h2 : (3 : ZMod 9742146717540659659) ^ 3247382239180219886 = ((2234091668858766604 : ℕ) : ZMod 9742146717540659659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9742146717540659659 - 1) / 487 = 20004408044231334 from by norm_num]
      have h2 : (3 : ZMod 9742146717540659659) ^ 20004408044231334 = ((1502146414929742565 : ℕ) : ZMod 9742146717540659659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9742146717540659659 - 1) / 10267351 = 948847148358 from by norm_num]
      have h2 : (3 : ZMod 9742146717540659659) ^ 948847148358 = ((8008040479907858104 : ℕ) : ZMod 9742146717540659659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_324725239).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9742146717540659659 - 1) / 324725239 = 30001199622 from by norm_num]
      have h2 : (3 : ZMod 9742146717540659659) ^ 30001199622 = ((5841584548654916009 : ℕ) : ZMod 9742146717540659659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116905760610487915909 : Nat.Prime 116905760610487915909 := by
  refine lucas_primality 116905760610487915909 (6 : ZMod 116905760610487915909) ?_ (fun q hq hd => ?_)
  · rw [show 116905760610487915909 - 1 = 116905760610487915908 from by norm_num]
    reduce_mod_char
  · have e : 116905760610487915909 - 1 = [2 ^ 2, 3 ^ 1, 9742146717540659659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116905760610487915909 - 1) / 2 = 58452880305243957954 from by norm_num]
      have h2 : (6 : ZMod 116905760610487915909) ^ 58452880305243957954 = ((116905760610487915908 : ℕ) : ZMod 116905760610487915909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116905760610487915909 - 1) / 3 = 38968586870162638636 from by norm_num]
      have h2 : (6 : ZMod 116905760610487915909) ^ 38968586870162638636 = ((62769999495801674183 : ℕ) : ZMod 116905760610487915909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9742146717540659659).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116905760610487915909 - 1) / 9742146717540659659 = 12 from by norm_num]
      have h2 : (6 : ZMod 116905760610487915909) ^ 12 = ((2176782336 : ℕ) : ZMod 116905760610487915909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3971320541 : Nat.Prime 3971320541 := by
  refine lucas_primality 3971320541 (2 : ZMod 3971320541) ?_ (fun q hq hd => ?_)
  · rw [show 3971320541 - 1 = 3971320540 from by norm_num]
    reduce_mod_char
  · have e : 3971320541 - 1 = [2 ^ 2, 5 ^ 1, 11 ^ 1, 18051457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3971320541 - 1) / 2 = 1985660270 from by norm_num]
      have h2 : (2 : ZMod 3971320541) ^ 1985660270 = ((3971320540 : ℕ) : ZMod 3971320541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3971320541 - 1) / 5 = 794264108 from by norm_num]
      have h2 : (2 : ZMod 3971320541) ^ 794264108 = ((2789110734 : ℕ) : ZMod 3971320541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3971320541 - 1) / 11 = 361029140 from by norm_num]
      have h2 : (2 : ZMod 3971320541) ^ 361029140 = ((3694635760 : ℕ) : ZMod 3971320541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3971320541 - 1) / 18051457 = 220 from by norm_num]
      have h2 : (2 : ZMod 3971320541) ^ 220 = ((1400656921 : ℕ) : ZMod 3971320541) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76824655095930309016347566008213507 : Nat.Prime 76824655095930309016347566008213507 := by
  refine lucas_primality 76824655095930309016347566008213507 (2 : ZMod 76824655095930309016347566008213507) ?_ (fun q hq hd => ?_)
  · rw [show 76824655095930309016347566008213507 - 1 = 76824655095930309016347566008213506 from by norm_num]
    reduce_mod_char
  · have e : 76824655095930309016347566008213507 - 1 = [2 ^ 1, 3 ^ 2, 29 ^ 1, 317 ^ 1, 3971320541 ^ 1, 116905760610487915909 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 2 = 38412327547965154508173783004106753 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 38412327547965154508173783004106753 = ((76824655095930309016347566008213506 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 3 = 25608218365310103005449188669404502 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 25608218365310103005449188669404502 = ((59274912056131994324202706151650920 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 29 = 2649126037790700310908536758903914 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 2649126037790700310908536758903914 = ((9356878136542543663930375857742863 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 317 = 242349069703250186171443425893418 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 242349069703250186171443425893418 = ((50281021886475813151416946862185888 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3971320541).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 3971320541 = 19344863831259877397125866 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 19344863831259877397125866 = ((34569244576740532798464110623610280 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_116905760610487915909).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76824655095930309016347566008213507 - 1) / 116905760610487915909 = 657150295201434 from by norm_num]
      have h2 : (2 : ZMod 76824655095930309016347566008213507) ^ 657150295201434 = ((31708700953360684531447873036756427 : ℕ) : ZMod 76824655095930309016347566008213507) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1152709099 : Nat.Prime 1152709099 := by
  refine lucas_primality 1152709099 (2 : ZMod 1152709099) ?_ (fun q hq hd => ?_)
  · rw [show 1152709099 - 1 = 1152709098 from by norm_num]
    reduce_mod_char
  · have e : 1152709099 - 1 = [2 ^ 1, 3 ^ 1, 193 ^ 1, 995431 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1152709099 - 1) / 2 = 576354549 from by norm_num]
      have h2 : (2 : ZMod 1152709099) ^ 576354549 = ((1152709098 : ℕ) : ZMod 1152709099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1152709099 - 1) / 3 = 384236366 from by norm_num]
      have h2 : (2 : ZMod 1152709099) ^ 384236366 = ((518034149 : ℕ) : ZMod 1152709099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1152709099 - 1) / 193 = 5972586 from by norm_num]
      have h2 : (2 : ZMod 1152709099) ^ 5972586 = ((958079548 : ℕ) : ZMod 1152709099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1152709099 - 1) / 995431 = 1158 from by norm_num]
      have h2 : (2 : ZMod 1152709099) ^ 1158 = ((507502193 : ℕ) : ZMod 1152709099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_16274984685283 : Nat.Prime 16274984685283 := by
  refine lucas_primality 16274984685283 (2 : ZMod 16274984685283) ?_ (fun q hq hd => ?_)
  · rw [show 16274984685283 - 1 = 16274984685282 from by norm_num]
    reduce_mod_char
  · have e : 16274984685283 - 1 = [2 ^ 1, 3 ^ 3, 29 ^ 1, 191 ^ 1, 331 ^ 1, 164387 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 2 = 8137492342641 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 8137492342641 = ((16274984685282 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 3 = 5424994895094 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 5424994895094 = ((4495062851413 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 29 = 561206368458 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 561206368458 = ((2118793787101 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 191 = 85209343902 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 85209343902 = ((11850153190571 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 331 = 49169138022 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 49169138022 = ((9151396847095 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16274984685283 - 1) / 164387 = 99004086 from by norm_num]
      have h2 : (2 : ZMod 16274984685283) ^ 99004086 = ((11749352776270 : ℕ) : ZMod 16274984685283) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_108711523 : Nat.Prime 108711523 := by
  refine lucas_primality 108711523 (2 : ZMod 108711523) ?_ (fun q hq hd => ?_)
  · rw [show 108711523 - 1 = 108711522 from by norm_num]
    reduce_mod_char
  · have e : 108711523 - 1 = [2 ^ 1, 3 ^ 2, 1741 ^ 1, 3469 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108711523 - 1) / 2 = 54355761 from by norm_num]
      have h2 : (2 : ZMod 108711523) ^ 54355761 = ((108711522 : ℕ) : ZMod 108711523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108711523 - 1) / 3 = 36237174 from by norm_num]
      have h2 : (2 : ZMod 108711523) ^ 36237174 = ((97170999 : ℕ) : ZMod 108711523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108711523 - 1) / 1741 = 62442 from by norm_num]
      have h2 : (2 : ZMod 108711523) ^ 62442 = ((9307133 : ℕ) : ZMod 108711523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (108711523 - 1) / 3469 = 31338 from by norm_num]
      have h2 : (2 : ZMod 108711523) ^ 31338 = ((58764650 : ℕ) : ZMod 108711523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_104309321 : Nat.Prime 104309321 := by
  refine lucas_primality 104309321 (3 : ZMod 104309321) ?_ (fun q hq hd => ?_)
  · rw [show 104309321 - 1 = 104309320 from by norm_num]
    reduce_mod_char
  · have e : 104309321 - 1 = [2 ^ 3, 5 ^ 1, 2607733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104309321 - 1) / 2 = 52154660 from by norm_num]
      have h2 : (3 : ZMod 104309321) ^ 52154660 = ((104309320 : ℕ) : ZMod 104309321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104309321 - 1) / 5 = 20861864 from by norm_num]
      have h2 : (3 : ZMod 104309321) ^ 20861864 = ((50708351 : ℕ) : ZMod 104309321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104309321 - 1) / 2607733 = 40 from by norm_num]
      have h2 : (3 : ZMod 104309321) ^ 40 = ((80893432 : ℕ) : ZMod 104309321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1736750194651 : Nat.Prime 1736750194651 := by
  refine lucas_primality 1736750194651 (10 : ZMod 1736750194651) ?_ (fun q hq hd => ?_)
  · rw [show 1736750194651 - 1 = 1736750194650 from by norm_num]
    reduce_mod_char
  · have e : 1736750194651 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 37 ^ 1, 104309321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1736750194651 - 1) / 2 = 868375097325 from by norm_num]
      have h2 : (10 : ZMod 1736750194651) ^ 868375097325 = ((1736750194650 : ℕ) : ZMod 1736750194651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1736750194651 - 1) / 3 = 578916731550 from by norm_num]
      have h2 : (10 : ZMod 1736750194651) ^ 578916731550 = ((1436631503551 : ℕ) : ZMod 1736750194651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1736750194651 - 1) / 5 = 347350038930 from by norm_num]
      have h2 : (10 : ZMod 1736750194651) ^ 347350038930 = ((1141161824606 : ℕ) : ZMod 1736750194651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1736750194651 - 1) / 37 = 46939194450 from by norm_num]
      have h2 : (10 : ZMod 1736750194651) ^ 46939194450 = ((1205361474975 : ℕ) : ZMod 1736750194651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_104309321).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1736750194651 - 1) / 104309321 = 16650 from by norm_num]
      have h2 : (10 : ZMod 1736750194651) ^ 16650 = ((882897378896 : ℕ) : ZMod 1736750194651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_278547615885120737739334917394469 : Nat.Prime 278547615885120737739334917394469 := by
  refine lucas_primality 278547615885120737739334917394469 (2 : ZMod 278547615885120737739334917394469) ?_ (fun q hq hd => ?_)
  · rw [show 278547615885120737739334917394469 - 1 = 278547615885120737739334917394468 from by norm_num]
    reduce_mod_char
  · have e : 278547615885120737739334917394469 - 1 = [2 ^ 2, 3581 ^ 1, 5381 ^ 1, 179089 ^ 1, 11618923 ^ 1, 1736750194651 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 2 = 139273807942560368869667458697234 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 139273807942560368869667458697234 = ((278547615885120737739334917394468 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 3581 = 77784868998916709784790538228 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 77784868998916709784790538228 = ((173265935477042219675977310665347 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 5381 = 51765028040349514539924719828 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 51765028040349514539924719828 = ((58422998585298902020372769947938 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 179089 = 1555358597597399827679728612 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 1555358597597399827679728612 = ((83135379983510780338688780714524 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 11618923 = 23973617510428525754007916 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 23973617510428525754007916 = ((55269557204047880258962683038314 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1736750194651).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278547615885120737739334917394469 - 1) / 1736750194651 = 160384387313165028268 from by norm_num]
      have h2 : (2 : ZMod 278547615885120737739334917394469) ^ 160384387313165028268 = ((198930581498051919135550383823928 : ℕ) : ZMod 278547615885120737739334917394469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15041571257796519837924085539301327 : Nat.Prime 15041571257796519837924085539301327 := by
  refine lucas_primality 15041571257796519837924085539301327 (6 : ZMod 15041571257796519837924085539301327) ?_ (fun q hq hd => ?_)
  · rw [show 15041571257796519837924085539301327 - 1 = 15041571257796519837924085539301326 from by norm_num]
    reduce_mod_char
  · have e : 15041571257796519837924085539301327 - 1 = [2 ^ 1, 3 ^ 3, 278547615885120737739334917394469 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15041571257796519837924085539301327 - 1) / 2 = 7520785628898259918962042769650663 from by norm_num]
      have h2 : (6 : ZMod 15041571257796519837924085539301327) ^ 7520785628898259918962042769650663 = ((15041571257796519837924085539301326 : ℕ) : ZMod 15041571257796519837924085539301327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15041571257796519837924085539301327 - 1) / 3 = 5013857085932173279308028513100442 from by norm_num]
      have h2 : (6 : ZMod 15041571257796519837924085539301327) ^ 5013857085932173279308028513100442 = ((853096107894680185436848996484271 : ℕ) : ZMod 15041571257796519837924085539301327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_278547615885120737739334917394469).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15041571257796519837924085539301327 - 1) / 278547615885120737739334917394469 = 54 from by norm_num]
      have h2 : (6 : ZMod 15041571257796519837924085539301327) ^ 54 = ((14564238894356519660489477145727085 : ℕ) : ZMod 15041571257796519837924085539301327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_270748282640337357082633539707423887 : Nat.Prime 270748282640337357082633539707423887 := by
  refine lucas_primality 270748282640337357082633539707423887 (5 : ZMod 270748282640337357082633539707423887) ?_ (fun q hq hd => ?_)
  · rw [show 270748282640337357082633539707423887 - 1 = 270748282640337357082633539707423886 from by norm_num]
    reduce_mod_char
  · have e : 270748282640337357082633539707423887 - 1 = [2 ^ 1, 3 ^ 2, 15041571257796519837924085539301327 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270748282640337357082633539707423887 - 1) / 2 = 135374141320168678541316769853711943 from by norm_num]
      have h2 : (5 : ZMod 270748282640337357082633539707423887) ^ 135374141320168678541316769853711943 = ((270748282640337357082633539707423886 : ℕ) : ZMod 270748282640337357082633539707423887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270748282640337357082633539707423887 - 1) / 3 = 90249427546779119027544513235807962 from by norm_num]
      have h2 : (5 : ZMod 270748282640337357082633539707423887) ^ 90249427546779119027544513235807962 = ((251080064472550477762051181832540932 : ℕ) : ZMod 270748282640337357082633539707423887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15041571257796519837924085539301327).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270748282640337357082633539707423887 - 1) / 15041571257796519837924085539301327 = 18 from by norm_num]
      have h2 : (5 : ZMod 270748282640337357082633539707423887) ^ 18 = ((3814697265625 : ℕ) : ZMod 270748282640337357082633539707423887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_36592782543791024327710625901049544696732978671 : Nat.Prime 36592782543791024327710625901049544696732978671 := by
  refine lucas_primality 36592782543791024327710625901049544696732978671 (3 : ZMod 36592782543791024327710625901049544696732978671) ?_ (fun q hq hd => ?_)
  · rw [show 36592782543791024327710625901049544696732978671 - 1 = 36592782543791024327710625901049544696732978670 from by norm_num]
    reduce_mod_char
  · have e : 36592782543791024327710625901049544696732978671 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 157 ^ 1, 1543 ^ 1, 6199 ^ 1, 270748282640337357082633539707423887 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 2 = 18296391271895512163855312950524772348366489335 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 18296391271895512163855312950524772348366489335 = ((36592782543791024327710625901049544696732978670 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 3 = 12197594181263674775903541967016514898910992890 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 12197594181263674775903541967016514898910992890 = ((35686671789643943656514774934945882696285009597 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 5 = 7318556508758204865542125180209908939346595734 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 7318556508758204865542125180209908939346595734 = ((18745230572846153794285830774299831241974855035 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 157 = 233075048049624358775226916567194552208490310 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 233075048049624358775226916567194552208490310 = ((1969907920970305354692654716818729668364754690 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 1543 = 23715348375755686537725616267692511144998690 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 23715348375755686537725616267692511144998690 = ((16415489143943391201553042207386877954025826648 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 6199 = 5903013799611392858156255186489682964467330 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 5903013799611392858156255186489682964467330 = ((17412954046826586922047535997124750043525003539 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_270748282640337357082633539707423887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (36592782543791024327710625901049544696732978671 - 1) / 270748282640337357082633539707423887 = 135154255410 from by norm_num]
      have h2 : (3 : ZMod 36592782543791024327710625901049544696732978671) ^ 135154255410 = ((4155305937031625422518770263350841925362216121 : ℕ) : ZMod 36592782543791024327710625901049544696732978671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_61127977 : Nat.Prime 61127977 := by
  refine lucas_primality 61127977 (5 : ZMod 61127977) ?_ (fun q hq hd => ?_)
  · rw [show 61127977 - 1 = 61127976 from by norm_num]
    reduce_mod_char
  · have e : 61127977 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 13 ^ 2, 2153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61127977 - 1) / 2 = 30563988 from by norm_num]
      have h2 : (5 : ZMod 61127977) ^ 30563988 = ((61127976 : ℕ) : ZMod 61127977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61127977 - 1) / 3 = 20375992 from by norm_num]
      have h2 : (5 : ZMod 61127977) ^ 20375992 = ((13073983 : ℕ) : ZMod 61127977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61127977 - 1) / 7 = 8732568 from by norm_num]
      have h2 : (5 : ZMod 61127977) ^ 8732568 = ((17276174 : ℕ) : ZMod 61127977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61127977 - 1) / 13 = 4702152 from by norm_num]
      have h2 : (5 : ZMod 61127977) ^ 4702152 = ((15164023 : ℕ) : ZMod 61127977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (61127977 - 1) / 2153 = 28392 from by norm_num]
      have h2 : (5 : ZMod 61127977) ^ 28392 = ((20419191 : ℕ) : ZMod 61127977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_458427808464599360198958190584523975568577060978636244306691569817 : Nat.Prime 458427808464599360198958190584523975568577060978636244306691569817 := by
  refine lucas_primality 458427808464599360198958190584523975568577060978636244306691569817 (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ?_ (fun q hq hd => ?_)
  · rw [show 458427808464599360198958190584523975568577060978636244306691569817 - 1 = 458427808464599360198958190584523975568577060978636244306691569816 from by norm_num]
    reduce_mod_char
  · have e : 458427808464599360198958190584523975568577060978636244306691569817 - 1 = [2 ^ 3, 83 ^ 1, 1181 ^ 1, 261347 ^ 1, 61127977 ^ 1, 36592782543791024327710625901049544696732978671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 2 = 229213904232299680099479095292261987784288530489318122153345784908 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 229213904232299680099479095292261987784288530489318122153345784908 = ((458427808464599360198958190584523975568577060978636244306691569816 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 83 = 5523226608007221207216363741982216573115386276851039088032428552 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 5523226608007221207216363741982216573115386276851039088032428552 = ((458427808442414047854335583048558792488211566660963705695113161096 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 1181 = 388169185829466012022826579665134610981013599473866421936233336 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 388169185829466012022826579665134610981013599473866421936233336 = ((316638672512477021602423510730972269979204987053430921480580440480 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 261347 = 1754096310516666960779952287895112534555885703599567794184328 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 1754096310516666960779952287895112534555885703599567794184328 = ((207472725779390443864629423781694830399932266681646493735439357213 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_61127977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 61127977 = 7499476196711030698741399385497805294105791542531110498008 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 7499476196711030698741399385497805294105791542531110498008 = ((422286024037735236687662851226432883651972069062381585735194881306 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_36592782543791024327710625901049544696732978671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (458427808464599360198958190584523975568577060978636244306691569817 - 1) / 36592782543791024327710625901049544696732978671 = 12527820422401419496 from by norm_num]
      have h2 : (5 : ZMod 458427808464599360198958190584523975568577060978636244306691569817) ^ 12527820422401419496 = ((5974277341798063527199021637918269817880534508566095816254650676 : ℕ) : ZMod 458427808464599360198958190584523975568577060978636244306691569817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6280719119431 : Nat.Prime 6280719119431 := by
  refine lucas_primality 6280719119431 (3 : ZMod 6280719119431) ?_ (fun q hq hd => ?_)
  · rw [show 6280719119431 - 1 = 6280719119430 from by norm_num]
    reduce_mod_char
  · have e : 6280719119431 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 37 ^ 1, 47 ^ 1, 17198497 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 2 = 3140359559715 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 3140359559715 = ((6280719119430 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 3 = 2093573039810 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 2093573039810 = ((5824742761961 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 5 = 1256143823886 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 1256143823886 = ((4763194245979 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 7 = 897245588490 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 897245588490 = ((2793754777425 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 37 = 169749165390 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 169749165390 = ((2222792658477 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 47 = 133632321690 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 133632321690 = ((5449475454470 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6280719119431 - 1) / 17198497 = 365190 from by norm_num]
      have h2 : (3 : ZMod 6280719119431) ^ 365190 = ((2919804527239 : ℕ) : ZMod 6280719119431) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1190204597436709967401788193 : Nat.Prime 1190204597436709967401788193 := by
  refine lucas_primality 1190204597436709967401788193 (5 : ZMod 1190204597436709967401788193) ?_ (fun q hq hd => ?_)
  · rw [show 1190204597436709967401788193 - 1 = 1190204597436709967401788192 from by norm_num]
    reduce_mod_char
  · have e : 1190204597436709967401788193 - 1 = [2 ^ 5, 3 ^ 1, 167 ^ 1, 12113 ^ 1, 975827 ^ 1, 6280719119431 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 2 = 595102298718354983700894096 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 595102298718354983700894096 = ((1190204597436709967401788192 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 3 = 396734865812236655800596064 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 396734865812236655800596064 = ((930999946320383230538027901 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 167 = 7126973637345568667076576 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 7126973637345568667076576 = ((680218423669136118218046434 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 12113 = 98258449387988934813984 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 98258449387988934813984 = ((567828723129753114558748549 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 975827 = 1219688118320880614496 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 1219688118320880614496 = ((1072048699712607320475817981 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6280719119431).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1190204597436709967401788193 - 1) / 6280719119431 = 189501325374432 from by norm_num]
      have h2 : (5 : ZMod 1190204597436709967401788193) ^ 189501325374432 = ((1108944689844331866526141812 : ℕ) : ZMod 1190204597436709967401788193) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2671903153 : Nat.Prime 2671903153 := by
  refine lucas_primality 2671903153 (5 : ZMod 2671903153) ?_ (fun q hq hd => ?_)
  · rw [show 2671903153 - 1 = 2671903152 from by norm_num]
    reduce_mod_char
  · have e : 2671903153 - 1 = [2 ^ 4, 3 ^ 3, 337 ^ 1, 18353 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2671903153 - 1) / 2 = 1335951576 from by norm_num]
      have h2 : (5 : ZMod 2671903153) ^ 1335951576 = ((2671903152 : ℕ) : ZMod 2671903153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2671903153 - 1) / 3 = 890634384 from by norm_num]
      have h2 : (5 : ZMod 2671903153) ^ 890634384 = ((923960691 : ℕ) : ZMod 2671903153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2671903153 - 1) / 337 = 7928496 from by norm_num]
      have h2 : (5 : ZMod 2671903153) ^ 7928496 = ((2099730629 : ℕ) : ZMod 2671903153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2671903153 - 1) / 18353 = 145584 from by norm_num]
      have h2 : (5 : ZMod 2671903153) ^ 145584 = ((616457502 : ℕ) : ZMod 2671903153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3841314164761 : Nat.Prime 3841314164761 := by
  refine lucas_primality 3841314164761 (7 : ZMod 3841314164761) ?_ (fun q hq hd => ?_)
  · rw [show 3841314164761 - 1 = 3841314164760 from by norm_num]
    reduce_mod_char
  · have e : 3841314164761 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 173 ^ 1, 1117 ^ 1, 165653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 2 = 1920657082380 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 1920657082380 = ((3841314164760 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 3 = 1280438054920 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 1280438054920 = ((82128464666 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 5 = 768262832952 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 768262832952 = ((2302784762774 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 173 = 22204128120 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 22204128120 = ((1804403725693 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 1117 = 3438956280 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 3438956280 = ((888914752164 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3841314164761 - 1) / 165653 = 23188920 from by norm_num]
      have h2 : (7 : ZMod 3841314164761) ^ 23188920 = ((3445715309308 : ℕ) : ZMod 3841314164761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_288828413 : Nat.Prime 288828413 := by
  refine lucas_primality 288828413 (2 : ZMod 288828413) ?_ (fun q hq hd => ?_)
  · rw [show 288828413 - 1 = 288828412 from by norm_num]
    reduce_mod_char
  · have e : 288828413 - 1 = [2 ^ 2, 61 ^ 1, 1183723 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (288828413 - 1) / 2 = 144414206 from by norm_num]
      have h2 : (2 : ZMod 288828413) ^ 144414206 = ((288828412 : ℕ) : ZMod 288828413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (288828413 - 1) / 61 = 4734892 from by norm_num]
      have h2 : (2 : ZMod 288828413) ^ 4734892 = ((70835251 : ℕ) : ZMod 288828413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (288828413 - 1) / 1183723 = 244 from by norm_num]
      have h2 : (2 : ZMod 288828413) ^ 244 = ((50035276 : ℕ) : ZMod 288828413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_54231194754050808887 : Nat.Prime 54231194754050808887 := by
  refine lucas_primality 54231194754050808887 (5 : ZMod 54231194754050808887) ?_ (fun q hq hd => ?_)
  · rw [show 54231194754050808887 - 1 = 54231194754050808886 from by norm_num]
    reduce_mod_char
  · have e : 54231194754050808887 - 1 = [2 ^ 1, 7 ^ 2, 29 ^ 1, 191 ^ 2, 1811 ^ 1, 288828413 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 2 = 27115597377025404443 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 27115597377025404443 = ((54231194754050808886 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 7 = 7747313536292972698 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 7747313536292972698 = ((13328191138792119079 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 29 = 1870041198415545134 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 1870041198415545134 = ((16181667710274754428 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 191 = 283932956827491146 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 283932956827491146 = ((179462952949905434 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 1811 = 29945441609083826 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 29945441609083826 = ((18898698470141167046 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_288828413).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54231194754050808887 - 1) / 288828413 = 187762672622 from by norm_num]
      have h2 : (5 : ZMod 54231194754050808887) ^ 187762672622 = ((24218771370314487060 : ℕ) : ZMod 54231194754050808887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3049995907846175495204772167 : Nat.Prime 3049995907846175495204772167 := by
  refine lucas_primality 3049995907846175495204772167 (5 : ZMod 3049995907846175495204772167) ?_ (fun q hq hd => ?_)
  · rw [show 3049995907846175495204772167 - 1 = 3049995907846175495204772166 from by norm_num]
    reduce_mod_char
  · have e : 3049995907846175495204772167 - 1 = [2 ^ 1, 7 ^ 1, 311 ^ 1, 12917 ^ 1, 54231194754050808887 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3049995907846175495204772167 - 1) / 2 = 1524997953923087747602386083 from by norm_num]
      have h2 : (5 : ZMod 3049995907846175495204772167) ^ 1524997953923087747602386083 = ((3049995907846175495204772166 : ℕ) : ZMod 3049995907846175495204772167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3049995907846175495204772167 - 1) / 7 = 435713701120882213600681738 from by norm_num]
      have h2 : (5 : ZMod 3049995907846175495204772167) ^ 435713701120882213600681738 = ((1648236847746292630505442019 : ℕ) : ZMod 3049995907846175495204772167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3049995907846175495204772167 - 1) / 311 = 9807060796933040177507306 from by norm_num]
      have h2 : (5 : ZMod 3049995907846175495204772167) ^ 9807060796933040177507306 = ((964855686915278588801252182 : ℕ) : ZMod 3049995907846175495204772167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3049995907846175495204772167 - 1) / 12917 = 236122621959137221893998 from by norm_num]
      have h2 : (5 : ZMod 3049995907846175495204772167) ^ 236122621959137221893998 = ((51073797287867335152464718 : ℕ) : ZMod 3049995907846175495204772167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_54231194754050808887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3049995907846175495204772167 - 1) / 54231194754050808887 = 56240618 from by norm_num]
      have h2 : (5 : ZMod 3049995907846175495204772167) ^ 56240618 = ((2188060480147115766160512231 : ℕ) : ZMod 3049995907846175495204772167) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_46007081 : Nat.Prime 46007081 := by
  refine lucas_primality 46007081 (3 : ZMod 46007081) ?_ (fun q hq hd => ?_)
  · rw [show 46007081 - 1 = 46007080 from by norm_num]
    reduce_mod_char
  · have e : 46007081 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 2, 23473 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46007081 - 1) / 2 = 23003540 from by norm_num]
      have h2 : (3 : ZMod 46007081) ^ 23003540 = ((46007080 : ℕ) : ZMod 46007081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46007081 - 1) / 5 = 9201416 from by norm_num]
      have h2 : (3 : ZMod 46007081) ^ 9201416 = ((44158363 : ℕ) : ZMod 46007081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46007081 - 1) / 7 = 6572440 from by norm_num]
      have h2 : (3 : ZMod 46007081) ^ 6572440 = ((14437914 : ℕ) : ZMod 46007081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46007081 - 1) / 23473 = 1960 from by norm_num]
      have h2 : (3 : ZMod 46007081) ^ 1960 = ((12415860 : ℕ) : ZMod 46007081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_428785994921 : Nat.Prime 428785994921 := by
  refine lucas_primality 428785994921 (3 : ZMod 428785994921) ?_ (fun q hq hd => ?_)
  · rw [show 428785994921 - 1 = 428785994920 from by norm_num]
    reduce_mod_char
  · have e : 428785994921 - 1 = [2 ^ 3, 5 ^ 1, 233 ^ 1, 46007081 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428785994921 - 1) / 2 = 214392997460 from by norm_num]
      have h2 : (3 : ZMod 428785994921) ^ 214392997460 = ((428785994920 : ℕ) : ZMod 428785994921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428785994921 - 1) / 5 = 85757198984 from by norm_num]
      have h2 : (3 : ZMod 428785994921) ^ 85757198984 = ((182103115722 : ℕ) : ZMod 428785994921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428785994921 - 1) / 233 = 1840283240 from by norm_num]
      have h2 : (3 : ZMod 428785994921) ^ 1840283240 = ((296188038663 : ℕ) : ZMod 428785994921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_46007081).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428785994921 - 1) / 46007081 = 9320 from by norm_num]
      have h2 : (3 : ZMod 428785994921) ^ 9320 = ((201929203030 : ℕ) : ZMod 428785994921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_857571989843 : Nat.Prime 857571989843 := by
  refine lucas_primality 857571989843 (2 : ZMod 857571989843) ?_ (fun q hq hd => ?_)
  · rw [show 857571989843 - 1 = 857571989842 from by norm_num]
    reduce_mod_char
  · have e : 857571989843 - 1 = [2 ^ 1, 428785994921 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857571989843 - 1) / 2 = 428785994921 from by norm_num]
      have h2 : (2 : ZMod 857571989843) ^ 428785994921 = ((857571989842 : ℕ) : ZMod 857571989843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_428785994921).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857571989843 - 1) / 428785994921 = 2 from by norm_num]
      have h2 : (2 : ZMod 857571989843) ^ 2 = ((4 : ℕ) : ZMod 857571989843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9357940013 : Nat.Prime 9357940013 := by
  refine lucas_primality 9357940013 (2 : ZMod 9357940013) ?_ (fun q hq hd => ?_)
  · rw [show 9357940013 - 1 = 9357940012 from by norm_num]
    reduce_mod_char
  · have e : 9357940013 - 1 = [2 ^ 2, 71 ^ 1, 1787 ^ 1, 18439 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9357940013 - 1) / 2 = 4678970006 from by norm_num]
      have h2 : (2 : ZMod 9357940013) ^ 4678970006 = ((9357940012 : ℕ) : ZMod 9357940013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9357940013 - 1) / 71 = 131801972 from by norm_num]
      have h2 : (2 : ZMod 9357940013) ^ 131801972 = ((5315827883 : ℕ) : ZMod 9357940013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9357940013 - 1) / 1787 = 5236676 from by norm_num]
      have h2 : (2 : ZMod 9357940013) ^ 5236676 = ((644090385 : ℕ) : ZMod 9357940013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9357940013 - 1) / 18439 = 507508 from by norm_num]
      have h2 : (2 : ZMod 9357940013) ^ 507508 = ((6644716598 : ℕ) : ZMod 9357940013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1005349580545941002278829932925047441448714307550239169249631491 : Nat.Prime 1005349580545941002278829932925047441448714307550239169249631491 := by
  refine lucas_primality 1005349580545941002278829932925047441448714307550239169249631491 (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ?_ (fun q hq hd => ?_)
  · rw [show 1005349580545941002278829932925047441448714307550239169249631491 - 1 = 1005349580545941002278829932925047441448714307550239169249631490 from by norm_num]
    reduce_mod_char
  · have e : 1005349580545941002278829932925047441448714307550239169249631491 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 347 ^ 1, 25763 ^ 1, 153151 ^ 1, 9357940013 ^ 1, 857571989843 ^ 1, 3049995907846175495204772167 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 2 = 502674790272970501139414966462523720724357153775119584624815745 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 502674790272970501139414966462523720724357153775119584624815745 = ((1005349580545941002278829932925047441448714307550239169249631490 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 3 = 335116526848647000759609977641682480482904769183413056416543830 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 335116526848647000759609977641682480482904769183413056416543830 = ((676042217452797305081311805732181836516429862457833127099506182 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 5 = 201069916109188200455765986585009488289742861510047833849926298 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 201069916109188200455765986585009488289742861510047833849926298 = ((60145503899120861822938361522183535039819907447179757787649878 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 347 = 2897261039037293954694034388832989744808974949712504810517670 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 2897261039037293954694034388832989744808974949712504810517670 = ((652368317121568700877385599218188498478287605175051630628987538 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 25763 = 39023001224466909998013815662968110912887253330366772862230 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 39023001224466909998013815662968110912887253330366772862230 = ((385580074435632056069093908048649239866685259779453496102682088 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 153151 = 6564433667073287162857767385946206302594918136677130212990 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 6564433667073287162857767385946206302594918136677130212990 = ((701512879000340345007379279724641319193899294221118369458905311 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9357940013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 9357940013 = 107432787467040263691293864348160728207556881199494730 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 107432787467040263691293864348160728207556881199494730 = ((17941011459276596697017810254800186701626453095126780657265425 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_857571989843).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 857571989843 = 1172320915856866297683484207152514929938020890293430 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 1172320915856866297683484207152514929938020890293430 = ((892540749868942026972735790741562383106630946727199785611415209 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3049995907846175495204772167).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1005349580545941002278829932925047441448714307550239169249631491 - 1) / 3049995907846175495204772167 = 329623255545903878744538116776639470 from by norm_num]
      have h2 : (13 : ZMod 1005349580545941002278829932925047441448714307550239169249631491) ^ 329623255545903878744538116776639470 = ((742169827843865020836327997106539324497635234382041204056766251 : ℕ) : ZMod 1005349580545941002278829932925047441448714307550239169249631491) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5572311991 : Nat.Prime 5572311991 := by
  refine lucas_primality 5572311991 (11 : ZMod 5572311991) ?_ (fun q hq hd => ?_)
  · rw [show 5572311991 - 1 = 5572311990 from by norm_num]
    reduce_mod_char
  · have e : 5572311991 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 349 ^ 1, 76031 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 2 = 2786155995 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 2786155995 = ((5572311990 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 3 = 1857437330 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 1857437330 = ((2704460701 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 5 = 1114462398 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 1114462398 = ((322509018 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 7 = 796044570 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 796044570 = ((2493368718 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 349 = 15966510 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 15966510 = ((2357567220 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5572311991 - 1) / 76031 = 73290 from by norm_num]
      have h2 : (11 : ZMod 5572311991) ^ 73290 = ((218788779 : ℕ) : ZMod 5572311991) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1324391188753961 : Nat.Prime 1324391188753961 := by
  refine lucas_primality 1324391188753961 (6 : ZMod 1324391188753961) ?_ (fun q hq hd => ?_)
  · rw [show 1324391188753961 - 1 = 1324391188753960 from by norm_num]
    reduce_mod_char
  · have e : 1324391188753961 - 1 = [2 ^ 3, 5 ^ 1, 89 ^ 1, 174467 ^ 1, 2132323 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1324391188753961 - 1) / 2 = 662195594376980 from by norm_num]
      have h2 : (6 : ZMod 1324391188753961) ^ 662195594376980 = ((1324391188753960 : ℕ) : ZMod 1324391188753961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1324391188753961 - 1) / 5 = 264878237750792 from by norm_num]
      have h2 : (6 : ZMod 1324391188753961) ^ 264878237750792 = ((51903554305320 : ℕ) : ZMod 1324391188753961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1324391188753961 - 1) / 89 = 14880799873640 from by norm_num]
      have h2 : (6 : ZMod 1324391188753961) ^ 14880799873640 = ((233474498662006 : ℕ) : ZMod 1324391188753961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1324391188753961 - 1) / 174467 = 7591069880 from by norm_num]
      have h2 : (6 : ZMod 1324391188753961) ^ 7591069880 = ((262579518952156 : ℕ) : ZMod 1324391188753961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1324391188753961 - 1) / 2132323 = 621102520 from by norm_num]
      have h2 : (6 : ZMod 1324391188753961) ^ 621102520 = ((52312206149346 : ℕ) : ZMod 1324391188753961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_387345425955593089 : Nat.Prime 387345425955593089 := by
  refine lucas_primality 387345425955593089 (17 : ZMod 387345425955593089) ?_ (fun q hq hd => ?_)
  · rw [show 387345425955593089 - 1 = 387345425955593088 from by norm_num]
    reduce_mod_char
  · have e : 387345425955593089 - 1 = [2 ^ 7, 3 ^ 1, 2111 ^ 1, 105031 ^ 1, 4549477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (387345425955593089 - 1) / 2 = 193672712977796544 from by norm_num]
      have h2 : (17 : ZMod 387345425955593089) ^ 193672712977796544 = ((387345425955593088 : ℕ) : ZMod 387345425955593089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (387345425955593089 - 1) / 3 = 129115141985197696 from by norm_num]
      have h2 : (17 : ZMod 387345425955593089) ^ 129115141985197696 = ((22037253349012854 : ℕ) : ZMod 387345425955593089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (387345425955593089 - 1) / 2111 = 183489069614208 from by norm_num]
      have h2 : (17 : ZMod 387345425955593089) ^ 183489069614208 = ((47352287710810556 : ℕ) : ZMod 387345425955593089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (387345425955593089 - 1) / 105031 = 3687915243648 from by norm_num]
      have h2 : (17 : ZMod 387345425955593089) ^ 3687915243648 = ((118882105089030789 : ℕ) : ZMod 387345425955593089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (387345425955593089 - 1) / 4549477 = 85140649344 from by norm_num]
      have h2 : (17 : ZMod 387345425955593089) ^ 85140649344 = ((185560082393127137 : ℕ) : ZMod 387345425955593089) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_185680639 : Nat.Prime 185680639 := by
  refine lucas_primality 185680639 (3 : ZMod 185680639) ?_ (fun q hq hd => ?_)
  · rw [show 185680639 - 1 = 185680638 from by norm_num]
    reduce_mod_char
  · have e : 185680639 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 13 ^ 2, 31 ^ 1, 179 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 2 = 92840319 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 92840319 = ((185680638 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 3 = 61893546 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 61893546 = ((182461416 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 11 = 16880058 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 16880058 = ((11944592 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 13 = 14283126 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 14283126 = ((4925205 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 31 = 5989698 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 5989698 = ((154161402 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (185680639 - 1) / 179 = 1037322 from by norm_num]
      have h2 : (3 : ZMod 185680639) ^ 1037322 = ((115564028 : ℕ) : ZMod 185680639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_742722557 : Nat.Prime 742722557 := by
  refine lucas_primality 742722557 (2 : ZMod 742722557) ?_ (fun q hq hd => ?_)
  · rw [show 742722557 - 1 = 742722556 from by norm_num]
    reduce_mod_char
  · have e : 742722557 - 1 = [2 ^ 2, 185680639 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (742722557 - 1) / 2 = 371361278 from by norm_num]
      have h2 : (2 : ZMod 742722557) ^ 371361278 = ((742722556 : ℕ) : ZMod 742722557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_185680639).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (742722557 - 1) / 185680639 = 4 from by norm_num]
      have h2 : (2 : ZMod 742722557) ^ 4 = ((16 : ℕ) : ZMod 742722557) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49043825759657387 : Nat.Prime 49043825759657387 := by
  refine lucas_primality 49043825759657387 (2 : ZMod 49043825759657387) ?_ (fun q hq hd => ?_)
  · rw [show 49043825759657387 - 1 = 49043825759657386 from by norm_num]
    reduce_mod_char
  · have e : 49043825759657387 - 1 = [2 ^ 1, 7 ^ 2, 673801 ^ 1, 742722557 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49043825759657387 - 1) / 2 = 24521912879828693 from by norm_num]
      have h2 : (2 : ZMod 49043825759657387) ^ 24521912879828693 = ((49043825759657386 : ℕ) : ZMod 49043825759657387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49043825759657387 - 1) / 7 = 7006260822808198 from by norm_num]
      have h2 : (2 : ZMod 49043825759657387) ^ 7006260822808198 = ((10024818350583239 : ℕ) : ZMod 49043825759657387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49043825759657387 - 1) / 673801 = 72786810586 from by norm_num]
      have h2 : (2 : ZMod 49043825759657387) ^ 72786810586 = ((8084845797141308 : ℕ) : ZMod 49043825759657387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_742722557).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49043825759657387 - 1) / 742722557 = 66032498 from by norm_num]
      have h2 : (2 : ZMod 49043825759657387) ^ 66032498 = ((46427987106603510 : ℕ) : ZMod 49043825759657387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_113981409476198276255719494149990659 : Nat.Prime 113981409476198276255719494149990659 := by
  refine lucas_primality 113981409476198276255719494149990659 (2 : ZMod 113981409476198276255719494149990659) ?_ (fun q hq hd => ?_)
  · rw [show 113981409476198276255719494149990659 - 1 = 113981409476198276255719494149990658 from by norm_num]
    reduce_mod_char
  · have e : 113981409476198276255719494149990659 - 1 = [2 ^ 1, 3 ^ 1, 49043825759657387 ^ 1, 387345425955593089 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113981409476198276255719494149990659 - 1) / 2 = 56990704738099138127859747074995329 from by norm_num]
      have h2 : (2 : ZMod 113981409476198276255719494149990659) ^ 56990704738099138127859747074995329 = ((113981409476198276255719494149990658 : ℕ) : ZMod 113981409476198276255719494149990659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113981409476198276255719494149990659 - 1) / 3 = 37993803158732758751906498049996886 from by norm_num]
      have h2 : (2 : ZMod 113981409476198276255719494149990659) ^ 37993803158732758751906498049996886 = ((22791736905612602302852513695912021 : ℕ) : ZMod 113981409476198276255719494149990659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_49043825759657387).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113981409476198276255719494149990659 - 1) / 49043825759657387 = 2324072555733558534 from by norm_num]
      have h2 : (2 : ZMod 113981409476198276255719494149990659) ^ 2324072555733558534 = ((93506572351561173184798245510588065 : ℕ) : ZMod 113981409476198276255719494149990659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_387345425955593089).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113981409476198276255719494149990659 - 1) / 387345425955593089 = 294262954557944322 from by norm_num]
      have h2 : (2 : ZMod 113981409476198276255719494149990659) ^ 294262954557944322 = ((62955625692091776458215643339951489 : ℕ) : ZMod 113981409476198276255719494149990659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_113080919977 : Nat.Prime 113080919977 := by
  refine lucas_primality 113080919977 (5 : ZMod 113080919977) ?_ (fun q hq hd => ?_)
  · rw [show 113080919977 - 1 = 113080919976 from by norm_num]
    reduce_mod_char
  · have e : 113080919977 - 1 = [2 ^ 3, 3 ^ 2, 229 ^ 1, 2591 ^ 1, 2647 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113080919977 - 1) / 2 = 56540459988 from by norm_num]
      have h2 : (5 : ZMod 113080919977) ^ 56540459988 = ((113080919976 : ℕ) : ZMod 113080919977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113080919977 - 1) / 3 = 37693639992 from by norm_num]
      have h2 : (5 : ZMod 113080919977) ^ 37693639992 = ((50694092610 : ℕ) : ZMod 113080919977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113080919977 - 1) / 229 = 493803144 from by norm_num]
      have h2 : (5 : ZMod 113080919977) ^ 493803144 = ((39943035576 : ℕ) : ZMod 113080919977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113080919977 - 1) / 2591 = 43643736 from by norm_num]
      have h2 : (5 : ZMod 113080919977) ^ 43643736 = ((66845511627 : ℕ) : ZMod 113080919977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (113080919977 - 1) / 2647 = 42720408 from by norm_num]
      have h2 : (5 : ZMod 113080919977) ^ 42720408 = ((50454240185 : ℕ) : ZMod 113080919977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1419693835327992540902041413024708359489718038816664067 : Nat.Prime 1419693835327992540902041413024708359489718038816664067 := by
  refine lucas_primality 1419693835327992540902041413024708359489718038816664067 (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ?_ (fun q hq hd => ?_)
  · rw [show 1419693835327992540902041413024708359489718038816664067 - 1 = 1419693835327992540902041413024708359489718038816664066 from by norm_num]
    reduce_mod_char
  · have e : 1419693835327992540902041413024708359489718038816664067 - 1 = [2 ^ 1, 3 ^ 3, 47 ^ 1, 43399 ^ 1, 113080919977 ^ 1, 113981409476198276255719494149990659 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 2 = 709846917663996270451020706512354179744859019408332033 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 709846917663996270451020706512354179744859019408332033 = ((1419693835327992540902041413024708359489718038816664066 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 3 = 473231278442664180300680471008236119829906012938888022 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 473231278442664180300680471008236119829906012938888022 = ((853791538386900229227504785545754785216076807156771387 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 47 = 30206251815489202997915774745206560840206766783333278 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 30206251815489202997915774745206560840206766783333278 = ((1107579036628697406768804613030128405736372526825696598 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 43399 = 32712593270075175485657305767983325871326943911534 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 32712593270075175485657305767983325871326943911534 = ((1051675316479160844513842077194083588840711098250889674 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_113080919977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 113080919977 = 12554671783858408579721360688949998420030258 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 12554671783858408579721360688949998420030258 = ((969182592187421683108402486811854150660182453582787836 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_113981409476198276255719494149990659).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1419693835327992540902041413024708359489718038816664067 - 1) / 113981409476198276255719494149990659 = 12455485871355666774 from by norm_num]
      have h2 : (5 : ZMod 1419693835327992540902041413024708359489718038816664067) ^ 12455485871355666774 = ((1187846433241970342207992176384228649068562715758571236 : ℕ) : ZMod 1419693835327992540902041413024708359489718038816664067) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_504309322960550822349386758900289002291375600620610676536009 : Nat.Prime 504309322960550822349386758900289002291375600620610676536009 := by
  refine lucas_primality 504309322960550822349386758900289002291375600620610676536009 (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ?_ (fun q hq hd => ?_)
  · rw [show 504309322960550822349386758900289002291375600620610676536009 - 1 = 504309322960550822349386758900289002291375600620610676536008 from by norm_num]
    reduce_mod_char
  · have e : 504309322960550822349386758900289002291375600620610676536009 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 2, 41 ^ 1, 1419693835327992540902041413024708359489718038816664067 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (504309322960550822349386758900289002291375600620610676536009 - 1) / 2 = 252154661480275411174693379450144501145687800310305338268004 from by norm_num]
      have h2 : (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ^ 252154661480275411174693379450144501145687800310305338268004 = ((504309322960550822349386758900289002291375600620610676536008 : ℕ) : ZMod 504309322960550822349386758900289002291375600620610676536009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (504309322960550822349386758900289002291375600620610676536009 - 1) / 3 = 168103107653516940783128919633429667430458533540203558845336 from by norm_num]
      have h2 : (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ^ 168103107653516940783128919633429667430458533540203558845336 = ((38160872337935636993714600358412720833689701234604027262921 : ℕ) : ZMod 504309322960550822349386758900289002291375600620610676536009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (504309322960550822349386758900289002291375600620610676536009 - 1) / 19 = 26542595945292148544704566257909947489019768453716351396632 from by norm_num]
      have h2 : (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ^ 26542595945292148544704566257909947489019768453716351396632 = ((233890362943483894328711914458611543310660633914528043414723 : ℕ) : ZMod 504309322960550822349386758900289002291375600620610676536009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (504309322960550822349386758900289002291375600620610676536009 - 1) / 41 = 12300227389281727374375286802446073226618917088307577476488 from by norm_num]
      have h2 : (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ^ 12300227389281727374375286802446073226618917088307577476488 = ((251717725131937414544060990109194427845204062489788706382948 : ℕ) : ZMod 504309322960550822349386758900289002291375600620610676536009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1419693835327992540902041413024708359489718038816664067).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (504309322960550822349386758900289002291375600620610676536009 - 1) / 1419693835327992540902041413024708359489718038816664067 = 355224 from by norm_num]
      have h2 : (14 : ZMod 504309322960550822349386758900289002291375600620610676536009) ^ 355224 = ((337281807202352763010712909904707538080794555842144564589316 : ℕ) : ZMod 504309322960550822349386758900289002291375600620610676536009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_291197899 : Nat.Prime 291197899 := by
  refine lucas_primality 291197899 (2 : ZMod 291197899) ?_ (fun q hq hd => ?_)
  · rw [show 291197899 - 1 = 291197898 from by norm_num]
    reduce_mod_char
  · have e : 291197899 - 1 = [2 ^ 1, 3 ^ 2, 16177661 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291197899 - 1) / 2 = 145598949 from by norm_num]
      have h2 : (2 : ZMod 291197899) ^ 145598949 = ((291197898 : ℕ) : ZMod 291197899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291197899 - 1) / 3 = 97065966 from by norm_num]
      have h2 : (2 : ZMod 291197899) ^ 97065966 = ((170000220 : ℕ) : ZMod 291197899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291197899 - 1) / 16177661 = 18 from by norm_num]
      have h2 : (2 : ZMod 291197899) ^ 18 = ((262144 : ℕ) : ZMod 291197899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22692469873273 : Nat.Prime 22692469873273 := by
  refine lucas_primality 22692469873273 (5 : ZMod 22692469873273) ?_ (fun q hq hd => ?_)
  · rw [show 22692469873273 - 1 = 22692469873272 from by norm_num]
    reduce_mod_char
  · have e : 22692469873273 - 1 = [2 ^ 3, 3 ^ 1, 17 ^ 1, 191 ^ 1, 291197899 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22692469873273 - 1) / 2 = 11346234936636 from by norm_num]
      have h2 : (5 : ZMod 22692469873273) ^ 11346234936636 = ((22692469873272 : ℕ) : ZMod 22692469873273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22692469873273 - 1) / 3 = 7564156624424 from by norm_num]
      have h2 : (5 : ZMod 22692469873273) ^ 7564156624424 = ((8695820306445 : ℕ) : ZMod 22692469873273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22692469873273 - 1) / 17 = 1334851169016 from by norm_num]
      have h2 : (5 : ZMod 22692469873273) ^ 1334851169016 = ((7605772402680 : ℕ) : ZMod 22692469873273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22692469873273 - 1) / 191 = 118808742792 from by norm_num]
      have h2 : (5 : ZMod 22692469873273) ^ 118808742792 = ((5134701803325 : ℕ) : ZMod 22692469873273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_291197899).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22692469873273 - 1) / 291197899 = 77928 from by norm_num]
      have h2 : (5 : ZMod 22692469873273) ^ 77928 = ((10189516832143 : ℕ) : ZMod 22692469873273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_287391390277 : Nat.Prime 287391390277 := by
  refine lucas_primality 287391390277 (2 : ZMod 287391390277) ?_ (fun q hq hd => ?_)
  · rw [show 287391390277 - 1 = 287391390276 from by norm_num]
    reduce_mod_char
  · have e : 287391390277 - 1 = [2 ^ 2, 3 ^ 1, 41903 ^ 1, 571541 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (287391390277 - 1) / 2 = 143695695138 from by norm_num]
      have h2 : (2 : ZMod 287391390277) ^ 143695695138 = ((287391390276 : ℕ) : ZMod 287391390277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (287391390277 - 1) / 3 = 95797130092 from by norm_num]
      have h2 : (2 : ZMod 287391390277) ^ 95797130092 = ((30283273290 : ℕ) : ZMod 287391390277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (287391390277 - 1) / 41903 = 6858492 from by norm_num]
      have h2 : (2 : ZMod 287391390277) ^ 6858492 = ((91404434517 : ℕ) : ZMod 287391390277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (287391390277 - 1) / 571541 = 502836 from by norm_num]
      have h2 : (2 : ZMod 287391390277) ^ 502836 = ((75364028279 : ℕ) : ZMod 287391390277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_80707842503 : Nat.Prime 80707842503 := by
  refine lucas_primality 80707842503 (5 : ZMod 80707842503) ?_ (fun q hq hd => ?_)
  · rw [show 80707842503 - 1 = 80707842502 from by norm_num]
    reduce_mod_char
  · have e : 80707842503 - 1 = [2 ^ 1, 7 ^ 1, 1523 ^ 1, 3785191 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80707842503 - 1) / 2 = 40353921251 from by norm_num]
      have h2 : (5 : ZMod 80707842503) ^ 40353921251 = ((80707842502 : ℕ) : ZMod 80707842503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80707842503 - 1) / 7 = 11529691786 from by norm_num]
      have h2 : (5 : ZMod 80707842503) ^ 11529691786 = ((634279621 : ℕ) : ZMod 80707842503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80707842503 - 1) / 1523 = 52992674 from by norm_num]
      have h2 : (5 : ZMod 80707842503) ^ 52992674 = ((69760166737 : ℕ) : ZMod 80707842503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (80707842503 - 1) / 3785191 = 21322 from by norm_num]
      have h2 : (5 : ZMod 80707842503) ^ 21322 = ((11810168155 : ℕ) : ZMod 80707842503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_266507551836102754532873191 : Nat.Prime 266507551836102754532873191 := by
  refine lucas_primality 266507551836102754532873191 (6 : ZMod 266507551836102754532873191) ?_ (fun q hq hd => ?_)
  · rw [show 266507551836102754532873191 - 1 = 266507551836102754532873190 from by norm_num]
    reduce_mod_char
  · have e : 266507551836102754532873191 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 383 ^ 1, 80707842503 ^ 1, 287391390277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 2 = 133253775918051377266436595 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 133253775918051377266436595 = ((266507551836102754532873190 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 3 = 88835850612034251510957730 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 88835850612034251510957730 = ((48586811657801449339245445 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 5 = 53301510367220550906574638 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 53301510367220550906574638 = ((174050401366906946627378126 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 383 = 695842171895829646299930 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 695842171895829646299930 = ((266507223579135359995795564 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_80707842503).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 80707842503 = 3302127074282730 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 3302127074282730 = ((249925790846536980942194322 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_287391390277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (266507551836102754532873191 - 1) / 287391390277 = 927333110359470 from by norm_num]
      have h2 : (6 : ZMod 266507551836102754532873191) ^ 927333110359470 = ((92079241343095184096347548 : ℕ) : ZMod 266507551836102754532873191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1371903593 : Nat.Prime 1371903593 := by
  refine lucas_primality 1371903593 (5 : ZMod 1371903593) ?_ (fun q hq hd => ?_)
  · rw [show 1371903593 - 1 = 1371903592 from by norm_num]
    reduce_mod_char
  · have e : 1371903593 - 1 = [2 ^ 3, 97 ^ 1, 1767917 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1371903593 - 1) / 2 = 685951796 from by norm_num]
      have h2 : (5 : ZMod 1371903593) ^ 685951796 = ((1371903592 : ℕ) : ZMod 1371903593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1371903593 - 1) / 97 = 14143336 from by norm_num]
      have h2 : (5 : ZMod 1371903593) ^ 14143336 = ((154748729 : ℕ) : ZMod 1371903593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1371903593 - 1) / 1767917 = 776 from by norm_num]
      have h2 : (5 : ZMod 1371903593) ^ 776 = ((891985476 : ℕ) : ZMod 1371903593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_907284546446671 : Nat.Prime 907284546446671 := by
  refine lucas_primality 907284546446671 (17 : ZMod 907284546446671) ?_ (fun q hq hd => ?_)
  · rw [show 907284546446671 - 1 = 907284546446670 from by norm_num]
    reduce_mod_char
  · have e : 907284546446671 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 7 ^ 1, 401 ^ 1, 49627 ^ 1, 72367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 2 = 453642273223335 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 453642273223335 = ((907284546446670 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 3 = 302428182148890 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 302428182148890 = ((760387119674679 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 5 = 181456909289334 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 181456909289334 = ((617689680103184 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 7 = 129612078063810 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 129612078063810 = ((189634082928785 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 401 = 2262554978670 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 2262554978670 = ((235563190995013 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 49627 = 18282075210 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 18282075210 = ((561744441298173 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (907284546446671 - 1) / 72367 = 12537269010 from by norm_num]
      have h2 : (17 : ZMod 907284546446671) ^ 12537269010 = ((6854428594047 : ℕ) : ZMod 907284546446671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4571750741 : Nat.Prime 4571750741 := by
  refine lucas_primality 4571750741 (2 : ZMod 4571750741) ?_ (fun q hq hd => ?_)
  · rw [show 4571750741 - 1 = 4571750740 from by norm_num]
    reduce_mod_char
  · have e : 4571750741 - 1 = [2 ^ 2, 5 ^ 1, 19 ^ 1, 12030923 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4571750741 - 1) / 2 = 2285875370 from by norm_num]
      have h2 : (2 : ZMod 4571750741) ^ 2285875370 = ((4571750740 : ℕ) : ZMod 4571750741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4571750741 - 1) / 5 = 914350148 from by norm_num]
      have h2 : (2 : ZMod 4571750741) ^ 914350148 = ((3494055251 : ℕ) : ZMod 4571750741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4571750741 - 1) / 19 = 240618460 from by norm_num]
      have h2 : (2 : ZMod 4571750741) ^ 240618460 = ((1661802988 : ℕ) : ZMod 4571750741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4571750741 - 1) / 12030923 = 380 from by norm_num]
      have h2 : (2 : ZMod 4571750741) ^ 380 = ((3060874469 : ℕ) : ZMod 4571750741) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9143501483 : Nat.Prime 9143501483 := by
  refine lucas_primality 9143501483 (2 : ZMod 9143501483) ?_ (fun q hq hd => ?_)
  · rw [show 9143501483 - 1 = 9143501482 from by norm_num]
    reduce_mod_char
  · have e : 9143501483 - 1 = [2 ^ 1, 4571750741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9143501483 - 1) / 2 = 4571750741 from by norm_num]
      have h2 : (2 : ZMod 9143501483) ^ 4571750741 = ((9143501482 : ℕ) : ZMod 9143501483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4571750741).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9143501483 - 1) / 4571750741 = 2 from by norm_num]
      have h2 : (2 : ZMod 9143501483) ^ 2 = ((4 : ℕ) : ZMod 9143501483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2764913093 : Nat.Prime 2764913093 := by
  refine lucas_primality 2764913093 (2 : ZMod 2764913093) ?_ (fun q hq hd => ?_)
  · rw [show 2764913093 - 1 = 2764913092 from by norm_num]
    reduce_mod_char
  · have e : 2764913093 - 1 = [2 ^ 2, 499 ^ 1, 647 ^ 1, 2141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2764913093 - 1) / 2 = 1382456546 from by norm_num]
      have h2 : (2 : ZMod 2764913093) ^ 1382456546 = ((2764913092 : ℕ) : ZMod 2764913093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2764913093 - 1) / 499 = 5540908 from by norm_num]
      have h2 : (2 : ZMod 2764913093) ^ 5540908 = ((2747933991 : ℕ) : ZMod 2764913093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2764913093 - 1) / 647 = 4273436 from by norm_num]
      have h2 : (2 : ZMod 2764913093) ^ 4273436 = ((637546262 : ℕ) : ZMod 2764913093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2764913093 - 1) / 2141 = 1291412 from by norm_num]
      have h2 : (2 : ZMod 2764913093) ^ 1291412 = ((1700297131 : ℕ) : ZMod 2764913093) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4499059465218602986753482277322389 : Nat.Prime 4499059465218602986753482277322389 := by
  refine lucas_primality 4499059465218602986753482277322389 (2 : ZMod 4499059465218602986753482277322389) ?_ (fun q hq hd => ?_)
  · rw [show 4499059465218602986753482277322389 - 1 = 4499059465218602986753482277322388 from by norm_num]
    reduce_mod_char
  · have e : 4499059465218602986753482277322389 - 1 = [2 ^ 2, 3 ^ 1, 11 ^ 1, 181 ^ 1, 409 ^ 1, 18211759 ^ 1, 2764913093 ^ 1, 9143501483 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 2 = 2249529732609301493376741138661194 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 2249529732609301493376741138661194 = ((4499059465218602986753482277322388 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 3 = 1499686488406200995584494092440796 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 1499686488406200995584494092440796 = ((2316088216085456386917542846516087 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 11 = 409005405928963907886680207029308 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 409005405928963907886680207029308 = ((4061357511800844903840739587300696 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 181 = 24856682128279574512450178327748 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 24856682128279574512450178327748 = ((2693840039775366989776213958335764 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 409 = 11000145391732525639984064247732 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 11000145391732525639984064247732 = ((3860743114136099988788159770679227 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 18211759 = 247041456304061732134357932 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 247041456304061732134357932 = ((1495191047668579947238549728110957 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2764913093).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 2764913093 = 1627197424978378149245316 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 1627197424978378149245316 = ((938904530685592491417684190845794 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9143501483).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4499059465218602986753482277322389 - 1) / 9143501483 = 492049951933999482543036 from by norm_num]
      have h2 : (2 : ZMod 4499059465218602986753482277322389) ^ 492049951933999482543036 = ((3553353118587178749164784917529492 : ℕ) : ZMod 4499059465218602986753482277322389) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1744959420643 : Nat.Prime 1744959420643 := by
  refine lucas_primality 1744959420643 (31 : ZMod 1744959420643) ?_ (fun q hq hd => ?_)
  · rw [show 1744959420643 - 1 = 1744959420642 from by norm_num]
    reduce_mod_char
  · have e : 1744959420643 - 1 = [2 ^ 1, 3 ^ 1, 62327 ^ 1, 4666141 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1744959420643 - 1) / 2 = 872479710321 from by norm_num]
      have h2 : (31 : ZMod 1744959420643) ^ 872479710321 = ((1744959420642 : ℕ) : ZMod 1744959420643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1744959420643 - 1) / 3 = 581653140214 from by norm_num]
      have h2 : (31 : ZMod 1744959420643) ^ 581653140214 = ((210111499204 : ℕ) : ZMod 1744959420643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1744959420643 - 1) / 62327 = 27996846 from by norm_num]
      have h2 : (31 : ZMod 1744959420643) ^ 27996846 = ((734347471739 : ℕ) : ZMod 1744959420643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1744959420643 - 1) / 4666141 = 373962 from by norm_num]
      have h2 : (31 : ZMod 1744959420643) ^ 373962 = ((1596595398066 : ℕ) : ZMod 1744959420643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_69001157 : Nat.Prime 69001157 := by
  refine lucas_primality 69001157 (2 : ZMod 69001157) ?_ (fun q hq hd => ?_)
  · rw [show 69001157 - 1 = 69001156 from by norm_num]
    reduce_mod_char
  · have e : 69001157 - 1 = [2 ^ 2, 7 ^ 1, 67 ^ 1, 36781 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69001157 - 1) / 2 = 34500578 from by norm_num]
      have h2 : (2 : ZMod 69001157) ^ 34500578 = ((69001156 : ℕ) : ZMod 69001157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69001157 - 1) / 7 = 9857308 from by norm_num]
      have h2 : (2 : ZMod 69001157) ^ 9857308 = ((46631673 : ℕ) : ZMod 69001157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69001157 - 1) / 67 = 1029868 from by norm_num]
      have h2 : (2 : ZMod 69001157) ^ 1029868 = ((43089739 : ℕ) : ZMod 69001157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69001157 - 1) / 36781 = 1876 from by norm_num]
      have h2 : (2 : ZMod 69001157) ^ 1876 = ((21507618 : ℕ) : ZMod 69001157) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5382090247 : Nat.Prime 5382090247 := by
  refine lucas_primality 5382090247 (3 : ZMod 5382090247) ?_ (fun q hq hd => ?_)
  · rw [show 5382090247 - 1 = 5382090246 from by norm_num]
    reduce_mod_char
  · have e : 5382090247 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 69001157 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5382090247 - 1) / 2 = 2691045123 from by norm_num]
      have h2 : (3 : ZMod 5382090247) ^ 2691045123 = ((5382090246 : ℕ) : ZMod 5382090247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5382090247 - 1) / 3 = 1794030082 from by norm_num]
      have h2 : (3 : ZMod 5382090247) ^ 1794030082 = ((4649185989 : ℕ) : ZMod 5382090247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5382090247 - 1) / 13 = 414006942 from by norm_num]
      have h2 : (3 : ZMod 5382090247) ^ 414006942 = ((4458002457 : ℕ) : ZMod 5382090247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_69001157).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5382090247 - 1) / 69001157 = 78 from by norm_num]
      have h2 : (3 : ZMod 5382090247) ^ 78 = ((2975141105 : ℕ) : ZMod 5382090247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12872193124359179360957763595281172943047231391521 : Nat.Prime 12872193124359179360957763595281172943047231391521 := by
  refine lucas_primality 12872193124359179360957763595281172943047231391521 (44 : ZMod 12872193124359179360957763595281172943047231391521) ?_ (fun q hq hd => ?_)
  · rw [show 12872193124359179360957763595281172943047231391521 - 1 = 12872193124359179360957763595281172943047231391520 from by norm_num]
    reduce_mod_char
  · have e : 12872193124359179360957763595281172943047231391521 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 29 ^ 1, 103 ^ 1, 1289 ^ 1, 14221 ^ 1, 33617 ^ 1, 7019489 ^ 1, 5382090247 ^ 1, 1744959420643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 2 = 6436096562179589680478881797640586471523615695760 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 6436096562179589680478881797640586471523615695760 = ((12872193124359179360957763595281172943047231391520 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 3 = 4290731041453059786985921198427057647682410463840 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 4290731041453059786985921198427057647682410463840 = ((9187639135354070626237733348221395782828488826001 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 5 = 2574438624871835872191552719056234588609446278304 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 2574438624871835872191552719056234588609446278304 = ((6804134967690941165426474407790145855543716901970 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 13 = 990168701873783027765981815021628687926710107040 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 990168701873783027765981815021628687926710107040 = ((12232658457578703139894106360850828546303350643072 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 17 = 757187830844657609468103740898892526061601846560 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 757187830844657609468103740898892526061601846560 = ((12709572156413979637543448942061394586450020585586 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 29 = 443868728426178598653715986044178377346456254880 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 443868728426178598653715986044178377346456254880 = ((307123385002587673347473773574610405986370121164 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 103 = 124972748780186207387939452381370611097545935840 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 124972748780186207387939452381370611097545935840 = ((6861699741289507002578039051704068397435865466434 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 1289 = 9986185511527679876615797979271662484908635680 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 9986185511527679876615797979271662484908635680 = ((3424362825229279486524556657746782751670154106492 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 14221 = 905153865716839839741070501039390545182985120 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 905153865716839839741070501039390545182985120 = ((8365811559277082776712697269011400035161775037481 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 33617 = 382907253007680023825973870222838829849398560 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 382907253007680023825973870222838829849398560 = ((8104791535349114783142485598310196315588961527980 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 7019489 = 1833779228710121115790303766453822057851680 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 1833779228710121115790303766453822057851680 = ((6907278195484926471722461928056242216452255616959 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5382090247).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 5382090247 = 2391671736001490233085971439170699016160 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 2391671736001490233085971439170699016160 = ((5693716890472409601349176914156501469729631546872 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1744959420643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12872193124359179360957763595281172943047231391521 - 1) / 1744959420643 = 7376786515537367414233183914345260640 from by norm_num]
      have h2 : (44 : ZMod 12872193124359179360957763595281172943047231391521) ^ 7376786515537367414233183914345260640 = ((11504463711986922253970009059487329873376106800223 : ℕ) : ZMod 12872193124359179360957763595281172943047231391521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_105821803 : Nat.Prime 105821803 := by
  refine lucas_primality 105821803 (5 : ZMod 105821803) ?_ (fun q hq hd => ?_)
  · rw [show 105821803 - 1 = 105821802 from by norm_num]
    reduce_mod_char
  · have e : 105821803 - 1 = [2 ^ 1, 3 ^ 4, 419 ^ 1, 1559 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105821803 - 1) / 2 = 52910901 from by norm_num]
      have h2 : (5 : ZMod 105821803) ^ 52910901 = ((105821802 : ℕ) : ZMod 105821803) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105821803 - 1) / 3 = 35273934 from by norm_num]
      have h2 : (5 : ZMod 105821803) ^ 35273934 = ((81451639 : ℕ) : ZMod 105821803) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105821803 - 1) / 419 = 252558 from by norm_num]
      have h2 : (5 : ZMod 105821803) ^ 252558 = ((104483993 : ℕ) : ZMod 105821803) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105821803 - 1) / 1559 = 67878 from by norm_num]
      have h2 : (5 : ZMod 105821803) ^ 67878 = ((59787246 : ℕ) : ZMod 105821803) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47610049 : Nat.Prime 47610049 := by
  refine lucas_primality 47610049 (13 : ZMod 47610049) ?_ (fun q hq hd => ?_)
  · rw [show 47610049 - 1 = 47610048 from by norm_num]
    reduce_mod_char
  · have e : 47610049 - 1 = [2 ^ 6, 3 ^ 1, 19 ^ 1, 31 ^ 1, 421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47610049 - 1) / 2 = 23805024 from by norm_num]
      have h2 : (13 : ZMod 47610049) ^ 23805024 = ((47610048 : ℕ) : ZMod 47610049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47610049 - 1) / 3 = 15870016 from by norm_num]
      have h2 : (13 : ZMod 47610049) ^ 15870016 = ((24571538 : ℕ) : ZMod 47610049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47610049 - 1) / 19 = 2505792 from by norm_num]
      have h2 : (13 : ZMod 47610049) ^ 2505792 = ((32453135 : ℕ) : ZMod 47610049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47610049 - 1) / 31 = 1535808 from by norm_num]
      have h2 : (13 : ZMod 47610049) ^ 1535808 = ((32617008 : ℕ) : ZMod 47610049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47610049 - 1) / 421 = 113088 from by norm_num]
      have h2 : (13 : ZMod 47610049) ^ 113088 = ((22253001 : ℕ) : ZMod 47610049) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7670841701 : Nat.Prime 7670841701 := by
  refine lucas_primality 7670841701 (7 : ZMod 7670841701) ?_ (fun q hq hd => ?_)
  · rw [show 7670841701 - 1 = 7670841700 from by norm_num]
    reduce_mod_char
  · have e : 7670841701 - 1 = [2 ^ 2, 5 ^ 2, 41 ^ 1, 211 ^ 1, 8867 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7670841701 - 1) / 2 = 3835420850 from by norm_num]
      have h2 : (7 : ZMod 7670841701) ^ 3835420850 = ((7670841700 : ℕ) : ZMod 7670841701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7670841701 - 1) / 5 = 1534168340 from by norm_num]
      have h2 : (7 : ZMod 7670841701) ^ 1534168340 = ((3691377165 : ℕ) : ZMod 7670841701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7670841701 - 1) / 41 = 187093700 from by norm_num]
      have h2 : (7 : ZMod 7670841701) ^ 187093700 = ((3858439050 : ℕ) : ZMod 7670841701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7670841701 - 1) / 211 = 36354700 from by norm_num]
      have h2 : (7 : ZMod 7670841701) ^ 36354700 = ((3068231381 : ℕ) : ZMod 7670841701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7670841701 - 1) / 8867 = 865100 from by norm_num]
      have h2 : (7 : ZMod 7670841701) ^ 865100 = ((1760311144 : ℕ) : ZMod 7670841701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6797644660321 : Nat.Prime 6797644660321 := by
  refine lucas_primality 6797644660321 (26 : ZMod 6797644660321) ?_ (fun q hq hd => ?_)
  · rw [show 6797644660321 - 1 = 6797644660320 from by norm_num]
    reduce_mod_char
  · have e : 6797644660321 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 23 ^ 1, 109 ^ 1, 401 ^ 1, 14087 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 2 = 3398822330160 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 3398822330160 = ((6797644660320 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 3 = 2265881553440 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 2265881553440 = ((6185233538014 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 5 = 1359528932064 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 1359528932064 = ((5227790144755 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 23 = 295549767840 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 295549767840 = ((291431008102 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 109 = 62363712480 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 62363712480 = ((1380208515309 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 401 = 16951732320 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 16951732320 = ((4339791820434 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6797644660321 - 1) / 14087 = 482547360 from by norm_num]
      have h2 : (26 : ZMod 6797644660321) ^ 482547360 = ((4245614276082 : ℕ) : ZMod 6797644660321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_163897597 : Nat.Prime 163897597 := by
  refine lucas_primality 163897597 (2 : ZMod 163897597) ?_ (fun q hq hd => ?_)
  · rw [show 163897597 - 1 = 163897596 from by norm_num]
    reduce_mod_char
  · have e : 163897597 - 1 = [2 ^ 2, 3 ^ 2, 43 ^ 1, 239 ^ 1, 443 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (163897597 - 1) / 2 = 81948798 from by norm_num]
      have h2 : (2 : ZMod 163897597) ^ 81948798 = ((163897596 : ℕ) : ZMod 163897597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (163897597 - 1) / 3 = 54632532 from by norm_num]
      have h2 : (2 : ZMod 163897597) ^ 54632532 = ((143325401 : ℕ) : ZMod 163897597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (163897597 - 1) / 43 = 3811572 from by norm_num]
      have h2 : (2 : ZMod 163897597) ^ 3811572 = ((96610465 : ℕ) : ZMod 163897597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (163897597 - 1) / 239 = 685764 from by norm_num]
      have h2 : (2 : ZMod 163897597) ^ 685764 = ((66753720 : ℕ) : ZMod 163897597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (163897597 - 1) / 443 = 369972 from by norm_num]
      have h2 : (2 : ZMod 163897597) ^ 369972 = ((134845277 : ℕ) : ZMod 163897597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1835198027137 : Nat.Prime 1835198027137 := by
  refine lucas_primality 1835198027137 (11 : ZMod 1835198027137) ?_ (fun q hq hd => ?_)
  · rw [show 1835198027137 - 1 = 1835198027136 from by norm_num]
    reduce_mod_char
  · have e : 1835198027137 - 1 = [2 ^ 7, 3 ^ 2, 229 ^ 1, 6956567 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1835198027137 - 1) / 2 = 917599013568 from by norm_num]
      have h2 : (11 : ZMod 1835198027137) ^ 917599013568 = ((1835198027136 : ℕ) : ZMod 1835198027137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1835198027137 - 1) / 3 = 611732675712 from by norm_num]
      have h2 : (11 : ZMod 1835198027137) ^ 611732675712 = ((373106774015 : ℕ) : ZMod 1835198027137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1835198027137 - 1) / 229 = 8013965184 from by norm_num]
      have h2 : (11 : ZMod 1835198027137) ^ 8013965184 = ((264427099054 : ℕ) : ZMod 1835198027137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1835198027137 - 1) / 6956567 = 263808 from by norm_num]
      have h2 : (11 : ZMod 1835198027137) ^ 263808 = ((1356449216936 : ℕ) : ZMod 1835198027137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5675504055555452009 : Nat.Prime 5675504055555452009 := by
  refine lucas_primality 5675504055555452009 (6 : ZMod 5675504055555452009) ?_ (fun q hq hd => ?_)
  · rw [show 5675504055555452009 - 1 = 5675504055555452008 from by norm_num]
    reduce_mod_char
  · have e : 5675504055555452009 - 1 = [2 ^ 3, 11 ^ 1, 113 ^ 1, 311 ^ 1, 1835198027137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5675504055555452009 - 1) / 2 = 2837752027777726004 from by norm_num]
      have h2 : (6 : ZMod 5675504055555452009) ^ 2837752027777726004 = ((5675504055555452008 : ℕ) : ZMod 5675504055555452009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5675504055555452009 - 1) / 11 = 515954914141404728 from by norm_num]
      have h2 : (6 : ZMod 5675504055555452009) ^ 515954914141404728 = ((2071475814897337040 : ℕ) : ZMod 5675504055555452009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5675504055555452009 - 1) / 113 = 50225699606685416 from by norm_num]
      have h2 : (6 : ZMod 5675504055555452009) ^ 50225699606685416 = ((276789815126283200 : ℕ) : ZMod 5675504055555452009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5675504055555452009 - 1) / 311 = 18249209181850328 from by norm_num]
      have h2 : (6 : ZMod 5675504055555452009) ^ 18249209181850328 = ((3850948884242547608 : ℕ) : ZMod 5675504055555452009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1835198027137).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5675504055555452009 - 1) / 1835198027137 = 3092584 from by norm_num]
      have h2 : (6 : ZMod 5675504055555452009) ^ 3092584 = ((1757963994512879908 : ℕ) : ZMod 5675504055555452009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_35545368601 : Nat.Prime 35545368601 := by
  refine lucas_primality 35545368601 (13 : ZMod 35545368601) ?_ (fun q hq hd => ?_)
  · rw [show 35545368601 - 1 = 35545368600 from by norm_num]
    reduce_mod_char
  · have e : 35545368601 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 7 ^ 1, 457 ^ 1, 6173 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 2 = 17772684300 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 17772684300 = ((35545368600 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 3 = 11848456200 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 11848456200 = ((34908102673 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 5 = 7109073720 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 7109073720 = ((15593641023 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 7 = 5077909800 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 5077909800 = ((27076799666 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 457 = 77779800 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 77779800 = ((8419730341 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35545368601 - 1) / 6173 = 5758200 from by norm_num]
      have h2 : (13 : ZMod 35545368601) ^ 5758200 = ((14155670378 : ℕ) : ZMod 35545368601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17772684301 : Nat.Prime 17772684301 := by
  refine lucas_primality 17772684301 (10 : ZMod 17772684301) ?_ (fun q hq hd => ?_)
  · rw [show 17772684301 - 1 = 17772684300 from by norm_num]
    reduce_mod_char
  · have e : 17772684301 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 2, 7 ^ 1, 457 ^ 1, 6173 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 2 = 8886342150 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 8886342150 = ((17772684300 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 3 = 5924228100 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 5924228100 = ((10943478628 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 5 = 3554536860 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 3554536860 = ((9252955900 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 7 = 2538954900 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 2538954900 = ((10779866530 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 457 = 38889900 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 38889900 = ((17272481392 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17772684301 - 1) / 6173 = 2879100 from by norm_num]
      have h2 : (10 : ZMod 17772684301) ^ 2879100 = ((1347884576 : ℕ) : ZMod 17772684301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7693035769 : Nat.Prime 7693035769 := by
  refine lucas_primality 7693035769 (7 : ZMod 7693035769) ?_ (fun q hq hd => ?_)
  · rw [show 7693035769 - 1 = 7693035768 from by norm_num]
    reduce_mod_char
  · have e : 7693035769 - 1 = [2 ^ 3, 3 ^ 2, 11 ^ 2, 23 ^ 1, 38393 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7693035769 - 1) / 2 = 3846517884 from by norm_num]
      have h2 : (7 : ZMod 7693035769) ^ 3846517884 = ((7693035768 : ℕ) : ZMod 7693035769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7693035769 - 1) / 3 = 2564345256 from by norm_num]
      have h2 : (7 : ZMod 7693035769) ^ 2564345256 = ((2363326480 : ℕ) : ZMod 7693035769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7693035769 - 1) / 11 = 699366888 from by norm_num]
      have h2 : (7 : ZMod 7693035769) ^ 699366888 = ((1405346687 : ℕ) : ZMod 7693035769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7693035769 - 1) / 23 = 334479816 from by norm_num]
      have h2 : (7 : ZMod 7693035769) ^ 334479816 = ((2815471274 : ℕ) : ZMod 7693035769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7693035769 - 1) / 38393 = 200376 from by norm_num]
      have h2 : (7 : ZMod 7693035769) ^ 200376 = ((2417141474 : ℕ) : ZMod 7693035769) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_297905117118757 : Nat.Prime 297905117118757 := by
  refine lucas_primality 297905117118757 (13 : ZMod 297905117118757) ?_ (fun q hq hd => ?_)
  · rw [show 297905117118757 - 1 = 297905117118756 from by norm_num]
    reduce_mod_char
  · have e : 297905117118757 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 461 ^ 1, 7693035769 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297905117118757 - 1) / 2 = 148952558559378 from by norm_num]
      have h2 : (13 : ZMod 297905117118757) ^ 148952558559378 = ((297905117118756 : ℕ) : ZMod 297905117118757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297905117118757 - 1) / 3 = 99301705706252 from by norm_num]
      have h2 : (13 : ZMod 297905117118757) ^ 99301705706252 = ((150497216581623 : ℕ) : ZMod 297905117118757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297905117118757 - 1) / 7 = 42557873874108 from by norm_num]
      have h2 : (13 : ZMod 297905117118757) ^ 42557873874108 = ((164830448305874 : ℕ) : ZMod 297905117118757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297905117118757 - 1) / 461 = 646215004596 from by norm_num]
      have h2 : (13 : ZMod 297905117118757) ^ 646215004596 = ((42210807722918 : ℕ) : ZMod 297905117118757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7693035769).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (297905117118757 - 1) / 7693035769 = 38724 from by norm_num]
      have h2 : (13 : ZMod 297905117118757) ^ 38724 = ((158139355949830 : ℕ) : ZMod 297905117118757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3464012989753 : Nat.Prime 3464012989753 := by
  refine lucas_primality 3464012989753 (10 : ZMod 3464012989753) ?_ (fun q hq hd => ?_)
  · rw [show 3464012989753 - 1 = 3464012989752 from by norm_num]
    reduce_mod_char
  · have e : 3464012989753 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 2, 23 ^ 1, 37 ^ 1, 337 ^ 1, 10271 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 2 = 1732006494876 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 1732006494876 = ((3464012989752 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 3 = 1154670996584 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 1154670996584 = ((2770915794115 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 7 = 494858998536 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 494858998536 = ((3011421764279 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 23 = 150609260424 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 150609260424 = ((2262716267083 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 37 = 93621972696 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 93621972696 = ((2633582846249 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 337 = 10278970296 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 10278970296 = ((1952760326216 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3464012989753 - 1) / 10271 = 337261512 from by norm_num]
      have h2 : (10 : ZMod 3464012989753) ^ 337261512 = ((2985898101731 : ℕ) : ZMod 3464012989753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1732006494877 : Nat.Prime 1732006494877 := by
  refine lucas_primality 1732006494877 (2 : ZMod 1732006494877) ?_ (fun q hq hd => ?_)
  · rw [show 1732006494877 - 1 = 1732006494876 from by norm_num]
    reduce_mod_char
  · have e : 1732006494877 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 2, 23 ^ 1, 37 ^ 1, 337 ^ 1, 10271 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 2 = 866003247438 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 866003247438 = ((1732006494876 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 3 = 577335498292 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 577335498292 = ((363288101419 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 7 = 247429499268 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 247429499268 = ((283646696157 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 23 = 75304630212 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 75304630212 = ((3249215346 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 37 = 46810986348 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 46810986348 = ((56807914221 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 337 = 5139485148 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 5139485148 = ((1485834180809 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1732006494877 - 1) / 10271 = 168630756 from by norm_num]
      have h2 : (2 : ZMod 1732006494877) ^ 168630756 = ((603917009869 : ℕ) : ZMod 1732006494877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33591968029 : Nat.Prime 33591968029 := by
  refine lucas_primality 33591968029 (6 : ZMod 33591968029) ?_ (fun q hq hd => ?_)
  · rw [show 33591968029 - 1 = 33591968028 from by norm_num]
    reduce_mod_char
  · have e : 33591968029 - 1 = [2 ^ 2, 3 ^ 3, 47 ^ 1, 6617803 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33591968029 - 1) / 2 = 16795984014 from by norm_num]
      have h2 : (6 : ZMod 33591968029) ^ 16795984014 = ((33591968028 : ℕ) : ZMod 33591968029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33591968029 - 1) / 3 = 11197322676 from by norm_num]
      have h2 : (6 : ZMod 33591968029) ^ 11197322676 = ((30432054681 : ℕ) : ZMod 33591968029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33591968029 - 1) / 47 = 714722724 from by norm_num]
      have h2 : (6 : ZMod 33591968029) ^ 714722724 = ((13890113135 : ℕ) : ZMod 33591968029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33591968029 - 1) / 6617803 = 5076 from by norm_num]
      have h2 : (6 : ZMod 33591968029) ^ 5076 = ((611754643 : ℕ) : ZMod 33591968029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_614908920077491091197 : Nat.Prime 614908920077491091197 := by
  refine lucas_primality 614908920077491091197 (2 : ZMod 614908920077491091197) ?_ (fun q hq hd => ?_)
  · rw [show 614908920077491091197 - 1 = 614908920077491091196 from by norm_num]
    reduce_mod_char
  · have e : 614908920077491091197 - 1 = [2 ^ 2, 3 ^ 1, 463 ^ 1, 3294679 ^ 1, 33591968029 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (614908920077491091197 - 1) / 2 = 307454460038745545598 from by norm_num]
      have h2 : (2 : ZMod 614908920077491091197) ^ 307454460038745545598 = ((614908920077491091196 : ℕ) : ZMod 614908920077491091197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (614908920077491091197 - 1) / 3 = 204969640025830363732 from by norm_num]
      have h2 : (2 : ZMod 614908920077491091197) ^ 204969640025830363732 = ((262838514393128856726 : ℕ) : ZMod 614908920077491091197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (614908920077491091197 - 1) / 463 = 1328097019605812292 from by norm_num]
      have h2 : (2 : ZMod 614908920077491091197) ^ 1328097019605812292 = ((558686733887463509890 : ℕ) : ZMod 614908920077491091197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (614908920077491091197 - 1) / 3294679 = 186636974369124 from by norm_num]
      have h2 : (2 : ZMod 614908920077491091197) ^ 186636974369124 = ((414519060298453432409 : ℕ) : ZMod 614908920077491091197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_33591968029).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (614908920077491091197 - 1) / 33591968029 = 18305236524 from by norm_num]
      have h2 : (2 : ZMod 614908920077491091197) ^ 18305236524 = ((530277538543129072099 : ℕ) : ZMod 614908920077491091197) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1169028365166332873 : Nat.Prime 1169028365166332873 := by
  refine lucas_primality 1169028365166332873 (3 : ZMod 1169028365166332873) ?_ (fun q hq hd => ?_)
  · rw [show 1169028365166332873 - 1 = 1169028365166332872 from by norm_num]
    reduce_mod_char
  · have e : 1169028365166332873 - 1 = [2 ^ 3, 19 ^ 1, 43 ^ 1, 613 ^ 1, 2917 ^ 1, 6917 ^ 1, 14461 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 2 = 584514182583166436 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 584514182583166436 = ((1169028365166332872 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 19 = 61527808692964888 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 61527808692964888 = ((822704854020736154 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 43 = 27186706166658904 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 27186706166658904 = ((743423719673645774 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 613 = 1907060954594344 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 1907060954594344 = ((780662058113285336 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 2917 = 400763923608616 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 400763923608616 = ((966476735777419383 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 6917 = 169008004216616 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 169008004216616 = ((147354000530070721 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1169028365166332873 - 1) / 14461 = 80840077806952 from by norm_num]
      have h2 : (3 : ZMod 1169028365166332873) ^ 80840077806952 = ((484537979476553170 : ℕ) : ZMod 1169028365166332873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3733008450772109 : Nat.Prime 3733008450772109 := by
  refine lucas_primality 3733008450772109 (2 : ZMod 3733008450772109) ?_ (fun q hq hd => ?_)
  · rw [show 3733008450772109 - 1 = 3733008450772108 from by norm_num]
    reduce_mod_char
  · have e : 3733008450772109 - 1 = [2 ^ 2, 43 ^ 1, 233 ^ 1, 23509 ^ 1, 3962237 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3733008450772109 - 1) / 2 = 1866504225386054 from by norm_num]
      have h2 : (2 : ZMod 3733008450772109) ^ 1866504225386054 = ((3733008450772108 : ℕ) : ZMod 3733008450772109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3733008450772109 - 1) / 43 = 86814150017956 from by norm_num]
      have h2 : (2 : ZMod 3733008450772109) ^ 86814150017956 = ((2021277950301565 : ℕ) : ZMod 3733008450772109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3733008450772109 - 1) / 233 = 16021495496876 from by norm_num]
      have h2 : (2 : ZMod 3733008450772109) ^ 16021495496876 = ((2389242738914779 : ℕ) : ZMod 3733008450772109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3733008450772109 - 1) / 23509 = 158790610012 from by norm_num]
      have h2 : (2 : ZMod 3733008450772109) ^ 158790610012 = ((100965970660776 : ℕ) : ZMod 3733008450772109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3733008450772109 - 1) / 3962237 = 942146684 from by norm_num]
      have h2 : (2 : ZMod 3733008450772109) ^ 942146684 = ((2836061632545377 : ℕ) : ZMod 3733008450772109) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_687003857 : Nat.Prime 687003857 := by
  refine lucas_primality 687003857 (3 : ZMod 687003857) ?_ (fun q hq hd => ?_)
  · rw [show 687003857 - 1 = 687003856 from by norm_num]
    reduce_mod_char
  · have e : 687003857 - 1 = [2 ^ 4, 7 ^ 1, 11 ^ 1, 557633 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (687003857 - 1) / 2 = 343501928 from by norm_num]
      have h2 : (3 : ZMod 687003857) ^ 343501928 = ((687003856 : ℕ) : ZMod 687003857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (687003857 - 1) / 7 = 98143408 from by norm_num]
      have h2 : (3 : ZMod 687003857) ^ 98143408 = ((619514483 : ℕ) : ZMod 687003857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (687003857 - 1) / 11 = 62454896 from by norm_num]
      have h2 : (3 : ZMod 687003857) ^ 62454896 = ((267983239 : ℕ) : ZMod 687003857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (687003857 - 1) / 557633 = 1232 from by norm_num]
      have h2 : (3 : ZMod 687003857) ^ 1232 = ((409355978 : ℕ) : ZMod 687003857) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1163784533759 : Nat.Prime 1163784533759 := by
  refine lucas_primality 1163784533759 (7 : ZMod 1163784533759) ?_ (fun q hq hd => ?_)
  · rw [show 1163784533759 - 1 = 1163784533758 from by norm_num]
    reduce_mod_char
  · have e : 1163784533759 - 1 = [2 ^ 1, 7 ^ 1, 11 ^ 2, 687003857 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1163784533759 - 1) / 2 = 581892266879 from by norm_num]
      have h2 : (7 : ZMod 1163784533759) ^ 581892266879 = ((1163784533758 : ℕ) : ZMod 1163784533759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1163784533759 - 1) / 7 = 166254933394 from by norm_num]
      have h2 : (7 : ZMod 1163784533759) ^ 166254933394 = ((207964033508 : ℕ) : ZMod 1163784533759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1163784533759 - 1) / 11 = 105798593978 from by norm_num]
      have h2 : (7 : ZMod 1163784533759) ^ 105798593978 = ((542620093308 : ℕ) : ZMod 1163784533759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_687003857).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1163784533759 - 1) / 687003857 = 1694 from by norm_num]
      have h2 : (7 : ZMod 1163784533759) ^ 1694 = ((762664215650 : ℕ) : ZMod 1163784533759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_376719381146855819 : Nat.Prime 376719381146855819 := by
  refine lucas_primality 376719381146855819 (2 : ZMod 376719381146855819) ?_ (fun q hq hd => ?_)
  · rw [show 376719381146855819 - 1 = 376719381146855818 from by norm_num]
    reduce_mod_char
  · have e : 376719381146855819 - 1 = [2 ^ 1, 23 ^ 1, 31 ^ 1, 227 ^ 1, 1163784533759 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (376719381146855819 - 1) / 2 = 188359690573427909 from by norm_num]
      have h2 : (2 : ZMod 376719381146855819) ^ 188359690573427909 = ((376719381146855818 : ℕ) : ZMod 376719381146855819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (376719381146855819 - 1) / 23 = 16379103528124166 from by norm_num]
      have h2 : (2 : ZMod 376719381146855819) ^ 16379103528124166 = ((39048339829018031 : ℕ) : ZMod 376719381146855819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (376719381146855819 - 1) / 31 = 12152238101511478 from by norm_num]
      have h2 : (2 : ZMod 376719381146855819) ^ 12152238101511478 = ((208806348165992728 : ℕ) : ZMod 376719381146855819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (376719381146855819 - 1) / 227 = 1659556745140334 from by norm_num]
      have h2 : (2 : ZMod 376719381146855819) ^ 1659556745140334 = ((228376960585723656 : ℕ) : ZMod 376719381146855819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1163784533759).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (376719381146855819 - 1) / 1163784533759 = 323702 from by norm_num]
      have h2 : (2 : ZMod 376719381146855819) ^ 323702 = ((1607622650379977 : ℕ) : ZMod 376719381146855819) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4092318459612302929741399 : Nat.Prime 4092318459612302929741399 := by
  refine lucas_primality 4092318459612302929741399 (3 : ZMod 4092318459612302929741399) ?_ (fun q hq hd => ?_)
  · rw [show 4092318459612302929741399 - 1 = 4092318459612302929741398 from by norm_num]
    reduce_mod_char
  · have e : 4092318459612302929741399 - 1 = [2 ^ 1, 3 ^ 1, 1810507 ^ 1, 376719381146855819 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4092318459612302929741399 - 1) / 2 = 2046159229806151464870699 from by norm_num]
      have h2 : (3 : ZMod 4092318459612302929741399) ^ 2046159229806151464870699 = ((4092318459612302929741398 : ℕ) : ZMod 4092318459612302929741399) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4092318459612302929741399 - 1) / 3 = 1364106153204100976580466 from by norm_num]
      have h2 : (3 : ZMod 4092318459612302929741399) ^ 1364106153204100976580466 = ((295717957130816858455063 : ℕ) : ZMod 4092318459612302929741399) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4092318459612302929741399 - 1) / 1810507 = 2260316286881134914 from by norm_num]
      have h2 : (3 : ZMod 4092318459612302929741399) ^ 2260316286881134914 = ((3832489577237827074253630 : ℕ) : ZMod 4092318459612302929741399) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_376719381146855819).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4092318459612302929741399 - 1) / 376719381146855819 = 10863042 from by norm_num]
      have h2 : (3 : ZMod 4092318459612302929741399) ^ 10863042 = ((208847410090009860637368 : ℕ) : ZMod 4092318459612302929741399) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_40309625771 : Nat.Prime 40309625771 := by
  refine lucas_primality 40309625771 (2 : ZMod 40309625771) ?_ (fun q hq hd => ?_)
  · rw [show 40309625771 - 1 = 40309625770 from by norm_num]
    reduce_mod_char
  · have e : 40309625771 - 1 = [2 ^ 1, 5 ^ 1, 103 ^ 1, 39135559 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40309625771 - 1) / 2 = 20154812885 from by norm_num]
      have h2 : (2 : ZMod 40309625771) ^ 20154812885 = ((40309625770 : ℕ) : ZMod 40309625771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40309625771 - 1) / 5 = 8061925154 from by norm_num]
      have h2 : (2 : ZMod 40309625771) ^ 8061925154 = ((34211609068 : ℕ) : ZMod 40309625771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40309625771 - 1) / 103 = 391355590 from by norm_num]
      have h2 : (2 : ZMod 40309625771) ^ 391355590 = ((21156508635 : ℕ) : ZMod 40309625771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40309625771 - 1) / 39135559 = 1030 from by norm_num]
      have h2 : (2 : ZMod 40309625771) ^ 1030 = ((7575938262 : ℕ) : ZMod 40309625771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7133145601932671820738044077873700651040107 : Nat.Prime 7133145601932671820738044077873700651040107 := by
  refine lucas_primality 7133145601932671820738044077873700651040107 (2 : ZMod 7133145601932671820738044077873700651040107) ?_ (fun q hq hd => ?_)
  · rw [show 7133145601932671820738044077873700651040107 - 1 = 7133145601932671820738044077873700651040106 from by norm_num]
    reduce_mod_char
  · have e : 7133145601932671820738044077873700651040107 - 1 = [2 ^ 1, 31 ^ 1, 697447 ^ 1, 40309625771 ^ 1, 4092318459612302929741399 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7133145601932671820738044077873700651040107 - 1) / 2 = 3566572800966335910369022038936850325520053 from by norm_num]
      have h2 : (2 : ZMod 7133145601932671820738044077873700651040107) ^ 3566572800966335910369022038936850325520053 = ((7133145601932671820738044077873700651040106 : ℕ) : ZMod 7133145601932671820738044077873700651040107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7133145601932671820738044077873700651040107 - 1) / 31 = 230101471030086187765743357350764537130326 from by norm_num]
      have h2 : (2 : ZMod 7133145601932671820738044077873700651040107) ^ 230101471030086187765743357350764537130326 = ((1187672990836078723722468420216305517250478 : ℕ) : ZMod 7133145601932671820738044077873700651040107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7133145601932671820738044077873700651040107 - 1) / 697447 = 10227509189849080748412487368751604998 from by norm_num]
      have h2 : (2 : ZMod 7133145601932671820738044077873700651040107) ^ 10227509189849080748412487368751604998 = ((2143775001022717836368272013853268253856418 : ℕ) : ZMod 7133145601932671820738044077873700651040107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_40309625771).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7133145601932671820738044077873700651040107 - 1) / 40309625771 = 176958864427475754169239669517886 from by norm_num]
      have h2 : (2 : ZMod 7133145601932671820738044077873700651040107) ^ 176958864427475754169239669517886 = ((1223350220891785410895625469161306802467104 : ℕ) : ZMod 7133145601932671820738044077873700651040107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4092318459612302929741399).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7133145601932671820738044077873700651040107 - 1) / 4092318459612302929741399 = 1743057309036611494 from by norm_num]
      have h2 : (2 : ZMod 7133145601932671820738044077873700651040107) ^ 1743057309036611494 = ((4004693184191905745956319006717435257224502 : ℕ) : ZMod 7133145601932671820738044077873700651040107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_159693683 : Nat.Prime 159693683 := by
  refine lucas_primality 159693683 (2 : ZMod 159693683) ?_ (fun q hq hd => ?_)
  · rw [show 159693683 - 1 = 159693682 from by norm_num]
    reduce_mod_char
  · have e : 159693683 - 1 = [2 ^ 1, 17 ^ 1, 4696873 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159693683 - 1) / 2 = 79846841 from by norm_num]
      have h2 : (2 : ZMod 159693683) ^ 79846841 = ((159693682 : ℕ) : ZMod 159693683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159693683 - 1) / 17 = 9393746 from by norm_num]
      have h2 : (2 : ZMod 159693683) ^ 9393746 = ((7385247 : ℕ) : ZMod 159693683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159693683 - 1) / 4696873 = 34 from by norm_num]
      have h2 : (2 : ZMod 159693683) ^ 34 = ((92645103 : ℕ) : ZMod 159693683) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23685128287829 : Nat.Prime 23685128287829 := by
  refine lucas_primality 23685128287829 (2 : ZMod 23685128287829) ?_ (fun q hq hd => ?_)
  · rw [show 23685128287829 - 1 = 23685128287828 from by norm_num]
    reduce_mod_char
  · have e : 23685128287829 - 1 = [2 ^ 2, 7 ^ 1, 5297 ^ 1, 159693683 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23685128287829 - 1) / 2 = 11842564143914 from by norm_num]
      have h2 : (2 : ZMod 23685128287829) ^ 11842564143914 = ((23685128287828 : ℕ) : ZMod 23685128287829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23685128287829 - 1) / 7 = 3383589755404 from by norm_num]
      have h2 : (2 : ZMod 23685128287829) ^ 3383589755404 = ((458863966107 : ℕ) : ZMod 23685128287829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23685128287829 - 1) / 5297 = 4471423124 from by norm_num]
      have h2 : (2 : ZMod 23685128287829) ^ 4471423124 = ((16636590457322 : ℕ) : ZMod 23685128287829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_159693683).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23685128287829 - 1) / 159693683 = 148316 from by norm_num]
      have h2 : (2 : ZMod 23685128287829) ^ 148316 = ((4058694867173 : ℕ) : ZMod 23685128287829) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_502516291 : Nat.Prime 502516291 := by
  refine lucas_primality 502516291 (3 : ZMod 502516291) ?_ (fun q hq hd => ?_)
  · rw [show 502516291 - 1 = 502516290 from by norm_num]
    reduce_mod_char
  · have e : 502516291 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 719 ^ 1, 23297 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502516291 - 1) / 2 = 251258145 from by norm_num]
      have h2 : (3 : ZMod 502516291) ^ 251258145 = ((502516290 : ℕ) : ZMod 502516291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502516291 - 1) / 3 = 167505430 from by norm_num]
      have h2 : (3 : ZMod 502516291) ^ 167505430 = ((73211609 : ℕ) : ZMod 502516291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502516291 - 1) / 5 = 100503258 from by norm_num]
      have h2 : (3 : ZMod 502516291) ^ 100503258 = ((133899219 : ℕ) : ZMod 502516291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502516291 - 1) / 719 = 698910 from by norm_num]
      have h2 : (3 : ZMod 502516291) ^ 698910 = ((283540063 : ℕ) : ZMod 502516291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (502516291 - 1) / 23297 = 21570 from by norm_num]
      have h2 : (3 : ZMod 502516291) ^ 21570 = ((125740432 : ℕ) : ZMod 502516291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_51857843 : Nat.Prime 51857843 := by
  refine lucas_primality 51857843 (2 : ZMod 51857843) ?_ (fun q hq hd => ?_)
  · rw [show 51857843 - 1 = 51857842 from by norm_num]
    reduce_mod_char
  · have e : 51857843 - 1 = [2 ^ 1, 139 ^ 1, 167 ^ 1, 1117 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51857843 - 1) / 2 = 25928921 from by norm_num]
      have h2 : (2 : ZMod 51857843) ^ 25928921 = ((51857842 : ℕ) : ZMod 51857843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51857843 - 1) / 139 = 373078 from by norm_num]
      have h2 : (2 : ZMod 51857843) ^ 373078 = ((21642613 : ℕ) : ZMod 51857843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51857843 - 1) / 167 = 310526 from by norm_num]
      have h2 : (2 : ZMod 51857843) ^ 310526 = ((23591216 : ℕ) : ZMod 51857843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (51857843 - 1) / 1117 = 46426 from by norm_num]
      have h2 : (2 : ZMod 51857843) ^ 46426 = ((30737418 : ℕ) : ZMod 51857843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7616711879199861861797533405726892034258383527977116552855858482952014397471 : Nat.Prime 7616711879199861861797533405726892034258383527977116552855858482952014397471 := by
  refine lucas_primality 7616711879199861861797533405726892034258383527977116552855858482952014397471 (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ?_ (fun q hq hd => ?_)
  · rw [show 7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1 = 7616711879199861861797533405726892034258383527977116552855858482952014397470 from by norm_num]
    reduce_mod_char
  · have e : 7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1 = [2 ^ 1, 5 ^ 1, 173 ^ 1, 51857843 ^ 1, 502516291 ^ 1, 23685128287829 ^ 1, 7133145601932671820738044077873700651040107 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 2 = 3808355939599930930898766702863446017129191763988558276427929241476007198735 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 3808355939599930930898766702863446017129191763988558276427929241476007198735 = ((7616711879199861861797533405726892034258383527977116552855858482952014397470 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 5 = 1523342375839972372359506681145378406851676705595423310571171696590402879494 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 1523342375839972372359506681145378406851676705595423310571171696590402879494 = ((3558376515673836711881760486340682431019103173254092221039942238836490225378 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 173 = 44027236295952958738714065929057179388776783398711656374889355392786210390 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 44027236295952958738714065929057179388776783398711656374889355392786210390 = ((4024434433799895416304753564489049549959599126977766606127764967595950426482 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_51857843).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 51857843 = 146876758433625206158257168654833793111263488687277574442420570461290 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 146876758433625206158257168654833793111263488687277574442420570461290 = ((5376420341047499476643868040851579209313907530205034743150654263351951142380 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_502516291).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 502516291 = 15157144187390855875352175210826930254204203556809895647454459308170 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 15157144187390855875352175210826930254204203556809895647454459308170 = ((2186590774919175187586772820270407508420780528696757449827823423522990727205 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_23685128287829).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 23685128287829 = 321582040284486737363378415230141300354468981052188707005739430 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 321582040284486737363378415230141300354468981052188707005739430 = ((3275946335092244475236461790115125286511038645568120179080193069020624667857 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7133145601932671820738044077873700651040107).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7616711879199861861797533405726892034258383527977116552855858482952014397471 - 1) / 7133145601932671820738044077873700651040107 = 1067791449137975175723810871925210 from by norm_num]
      have h2 : (7 : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) ^ 1067791449137975175723810871925210 = ((5701635296335287792171452519335347799367499976971041424527625128153844926967 : ℕ) : ZMod 7616711879199861861797533405726892034258383527977116552855858482952014397471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 : Nat.Prime 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 := by
  refine lucas_primality 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ?_ (fun q hq hd => ?_)
  · rw [show 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1 = 60892643104482757573306223567662688740985969197465290654173842691745096014633691396822 from by norm_num]
    reduce_mod_char
  · have e : 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1 = [2 ^ 1, 3 ^ 1, 491 ^ 1, 2713717 ^ 1, 7616711879199861861797533405726892034258383527977116552855858482952014397471 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1) / 2 = 30446321552241378786653111783831344370492984598732645327086921345872548007316845698411 from by norm_num]
      have h2 : (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ^ 30446321552241378786653111783831344370492984598732645327086921345872548007316845698411 = ((60892643104482757573306223567662688740985969197465290654173842691745096014633691396822 : ℕ) : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1) / 3 = 20297547701494252524435407855887562913661989732488430218057947563915032004877897132274 from by norm_num]
      have h2 : (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ^ 20297547701494252524435407855887562913661989732488430218057947563915032004877897132274 = ((56406808132634530460604902403909201712857789803648390943253115246854342487050651623210 : ℕ) : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1) / 491 = 124017603064119669192069701767133785623189346634348860802798050288686549927970858242 from by norm_num]
      have h2 : (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ^ 124017603064119669192069701767133785623189346634348860802798050288686549927970858242 = ((35624821756713166379767440900425579920348678468238226518374742589911382958756793848072 : ℕ) : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1) / 2713717 = 22438833196122793044855533413271423932925197873420585364713359090776634414949566 from by norm_num]
      have h2 : (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ^ 22438833196122793044855533413271423932925197873420585364713359090776634414949566 = ((51570383134432328971109925467548096768429456258837778958509248203471858057691908644745 : ℕ) : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7616711879199861861797533405726892034258383527977116552855858482952014397471).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 - 1) / 7616711879199861861797533405726892034258383527977116552855858482952014397471 = 7994610282 from by norm_num]
      have h2 : (5 : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) ^ 7994610282 = ((13468514448337710170830490415539365984783937077106994117446896967578182368621777188444 : ℕ) : ZMod 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- 3^202 + 1: 5 divides 3^202 + 1 and 29 + 1 (chain 1189912513 -> 29).
theorem kill3_e202 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 202 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1189912513 : 1189912513 ∈ P := S7 1189912513 prime_1189912513 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1189912513 ∣ 1 + 3 ^ 202).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1189912513 g1189912513 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 202).trans hd) 29 g29 (by norm_num)

-- 3^206 + 1: 5 divides 3^206 + 1 and 19 + 1 (chain 1522395676033 -> 37 -> 19).
theorem kill3_e206 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 206 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1522395676033 : 1522395676033 ∈ P := S7 1522395676033 prime_1522395676033 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1522395676033 ∣ 1 + 3 ^ 206).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1522395676033 g1522395676033 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 206).trans hd) 19 g19 (by norm_num)

-- 3^209 + 1: 5 divides 8779 + 1 and 439 + 1 (chains 8779; 8779 -> 439).
theorem kill3_e209 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 209 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8779 : 8779 ∈ P := S7 8779 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8779 ∣ 1 + 3 ^ 209).trans hd)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 8779 g8779 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8779 g8779 439 g439 (by norm_num) (by norm_num)
  omega

-- 3^211 + 1: 5 divides 37189 + 1 and 3719 + 1 (chains 892531 -> 223133 -> 37189; 892531 -> 223133 -> 37189 -> 3719).
theorem kill3_e211 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 211 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g892531 : 892531 ∈ P := S7 892531 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 892531 ∣ 1 + 3 ^ 211).trans hd)
  have g223133 : 223133 ∈ P := S1 223133 (by norm_num) (by norm_num) (hnz (by norm_num)) 892531 g892531 (by norm_num)
  have g37189 : 37189 ∈ P := S1 37189 (by norm_num) (by norm_num) (hnz (by norm_num)) 223133 g223133 (by norm_num)
  have g3719 : 3719 ∈ P := S1 3719 (by norm_num) (by norm_num) (hnz (by norm_num)) 37189 g37189 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 37189 g37189 3719 g3719 (by norm_num) (by norm_num)
  omega

-- 3^212 + 1: 5^2 divides 1079398849 + 1 (chain 1079398849).
theorem kill3_e212 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 212 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1079398849 : 1079398849 ∈ P := S7 1079398849 prime_1079398849 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1079398849 ∣ 1 + 3 ^ 212).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1079398849 g1079398849 (by norm_num)

-- 3^214 + 1: 5 divides 3^214 + 1 and 7109 + 1 (chain 582937 -> 7109).
theorem kill3_e214 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 214 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g582937 : 582937 ∈ P := S7 582937 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 582937 ∣ 1 + 3 ^ 214).trans hd)
  have g7109 : 7109 ∈ P := S1 7109 (by norm_num) (by norm_num) (hnz (by norm_num)) 582937 g582937 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 214).trans hd) 7109 g7109 (by norm_num)

-- 3^218 + 1: 2617 divides 3^218 + 1 and 5233 + 1 (chain 5233).
theorem kill3_e218 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 218 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5233 : 5233 ∈ P := S7 5233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5233 ∣ 1 + 3 ^ 218).trans hd)
  exact S8 2617 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 2617 ∣ 1 + 3 ^ 218).trans hd) 5233 g5233 (by norm_num)

-- 3^223 + 1: 5 divides 95429 + 1 and 19 + 1 (chains 19849231 -> 95429; 19849231 -> 95429 -> 3181 -> 37 -> 19).
theorem kill3_e223 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 223 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19849231 : 19849231 ∈ P := S7 19849231 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19849231 ∣ 1 + 3 ^ 223).trans hd)
  have g95429 : 95429 ∈ P := S1 95429 (by norm_num) (by norm_num) (hnz (by norm_num)) 19849231 g19849231 (by norm_num)
  have g3181 : 3181 ∈ P := S1 3181 (by norm_num) (by norm_num) (hnz (by norm_num)) 95429 g95429 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 3181 g3181 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 95429 g95429 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^226 + 1: 5 divides 3^226 + 1 and 59 + 1 (chain 2713 -> 59).
theorem kill3_e226 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 226 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2713 : 2713 ∈ P := S7 2713 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2713 ∣ 1 + 3 ^ 226).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 2713 g2713 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 226).trans hd) 59 g59 (by norm_num)

-- 3^227 + 1: 5^2 divides 149 + 1 (chain 28603 -> 7151 -> 149).
theorem kill3_e227 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 227 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g28603 : 28603 ∈ P := S7 28603 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28603 ∣ 1 + 3 ^ 227).trans hd)
  have g7151 : 7151 ∈ P := S1 7151 (by norm_num) (by norm_num) (hnz (by norm_num)) 28603 g28603 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 7151 g7151 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- 3^229 + 1: 11 divides 169003 + 1 and 704747 + 1 (chains 169003; 4032176417327894814764968543 -> 704747).
theorem kill3_e229 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 229 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g169003 : 169003 ∈ P := S7 169003 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 169003 ∣ 1 + 3 ^ 229).trans hd)
  have g4032176417327894814764968543 : 4032176417327894814764968543 ∈ P := S7 4032176417327894814764968543 prime_4032176417327894814764968543 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4032176417327894814764968543 ∣ 1 + 3 ^ 229).trans hd)
  have g704747 : 704747 ∈ P := S1 704747 (by norm_num) (by norm_num) (hnz (by norm_num)) 4032176417327894814764968543 g4032176417327894814764968543 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 169003 g169003 704747 g704747 (by norm_num) (by norm_num)
  omega

-- 3^233 + 1: 5^2 divides 1399 + 1 (chain 1399).
theorem kill3_e233 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 233 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1399 : 1399 ∈ P := S7 1399 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1399 ∣ 1 + 3 ^ 233).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1399 g1399 (by norm_num)

-- 3^236 + 1: 7 divides 41 + 1 and 87793 + 1 (chains 41; 87793).
theorem kill3_e236 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 236 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 236).trans hd)
  have g87793 : 87793 ∈ P := S7 87793 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 87793 ∣ 1 + 3 ^ 236).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 87793 g87793 (by norm_num) (by norm_num)
  omega

-- 3^239 + 1: 7^2 divides 42124768369936320790693 + 1 (chain 42124768369936320790693).
theorem kill3_e239 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 239 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g42124768369936320790693 : 42124768369936320790693 ∈ P := S7 42124768369936320790693 prime_42124768369936320790693 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 42124768369936320790693 ∣ 1 + 3 ^ 239).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 42124768369936320790693 g42124768369936320790693 (by norm_num)

-- 3^241 + 1: 5^2 divides 449 + 1 (chain 281971 -> 449).
theorem kill3_e241 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 241 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g281971 : 281971 ∈ P := S7 281971 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 281971 ∣ 1 + 3 ^ 241).trans hd)
  have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 281971 g281971 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)

-- 3^244 + 1: 11 divides 2441 + 1 and 123450337 + 1 (chains 2441; 123450337).
theorem kill3_e244 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 244 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2441 : 2441 ∈ P := S7 2441 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2441 ∣ 1 + 3 ^ 244).trans hd)
  have g123450337 : 123450337 ∈ P := S7 123450337 prime_123450337 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 123450337 ∣ 1 + 3 ^ 244).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 2441 g2441 123450337 g123450337 (by norm_num) (by norm_num)
  omega

-- 3^247 + 1: 5 divides 139 + 1 and 389 + 1 (chains 8893 -> 4447 -> 139; 101917 -> 389).
theorem kill3_e247 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 247 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8893 : 8893 ∈ P := S7 8893 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8893 ∣ 1 + 3 ^ 247).trans hd)
  have g4447 : 4447 ∈ P := S1 4447 (by norm_num) (by norm_num) (hnz (by norm_num)) 8893 g8893 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 4447 g4447 (by norm_num)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 101917 ∣ 1 + 3 ^ 247).trans hd)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 139 g139 389 g389 (by norm_num) (by norm_num)
  omega

-- 3^251 + 1: 31 divides 158843 + 1 and 61 + 1 (chains 6936751667531821 -> 158843; 6936751667531821 -> 158843 -> 61).
theorem kill3_e251 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 251 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6936751667531821 : 6936751667531821 ∈ P := S7 6936751667531821 prime_6936751667531821 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6936751667531821 ∣ 1 + 3 ^ 251).trans hd)
  have g158843 : 158843 ∈ P := S1 158843 (by norm_num) (by norm_num) (hnz (by norm_num)) 6936751667531821 g6936751667531821 (by norm_num)
  have g61 : 61 ∈ P := S1 61 (by norm_num) (by norm_num) (hnz (by norm_num)) 158843 g158843 (by norm_num)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 158843 g158843 61 g61 (by norm_num) (by norm_num)
  omega

-- 3^254 + 1: 5 divides 3^254 + 1 and 509 + 1 (chain 509).
theorem kill3_e254 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 254 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g509 : 509 ∈ P := S7 509 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 509 ∣ 1 + 3 ^ 254).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 254).trans hd) 509 g509 (by norm_num)

-- 3^256 + 1: 5 divides 12289 + 1 and 1229 + 1 (chains 12289; 12289 -> 1229).
theorem kill3_e256 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 256 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12289 : 12289 ∈ P := S7 12289 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 12289 ∣ 1 + 3 ^ 256).trans hd)
  have g1229 : 1229 ∈ P := S1 1229 (by norm_num) (by norm_num) (hnz (by norm_num)) 12289 g12289 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12289 g12289 1229 g1229 (by norm_num) (by norm_num)
  omega

-- 3^257 + 1: 7^2 divides 97 + 1 (chain 1543 -> 193 -> 97).
theorem kill3_e257 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 257 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1543 : 1543 ∈ P := S7 1543 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 257 = 3 ^ 200 * 3 ^ 57 from pow_add 3 200 57]; norm_num : 1543 ∣ 1 + 3 ^ 257).trans hd)
  have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 1543 g1543 (by norm_num)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

-- 3^262 + 1: 5 divides 3^262 + 1 and 19 + 1 (chain 2621 -> 19).
theorem kill3_e262 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 262 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2621 : 2621 ∈ P := S7 2621 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 262 = 3 ^ 200 * 3 ^ 62 from pow_add 3 200 62]; norm_num : 2621 ∣ 1 + 3 ^ 262).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2621 g2621 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 262 = 3 ^ 200 * 3 ^ 62 from pow_add 3 200 62]; norm_num : 5 ∣ 1 + 3 ^ 262).trans hd) 19 g19 (by norm_num)

-- 3^263 + 1: 7 divides 127819 + 1 and 83 + 1 (chains 255637 -> 127819; 255637 -> 127819 -> 83).
theorem kill3_e263 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 263 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g255637 : 255637 ∈ P := S7 255637 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 263 = 3 ^ 200 * 3 ^ 63 from pow_add 3 200 63]; norm_num : 255637 ∣ 1 + 3 ^ 263).trans hd)
  have g127819 : 127819 ∈ P := S1 127819 (by norm_num) (by norm_num) (hnz (by norm_num)) 255637 g255637 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 127819 g127819 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 127819 g127819 83 g83 (by norm_num) (by norm_num)
  omega

-- 3^268 + 1: 7 divides 41 + 1 and 1609 + 1 (chains 41; 3217 -> 1609).
theorem kill3_e268 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 268 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 268 = 3 ^ 200 * 3 ^ 68 from pow_add 3 200 68]; norm_num : 41 ∣ 1 + 3 ^ 268).trans hd)
  have g3217 : 3217 ∈ P := S7 3217 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 268 = 3 ^ 200 * 3 ^ 68 from pow_add 3 200 68]; norm_num : 3217 ∣ 1 + 3 ^ 268).trans hd)
  have g1609 : 1609 ∈ P := S1 1609 (by norm_num) (by norm_num) (hnz (by norm_num)) 3217 g3217 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 1609 g1609 (by norm_num) (by norm_num)
  omega

-- 3^269 + 1: 7 divides 61333 + 1 and 13 + 1 (chains 61333; 61333 -> 13).
theorem kill3_e269 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 269 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61333 : 61333 ∈ P := S7 61333 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 269 = 3 ^ 200 * 3 ^ 69 from pow_add 3 200 69]; norm_num : 61333 ∣ 1 + 3 ^ 269).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 61333 g61333 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 61333 g61333 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^271 + 1: 5^2 divides 349 + 1 (chain 220586933947 -> 349).
theorem kill3_e271 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 271 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g220586933947 : 220586933947 ∈ P := S7 220586933947 prime_220586933947 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 271 = 3 ^ 200 * 3 ^ 71 from pow_add 3 200 71]; norm_num : 220586933947 ∣ 1 + 3 ^ 271).trans hd)
  have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 220586933947 g220586933947 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 349 g349 (by norm_num)

-- 3^274 + 1: 5 divides 3^274 + 1 and 29 + 1 (chain 344693 -> 29).
theorem kill3_e274 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 274 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g344693 : 344693 ∈ P := S7 344693 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 274 = 3 ^ 200 * 3 ^ 74 from pow_add 3 200 74]; norm_num : 344693 ∣ 1 + 3 ^ 274).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 344693 g344693 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 274 = 3 ^ 200 * 3 ^ 74 from pow_add 3 200 74]; norm_num : 5 ∣ 1 + 3 ^ 274).trans hd) 29 g29 (by norm_num)

-- 3^277 + 1: 19 divides 113 + 1 and 683 + 1 (chains 43035232876181345838699618577 -> 113; 43035232876181345838699618577 -> 683).
theorem kill3_e277 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 277 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43035232876181345838699618577 : 43035232876181345838699618577 ∈ P := S7 43035232876181345838699618577 prime_43035232876181345838699618577 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 277 = 3 ^ 200 * 3 ^ 77 from pow_add 3 200 77]; norm_num : 43035232876181345838699618577 ∣ 1 + 3 ^ 277).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 43035232876181345838699618577 g43035232876181345838699618577 (by norm_num)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 43035232876181345838699618577 g43035232876181345838699618577 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 683 g683 (by norm_num) (by norm_num)
  omega

-- 3^278 + 1: 5 divides 3^278 + 1 and 29 + 1 (chain 1107553 -> 79111 -> 29).
theorem kill3_e278 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 278 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1107553 : 1107553 ∈ P := S7 1107553 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 278 = 3 ^ 200 * 3 ^ 78 from pow_add 3 200 78]; norm_num : 1107553 ∣ 1 + 3 ^ 278).trans hd)
  have g79111 : 79111 ∈ P := S1 79111 (by norm_num) (by norm_num) (hnz (by norm_num)) 1107553 g1107553 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 79111 g79111 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 278 = 3 ^ 200 * 3 ^ 78 from pow_add 3 200 78]; norm_num : 5 ∣ 1 + 3 ^ 278).trans hd) 29 g29 (by norm_num)

-- 3^281 + 1: 7 divides 13 + 1 and 853 + 1 (chains 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 -> 233 -> 13; 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 -> 68239 -> 853).
theorem kill3_e281 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 281 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 : 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 ∈ P := S7 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 prime_29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 281 = 3 ^ 200 * 3 ^ 81 from pow_add 3 200 81]; norm_num : 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 ∣ 1 + 3 ^ 281).trans hd)
  have g233 : 233 ∈ P := S1 233 (by norm_num) (by norm_num) (hnz (by norm_num)) 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 g29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 233 g233 (by norm_num)
  have g68239 : 68239 ∈ P := S1 68239 (by norm_num) (by norm_num) (hnz (by norm_num)) 29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 g29445069578863612104789418133159256661148453875684032393263578374823854755200938919581381543747105355134879568496869483416658932556201 (by norm_num)
  have g853 : 853 ∈ P := S1 853 (by norm_num) (by norm_num) (hnz (by norm_num)) 68239 g68239 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 853 g853 (by norm_num) (by norm_num)
  omega

-- 3^283 + 1: 17 divides 101 + 1 and 4283 + 1 (chains 542985073109767895287 -> 3460663 -> 101; 542985073109767895287 -> 3460663 -> 4283).
theorem kill3_e283 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 283 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g542985073109767895287 : 542985073109767895287 ∈ P := S7 542985073109767895287 prime_542985073109767895287 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 283 = 3 ^ 200 * 3 ^ 83 from pow_add 3 200 83]; norm_num : 542985073109767895287 ∣ 1 + 3 ^ 283).trans hd)
  have g3460663 : 3460663 ∈ P := S1 3460663 (by norm_num) (by norm_num) (hnz (by norm_num)) 542985073109767895287 g542985073109767895287 (by norm_num)
  have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 3460663 g3460663 (by norm_num)
  have g4283 : 4283 ∈ P := S1 4283 (by norm_num) (by norm_num) (hnz (by norm_num)) 3460663 g3460663 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 4283 g4283 (by norm_num) (by norm_num)
  omega

-- 3^284 + 1: 5 divides 569 + 1 and 19 + 1 (chains 569; 569 -> 19).
theorem kill3_e284 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 284 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g569 : 569 ∈ P := S7 569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 284 = 3 ^ 200 * 3 ^ 84 from pow_add 3 200 84]; norm_num : 569 ∣ 1 + 3 ^ 284).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 569 g569 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 569 g569 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^292 + 1: 5^2 divides 349 + 1 (chain 65138399321 -> 349).
theorem kill3_e292 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 292 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g65138399321 : 65138399321 ∈ P := S7 65138399321 prime_65138399321 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 292 = 3 ^ 200 * 3 ^ 92 from pow_add 3 200 92]; norm_num : 65138399321 ∣ 1 + 3 ^ 292).trans hd)
  have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 65138399321 g65138399321 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 349 g349 (by norm_num)

-- 3^293 + 1: 1759 divides 3^293 + 1 and 3517 + 1 (chain 3517).
theorem kill3_e293 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 293 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3517 : 3517 ∈ P := S7 3517 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 293 = 3 ^ 200 * 3 ^ 93 from pow_add 3 200 93]; norm_num : 3517 ∣ 1 + 3 ^ 293).trans hd)
  exact S8 1759 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 293 = 3 ^ 200 * 3 ^ 93 from pow_add 3 200 93]; norm_num : 1759 ∣ 1 + 3 ^ 293).trans hd) 3517 g3517 (by norm_num)

-- 3^298 + 1: 5 divides 3^298 + 1 and 409 + 1 (chain 1869419288028691397 -> 409).
theorem kill3_e298 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 298 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1869419288028691397 : 1869419288028691397 ∈ P := S7 1869419288028691397 prime_1869419288028691397 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 298 = 3 ^ 200 * 3 ^ 98 from pow_add 3 200 98]; norm_num : 1869419288028691397 ∣ 1 + 3 ^ 298).trans hd)
  have g409 : 409 ∈ P := S1 409 (by norm_num) (by norm_num) (hnz (by norm_num)) 1869419288028691397 g1869419288028691397 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 298 = 3 ^ 200 * 3 ^ 98 from pow_add 3 200 98]; norm_num : 5 ∣ 1 + 3 ^ 298).trans hd) 409 g409 (by norm_num)

-- 3^302 + 1: 17 divides 7853 + 1 and 1281934384324308751 + 1 (chains 7853; 138448913507025345101 -> 23074818917837557517 -> 1281934384324308751).
theorem kill3_e302 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 302 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7853 : 7853 ∈ P := S7 7853 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 302 = 3 ^ 200 * 3 ^ 102 from pow_add 3 200 102]; norm_num : 7853 ∣ 1 + 3 ^ 302).trans hd)
  have g138448913507025345101 : 138448913507025345101 ∈ P := S7 138448913507025345101 prime_138448913507025345101 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 302 = 3 ^ 200 * 3 ^ 102 from pow_add 3 200 102]; norm_num : 138448913507025345101 ∣ 1 + 3 ^ 302).trans hd)
  have g23074818917837557517 : 23074818917837557517 ∈ P := S1 23074818917837557517 prime_23074818917837557517 (by norm_num) (hnz (by norm_num)) 138448913507025345101 g138448913507025345101 (by norm_num)
  have g1281934384324308751 : 1281934384324308751 ∈ P := S1 1281934384324308751 prime_1281934384324308751 (by norm_num) (hnz (by norm_num)) 23074818917837557517 g23074818917837557517 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 7853 g7853 1281934384324308751 g1281934384324308751 (by norm_num) (by norm_num)
  omega

-- 3^307 + 1: 5 divides 7369 + 1 and 19 + 1 (chains 7369; 174991 -> 10937 -> 1823 -> 19).
theorem kill3_e307 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 307 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7369 : 7369 ∈ P := S7 7369 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 307 = 3 ^ 200 * 3 ^ 107 from pow_add 3 200 107]; norm_num : 7369 ∣ 1 + 3 ^ 307).trans hd)
  have g174991 : 174991 ∈ P := S7 174991 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 307 = 3 ^ 200 * 3 ^ 107 from pow_add 3 200 107]; norm_num : 174991 ∣ 1 + 3 ^ 307).trans hd)
  have g10937 : 10937 ∈ P := S1 10937 (by norm_num) (by norm_num) (hnz (by norm_num)) 174991 g174991 (by norm_num)
  have g1823 : 1823 ∈ P := S1 1823 (by norm_num) (by norm_num) (hnz (by norm_num)) 10937 g10937 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1823 g1823 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7369 g7369 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^311 + 1: 7 divides 13 + 1 and 83 + 1 (chains 1867 -> 467 -> 13; 14929 -> 1493 -> 83).
theorem kill3_e311 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 311 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1867 : 1867 ∈ P := S7 1867 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 311 = 3 ^ 200 * 3 ^ 111 from pow_add 3 200 111]; norm_num : 1867 ∣ 1 + 3 ^ 311).trans hd)
  have g467 : 467 ∈ P := S1 467 (by norm_num) (by norm_num) (hnz (by norm_num)) 1867 g1867 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 467 g467 (by norm_num)
  have g14929 : 14929 ∈ P := S7 14929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 311 = 3 ^ 200 * 3 ^ 111 from pow_add 3 200 111]; norm_num : 14929 ∣ 1 + 3 ^ 311).trans hd)
  have g1493 : 1493 ∈ P := S1 1493 (by norm_num) (by norm_num) (hnz (by norm_num)) 14929 g14929 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493 g1493 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)
  omega

-- 3^313 + 1: 5 divides 1879 + 1 and 3391669 + 1 (chains 1879; 3391669).
theorem kill3_e313 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 313 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1879 : 1879 ∈ P := S7 1879 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 313 = 3 ^ 200 * 3 ^ 113 from pow_add 3 200 113]; norm_num : 1879 ∣ 1 + 3 ^ 313).trans hd)
  have g3391669 : 3391669 ∈ P := S7 3391669 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 313 = 3 ^ 200 * 3 ^ 113 from pow_add 3 200 113]; norm_num : 3391669 ∣ 1 + 3 ^ 313).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1879 g1879 3391669 g3391669 (by norm_num) (by norm_num)
  omega

-- 3^314 + 1: 5 divides 3^314 + 1 and 29 + 1 (chain 852197 -> 173 -> 29).
theorem kill3_e314 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 314 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g852197 : 852197 ∈ P := S7 852197 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 314 = 3 ^ 200 * 3 ^ 114 from pow_add 3 200 114]; norm_num : 852197 ∣ 1 + 3 ^ 314).trans hd)
  have g173 : 173 ∈ P := S1 173 (by norm_num) (by norm_num) (hnz (by norm_num)) 852197 g852197 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 314 = 3 ^ 200 * 3 ^ 114 from pow_add 3 200 114]; norm_num : 5 ∣ 1 + 3 ^ 314).trans hd) 29 g29 (by norm_num)

-- 3^316 + 1: 7^2 divides 4650491 + 1 (chain 362738297 -> 4650491).
theorem kill3_e316 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 316 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g362738297 : 362738297 ∈ P := S7 362738297 prime_362738297 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 316 = 3 ^ 200 * 3 ^ 116 from pow_add 3 200 116]; norm_num : 362738297 ∣ 1 + 3 ^ 316).trans hd)
  have g4650491 : 4650491 ∈ P := S1 4650491 (by norm_num) (by norm_num) (hnz (by norm_num)) 362738297 g362738297 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4650491 g4650491 (by norm_num)

-- 3^317 + 1: 5^2 divides 1152709099 + 1 (chain 76824655095930309016347566008213507 -> 1152709099).
theorem kill3_e317 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 317 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g76824655095930309016347566008213507 : 76824655095930309016347566008213507 ∈ P := S7 76824655095930309016347566008213507 prime_76824655095930309016347566008213507 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 317 = 3 ^ 200 * 3 ^ 117 from pow_add 3 200 117]; norm_num : 76824655095930309016347566008213507 ∣ 1 + 3 ^ 317).trans hd)
  have g1152709099 : 1152709099 ∈ P := S1 1152709099 prime_1152709099 (by norm_num) (hnz (by norm_num)) 76824655095930309016347566008213507 g76824655095930309016347566008213507 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1152709099 g1152709099 (by norm_num)

-- 3^326 + 1: 5 divides 3^326 + 1 and 109 + 1 (chain 653 -> 109).
theorem kill3_e326 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 326 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g653 : 653 ∈ P := S7 653 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 326 = 3 ^ 200 * 3 ^ 126 from pow_add 3 200 126]; norm_num : 653 ∣ 1 + 3 ^ 326).trans hd)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 653 g653 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 326 = 3 ^ 200 * 3 ^ 126 from pow_add 3 200 126]; norm_num : 5 ∣ 1 + 3 ^ 326).trans hd) 109 g109 (by norm_num)

-- 3^331 + 1: 13 divides 16274984685283 + 1 and 1181647 + 1 (chains 16274984685283; 16274984685283 -> 108711523 -> 1181647).
theorem kill3_e331 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 331 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g16274984685283 : 16274984685283 ∈ P := S7 16274984685283 prime_16274984685283 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 331 = 3 ^ 200 * 3 ^ 131 from pow_add 3 200 131]; norm_num : 16274984685283 ∣ 1 + 3 ^ 331).trans hd)
  have g108711523 : 108711523 ∈ P := S1 108711523 prime_108711523 (by norm_num) (hnz (by norm_num)) 16274984685283 g16274984685283 (by norm_num)
  have g1181647 : 1181647 ∈ P := S1 1181647 (by norm_num) (by norm_num) (hnz (by norm_num)) 108711523 g108711523 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 16274984685283 g16274984685283 1181647 g1181647 (by norm_num) (by norm_num)
  omega

-- 3^332 + 1: 5^2 divides 199 + 1 (chain 458427808464599360198958190584523975568577060978636244306691569817 -> 2148403 -> 199).
theorem kill3_e332 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 332 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g458427808464599360198958190584523975568577060978636244306691569817 : 458427808464599360198958190584523975568577060978636244306691569817 ∈ P := S7 458427808464599360198958190584523975568577060978636244306691569817 prime_458427808464599360198958190584523975568577060978636244306691569817 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 332 = 3 ^ 200 * 3 ^ 132 from pow_add 3 200 132]; norm_num : 458427808464599360198958190584523975568577060978636244306691569817 ∣ 1 + 3 ^ 332).trans hd)
  have g2148403 : 2148403 ∈ P := S1 2148403 (by norm_num) (by norm_num) (hnz (by norm_num)) 458427808464599360198958190584523975568577060978636244306691569817 g458427808464599360198958190584523975568577060978636244306691569817 (by norm_num)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 2148403 g2148403 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

-- 3^334 + 1: 5 divides 3^334 + 1 and 472939 + 1 (chain 1190204597436709967401788193 -> 472939).
theorem kill3_e334 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 334 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1190204597436709967401788193 : 1190204597436709967401788193 ∈ P := S7 1190204597436709967401788193 prime_1190204597436709967401788193 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 334 = 3 ^ 200 * 3 ^ 134 from pow_add 3 200 134]; norm_num : 1190204597436709967401788193 ∣ 1 + 3 ^ 334).trans hd)
  have g472939 : 472939 ∈ P := S1 472939 (by norm_num) (by norm_num) (hnz (by norm_num)) 1190204597436709967401788193 g1190204597436709967401788193 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 334 = 3 ^ 200 * 3 ^ 134 from pow_add 3 200 134]; norm_num : 5 ∣ 1 + 3 ^ 334).trans hd) 472939 g472939 (by norm_num)

-- 3^337 + 1: 5 divides 1009 + 1 and 220709 + 1 (chains 2671903153 -> 6053 -> 1009; 2671903153 -> 220709).
theorem kill3_e337 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 337 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2671903153 : 2671903153 ∈ P := S7 2671903153 prime_2671903153 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 337 = 3 ^ 200 * 3 ^ 137 from pow_add 3 200 137]; norm_num : 2671903153 ∣ 1 + 3 ^ 337).trans hd)
  have g6053 : 6053 ∈ P := S1 6053 (by norm_num) (by norm_num) (hnz (by norm_num)) 2671903153 g2671903153 (by norm_num)
  have g1009 : 1009 ∈ P := S1 1009 (by norm_num) (by norm_num) (hnz (by norm_num)) 6053 g6053 (by norm_num)
  have g220709 : 220709 ∈ P := S1 220709 (by norm_num) (by norm_num) (hnz (by norm_num)) 2671903153 g2671903153 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1009 g1009 220709 g220709 (by norm_num) (by norm_num)
  omega

-- 3^346 + 1: 7 divides 451723 + 1 and 13 + 1 (chains 3841314164761 -> 451723; 3841314164761 -> 451723 -> 13).
theorem kill3_e346 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 346 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3841314164761 : 3841314164761 ∈ P := S7 3841314164761 prime_3841314164761 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 346 = 3 ^ 200 * 3 ^ 146 from pow_add 3 200 146]; norm_num : 3841314164761 ∣ 1 + 3 ^ 346).trans hd)
  have g451723 : 451723 ∈ P := S1 451723 (by norm_num) (by norm_num) (hnz (by norm_num)) 3841314164761 g3841314164761 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 451723 g451723 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 451723 g451723 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^347 + 1: 11 divides 6247 + 1 and 1005349580545941002278829932925047441448714307550239169249631491 + 1 (chains 6247; 1005349580545941002278829932925047441448714307550239169249631491).
theorem kill3_e347 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 347 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6247 : 6247 ∈ P := S7 6247 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 347 = 3 ^ 200 * 3 ^ 147 from pow_add 3 200 147]; norm_num : 6247 ∣ 1 + 3 ^ 347).trans hd)
  have g1005349580545941002278829932925047441448714307550239169249631491 : 1005349580545941002278829932925047441448714307550239169249631491 ∈ P := S7 1005349580545941002278829932925047441448714307550239169249631491 prime_1005349580545941002278829932925047441448714307550239169249631491 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 347 = 3 ^ 200 * 3 ^ 147 from pow_add 3 200 147]; norm_num : 1005349580545941002278829932925047441448714307550239169249631491 ∣ 1 + 3 ^ 347).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 6247 g6247 1005349580545941002278829932925047441448714307550239169249631491 g1005349580545941002278829932925047441448714307550239169249631491 (by norm_num) (by norm_num)
  omega

-- 3^349 + 1: 13 divides 5572311991 + 1 and 5147 + 1 (chains 5572311991; 5572311991 -> 154409 -> 5147).
theorem kill3_e349 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 349 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5572311991 : 5572311991 ∈ P := S7 5572311991 prime_5572311991 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 349 = 3 ^ 200 * 3 ^ 149 from pow_add 3 200 149]; norm_num : 5572311991 ∣ 1 + 3 ^ 349).trans hd)
  have g154409 : 154409 ∈ P := S1 154409 (by norm_num) (by norm_num) (hnz (by norm_num)) 5572311991 g5572311991 (by norm_num)
  have g5147 : 5147 ∈ P := S1 5147 (by norm_num) (by norm_num) (hnz (by norm_num)) 154409 g154409 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 5572311991 g5572311991 5147 g5147 (by norm_num) (by norm_num)
  omega

-- 3^353 + 1: 13 divides 25005109 + 1 and 192347 + 1 (chains 25005109; 25005109 -> 192347).
theorem kill3_e353 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 353 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25005109 : 25005109 ∈ P := S7 25005109 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 353 = 3 ^ 200 * 3 ^ 153 from pow_add 3 200 153]; norm_num : 25005109 ∣ 1 + 3 ^ 353).trans hd)
  have g192347 : 192347 ∈ P := S1 192347 (by norm_num) (by norm_num) (hnz (by norm_num)) 25005109 g25005109 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 25005109 g25005109 192347 g192347 (by norm_num) (by norm_num)
  omega

-- 3^356 + 1: 7 divides 41 + 1 and 1324391188753961 + 1 (chains 41; 1324391188753961).
theorem kill3_e356 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 356 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 356 = 3 ^ 200 * 3 ^ 156 from pow_add 3 200 156]; norm_num : 41 ∣ 1 + 3 ^ 356).trans hd)
  have g1324391188753961 : 1324391188753961 ∈ P := S7 1324391188753961 prime_1324391188753961 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 356 = 3 ^ 200 * 3 ^ 156 from pow_add 3 200 156]; norm_num : 1324391188753961 ∣ 1 + 3 ^ 356).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 1324391188753961 g1324391188753961 (by norm_num) (by norm_num)
  omega

-- 3^358 + 1: 5 divides 3^358 + 1 and 668029 + 1 (chain 2672113 -> 1336057 -> 668029).
theorem kill3_e358 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 358 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2672113 : 2672113 ∈ P := S7 2672113 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 358 = 3 ^ 200 * 3 ^ 158 from pow_add 3 200 158]; norm_num : 2672113 ∣ 1 + 3 ^ 358).trans hd)
  have g1336057 : 1336057 ∈ P := S1 1336057 (by norm_num) (by norm_num) (hnz (by norm_num)) 2672113 g2672113 (by norm_num)
  have g668029 : 668029 ∈ P := S1 668029 (by norm_num) (by norm_num) (hnz (by norm_num)) 1336057 g1336057 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 358 = 3 ^ 200 * 3 ^ 158 from pow_add 3 200 158]; norm_num : 5 ∣ 1 + 3 ^ 358).trans hd) 668029 g668029 (by norm_num)

-- 3^361 + 1: 5 divides 389 + 1 and 504309322960550822349386758900289002291375600620610676536009 + 1 (chains 101917 -> 389; 504309322960550822349386758900289002291375600620610676536009).
theorem kill3_e361 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 361 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 361 = 3 ^ 200 * 3 ^ 161 from pow_add 3 200 161]; norm_num : 101917 ∣ 1 + 3 ^ 361).trans hd)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g504309322960550822349386758900289002291375600620610676536009 : 504309322960550822349386758900289002291375600620610676536009 ∈ P := S7 504309322960550822349386758900289002291375600620610676536009 prime_504309322960550822349386758900289002291375600620610676536009 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 361 = 3 ^ 200 * 3 ^ 161 from pow_add 3 200 161]; norm_num : 504309322960550822349386758900289002291375600620610676536009 ∣ 1 + 3 ^ 361).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 504309322960550822349386758900289002291375600620610676536009 g504309322960550822349386758900289002291375600620610676536009 (by norm_num) (by norm_num)
  omega

-- 3^367 + 1: 5 divides 19 + 1 and 29 + 1 (chains 2203 -> 19; 2203 -> 29).
theorem kill3_e367 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 367 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2203 : 2203 ∈ P := S7 2203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 367 = 3 ^ 200 * 3 ^ 167 from pow_add 3 200 167]; norm_num : 2203 ∣ 1 + 3 ^ 367).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

-- 3^373 + 1: 11 divides 23051401 + 1 and 307 + 1 (chains 23051401; 23051401 -> 307).
theorem kill3_e373 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 373 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23051401 : 23051401 ∈ P := S7 23051401 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 373 = 3 ^ 200 * 3 ^ 173 from pow_add 3 200 173]; norm_num : 23051401 ∣ 1 + 3 ^ 373).trans hd)
  have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 23051401 g23051401 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 23051401 g23051401 307 g307 (by norm_num) (by norm_num)
  omega

-- 3^379 + 1: 5 divides 29 + 1 and 79 + 1 (chains 54577 -> 29; 54577 -> 941 -> 157 -> 79).
theorem kill3_e379 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 379 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g54577 : 54577 ∈ P := S7 54577 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 379 = 3 ^ 200 * 3 ^ 179 from pow_add 3 200 179]; norm_num : 54577 ∣ 1 + 3 ^ 379).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 54577 g54577 (by norm_num)
  have g941 : 941 ∈ P := S1 941 (by norm_num) (by norm_num) (hnz (by norm_num)) 54577 g54577 (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 941 g941 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 79 g79 (by norm_num) (by norm_num)
  omega

-- 3^382 + 1: 5 divides 3^382 + 1 and 19 + 1 (chain 22692469873273 -> 19).
theorem kill3_e382 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 382 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g22692469873273 : 22692469873273 ∈ P := S7 22692469873273 prime_22692469873273 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 382 = 3 ^ 200 * 3 ^ 182 from pow_add 3 200 182]; norm_num : 22692469873273 ∣ 1 + 3 ^ 382).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 22692469873273 g22692469873273 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 382 = 3 ^ 200 * 3 ^ 182 from pow_add 3 200 182]; norm_num : 5 ∣ 1 + 3 ^ 382).trans hd) 19 g19 (by norm_num)

-- 3^383 + 1: 17 divides 862171 + 1 and 21521 + 1 (chains 266507551836102754532873191 -> 862171; 266507551836102754532873191 -> 2840771 -> 21521).
theorem kill3_e383 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 383 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g266507551836102754532873191 : 266507551836102754532873191 ∈ P := S7 266507551836102754532873191 prime_266507551836102754532873191 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 383 = 3 ^ 200 * 3 ^ 183 from pow_add 3 200 183]; norm_num : 266507551836102754532873191 ∣ 1 + 3 ^ 383).trans hd)
  have g862171 : 862171 ∈ P := S1 862171 (by norm_num) (by norm_num) (hnz (by norm_num)) 266507551836102754532873191 g266507551836102754532873191 (by norm_num)
  have g2840771 : 2840771 ∈ P := S1 2840771 (by norm_num) (by norm_num) (hnz (by norm_num)) 266507551836102754532873191 g266507551836102754532873191 (by norm_num)
  have g21521 : 21521 ∈ P := S1 21521 (by norm_num) (by norm_num) (hnz (by norm_num)) 2840771 g2840771 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 862171 g862171 21521 g21521 (by norm_num) (by norm_num)
  omega

-- 3^386 + 1: 5 divides 3^386 + 1 and 239 + 1 (chain 10037 -> 239).
theorem kill3_e386 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 386 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g10037 : 10037 ∈ P := S7 10037 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 386 = 3 ^ 200 * 3 ^ 186 from pow_add 3 200 186]; norm_num : 10037 ∣ 1 + 3 ^ 386).trans hd)
  have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 10037 g10037 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 386 = 3 ^ 200 * 3 ^ 186 from pow_add 3 200 186]; norm_num : 5 ∣ 1 + 3 ^ 386).trans hd) 239 g239 (by norm_num)

-- 3^388 + 1: 7 divides 41 + 1 and 158017 + 1 (chains 41; 1371903593 -> 158017).
theorem kill3_e388 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 388 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 388 = 3 ^ 200 * 3 ^ 188 from pow_add 3 200 188]; norm_num : 41 ∣ 1 + 3 ^ 388).trans hd)
  have g1371903593 : 1371903593 ∈ P := S7 1371903593 prime_1371903593 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 388 = 3 ^ 200 * 3 ^ 188 from pow_add 3 200 188]; norm_num : 1371903593 ∣ 1 + 3 ^ 388).trans hd)
  have g158017 : 158017 ∈ P := S1 158017 (by norm_num) (by norm_num) (hnz (by norm_num)) 1371903593 g1371903593 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 158017 g158017 (by norm_num) (by norm_num)
  omega

-- 3^389 + 1: 5 divides 165589 + 1 and 29 + 1 (chains 9272983 -> 165589; 9272983 -> 165589 -> 29).
theorem kill3_e389 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 389 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9272983 : 9272983 ∈ P := S7 9272983 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 389 = 3 ^ 200 * 3 ^ 189 from pow_add 3 200 189]; norm_num : 9272983 ∣ 1 + 3 ^ 389).trans hd)
  have g165589 : 165589 ∈ P := S1 165589 (by norm_num) (by norm_num) (hnz (by norm_num)) 9272983 g9272983 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 165589 g165589 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 165589 g165589 29 g29 (by norm_num) (by norm_num)
  omega

-- 3^394 + 1: 5 divides 3^394 + 1 and 4729 + 1 (chain 4729).
theorem kill3_e394 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 394 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4729 : 4729 ∈ P := S7 4729 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 394 = 3 ^ 200 * 3 ^ 194 from pow_add 3 200 194]; norm_num : 4729 ∣ 1 + 3 ^ 394).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 394 = 3 ^ 200 * 3 ^ 194 from pow_add 3 200 194]; norm_num : 5 ∣ 1 + 3 ^ 394).trans hd) 4729 g4729 (by norm_num)

-- 3^397 + 1: 5^2 divides 149 + 1 (chain 2383 -> 149).
theorem kill3_e397 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 397 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2383 : 2383 ∈ P := S7 2383 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 397 = 3 ^ 200 * 3 ^ 197 from pow_add 3 200 197]; norm_num : 2383 ∣ 1 + 3 ^ 397).trans hd)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 2383 g2383 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- 3^398 + 1: 5 divides 3^398 + 1 and 19 + 1 (chain 797 -> 19).
theorem kill3_e398 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 398 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g797 : 797 ∈ P := S7 797 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 398 = 3 ^ 200 * 3 ^ 198 from pow_add 3 200 198]; norm_num : 797 ∣ 1 + 3 ^ 398).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 797 g797 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 398 = 3 ^ 200 * 3 ^ 198 from pow_add 3 200 198]; norm_num : 5 ∣ 1 + 3 ^ 398).trans hd) 19 g19 (by norm_num)

-- 3^401 + 1: 5 divides 67369 + 1 and 79 + 1 (chains 67369; 907284546446671 -> 631 -> 79).
theorem kill3_e401 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 401 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67369 : 67369 ∈ P := S7 67369 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 401 = 3 ^ 200 * 3 ^ 201 from pow_add 3 200 201]; norm_num : 67369 ∣ 1 + 3 ^ 401).trans hd)
  have g907284546446671 : 907284546446671 ∈ P := S7 907284546446671 prime_907284546446671 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 401 = 3 ^ 200 * 3 ^ 201 from pow_add 3 200 201]; norm_num : 907284546446671 ∣ 1 + 3 ^ 401).trans hd)
  have g631 : 631 ∈ P := S1 631 (by norm_num) (by norm_num) (hnz (by norm_num)) 907284546446671 g907284546446671 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 631 g631 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 67369 g67369 79 g79 (by norm_num) (by norm_num)
  omega

-- 3^404 + 1: 5 divides 809 + 1 and 3230519 + 1 (chains 809; 19383113 -> 3230519).
theorem kill3_e404 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 404 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g809 : 809 ∈ P := S7 809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 404 = 3 ^ 200 * 3 ^ 204 from pow_add 3 200 204]; norm_num : 809 ∣ 1 + 3 ^ 404).trans hd)
  have g19383113 : 19383113 ∈ P := S7 19383113 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 404 = 3 ^ 200 * 3 ^ 204 from pow_add 3 200 204]; norm_num : 19383113 ∣ 1 + 3 ^ 404).trans hd)
  have g3230519 : 3230519 ∈ P := S1 3230519 (by norm_num) (by norm_num) (hnz (by norm_num)) 19383113 g19383113 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 809 g809 3230519 g3230519 (by norm_num) (by norm_num)
  omega

-- 3^409 + 1: 11 divides 298693 + 1 and 4990303 + 1 (chains 4499059465218602986753482277322389 -> 298693; 4499059465218602986753482277322389 -> 4990303).
theorem kill3_e409 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 409 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4499059465218602986753482277322389 : 4499059465218602986753482277322389 ∈ P := S7 4499059465218602986753482277322389 prime_4499059465218602986753482277322389 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 409 = 3 ^ 200 * 3 ^ 209 from pow_add 3 200 209]; norm_num : 4499059465218602986753482277322389 ∣ 1 + 3 ^ 409).trans hd)
  have g298693 : 298693 ∈ P := S1 298693 (by norm_num) (by norm_num) (hnz (by norm_num)) 4499059465218602986753482277322389 g4499059465218602986753482277322389 (by norm_num)
  have g4990303 : 4990303 ∈ P := S1 4990303 (by norm_num) (by norm_num) (hnz (by norm_num)) 4499059465218602986753482277322389 g4499059465218602986753482277322389 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 298693 g298693 4990303 g4990303 (by norm_num) (by norm_num)
  omega

-- 3^412 + 1: 11 divides 345047 + 1 and 1911029 + 1 (chains 12872193124359179360957763595281172943047231391521 -> 345047; 12872193124359179360957763595281172943047231391521 -> 1911029).
theorem kill3_e412 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 412 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12872193124359179360957763595281172943047231391521 : 12872193124359179360957763595281172943047231391521 ∈ P := S7 12872193124359179360957763595281172943047231391521 prime_12872193124359179360957763595281172943047231391521 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 412 = 3 ^ 200 * 3 ^ 212 from pow_add 3 200 212]; norm_num : 12872193124359179360957763595281172943047231391521 ∣ 1 + 3 ^ 412).trans hd)
  have g345047 : 345047 ∈ P := S1 345047 (by norm_num) (by norm_num) (hnz (by norm_num)) 12872193124359179360957763595281172943047231391521 g12872193124359179360957763595281172943047231391521 (by norm_num)
  have g1911029 : 1911029 ∈ P := S1 1911029 (by norm_num) (by norm_num) (hnz (by norm_num)) 12872193124359179360957763595281172943047231391521 g12872193124359179360957763595281172943047231391521 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 345047 g345047 1911029 g1911029 (by norm_num) (by norm_num)
  omega

-- 3^419 + 1: 11 divides 105821803 + 1 and 769 + 1 (chains 105821803; 105821803 -> 6151 -> 769).
theorem kill3_e419 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 419 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g105821803 : 105821803 ∈ P := S7 105821803 prime_105821803 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 419 = 3 ^ 200 * 3 ^ 219 from pow_add 3 200 219]; norm_num : 105821803 ∣ 1 + 3 ^ 419).trans hd)
  have g6151 : 6151 ∈ P := S1 6151 (by norm_num) (by norm_num) (hnz (by norm_num)) 105821803 g105821803 (by norm_num)
  have g769 : 769 ∈ P := S1 769 (by norm_num) (by norm_num) (hnz (by norm_num)) 6151 g6151 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 105821803 g105821803 769 g769 (by norm_num) (by norm_num)
  omega

-- 3^421 + 1: 5^2 divides 47610049 + 1 (chain 47610049).
theorem kill3_e421 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 421 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g47610049 : 47610049 ∈ P := S7 47610049 prime_47610049 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 421 = 3 ^ 200 * 3 ^ 221 from pow_add 3 200 221]; norm_num : 47610049 ∣ 1 + 3 ^ 421).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 47610049 g47610049 (by norm_num)

-- 3^422 + 1: 5 divides 3^422 + 1 and 19 + 1 (chain 7670841701 -> 37 -> 19).
theorem kill3_e422 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 422 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7670841701 : 7670841701 ∈ P := S7 7670841701 prime_7670841701 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 422 = 3 ^ 200 * 3 ^ 222 from pow_add 3 200 222]; norm_num : 7670841701 ∣ 1 + 3 ^ 422).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 7670841701 g7670841701 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 422 = 3 ^ 200 * 3 ^ 222 from pow_add 3 200 222]; norm_num : 5 ∣ 1 + 3 ^ 422).trans hd) 19 g19 (by norm_num)

-- 3^428 + 1: 7 divides 41 + 1 and 13 + 1 (chains 41; 857 -> 13).
theorem kill3_e428 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 428 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 428 = 3 ^ 200 * 3 ^ 228 from pow_add 3 200 228]; norm_num : 41 ∣ 1 + 3 ^ 428).trans hd)
  have g857 : 857 ∈ P := S7 857 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 428 = 3 ^ 200 * 3 ^ 228 from pow_add 3 200 228]; norm_num : 857 ∣ 1 + 3 ^ 428).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 857 g857 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^431 + 1: 5^2 divides 46549 + 1 (chain 93097 -> 46549).
theorem kill3_e431 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 431 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g93097 : 93097 ∈ P := S7 93097 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 431 = 3 ^ 200 * 3 ^ 231 from pow_add 3 200 231]; norm_num : 93097 ∣ 1 + 3 ^ 431).trans hd)
  have g46549 : 46549 ∈ P := S1 46549 (by norm_num) (by norm_num) (hnz (by norm_num)) 93097 g93097 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 46549 g46549 (by norm_num)

-- 3^433 + 1: 11 divides 25981 + 1 and 197 + 1 (chains 25981; 25981 -> 1181 -> 197).
theorem kill3_e433 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 433 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25981 : 25981 ∈ P := S7 25981 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 433 = 3 ^ 200 * 3 ^ 233 from pow_add 3 200 233]; norm_num : 25981 ∣ 1 + 3 ^ 433).trans hd)
  have g1181 : 1181 ∈ P := S1 1181 (by norm_num) (by norm_num) (hnz (by norm_num)) 25981 g25981 (by norm_num)
  have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 1181 g1181 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 25981 g25981 197 g197 (by norm_num) (by norm_num)
  omega

-- 3^436 + 1: 5 divides 229 + 1 and 829 + 1 (chains 6797644660321 -> 229; 6797644660321 -> 829).
theorem kill3_e436 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 436 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6797644660321 : 6797644660321 ∈ P := S7 6797644660321 prime_6797644660321 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 436 = 3 ^ 200 * 3 ^ 236 from pow_add 3 200 236]; norm_num : 6797644660321 ∣ 1 + 3 ^ 436).trans hd)
  have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 6797644660321 g6797644660321 (by norm_num)
  have g829 : 829 ∈ P := S1 829 (by norm_num) (by norm_num) (hnz (by norm_num)) 6797644660321 g6797644660321 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 229 g229 829 g829 (by norm_num) (by norm_num)
  omega

-- 3^439 + 1: 5 divides 19 + 1 and 89 + 1 (chains 13171 -> 37 -> 19; 13171 -> 89).
theorem kill3_e439 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 439 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13171 : 13171 ∈ P := S7 13171 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 439 = 3 ^ 200 * 3 ^ 239 from pow_add 3 200 239]; norm_num : 13171 ∣ 1 + 3 ^ 439).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 13171 g13171 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 13171 g13171 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 89 g89 (by norm_num) (by norm_num)
  omega

-- 3^443 + 1: 7 divides 1637 + 1 and 13 + 1 (chains 163897597 -> 6547 -> 1637; 163897597 -> 6547 -> 1637 -> 13).
theorem kill3_e443 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 443 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g163897597 : 163897597 ∈ P := S7 163897597 prime_163897597 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 443 = 3 ^ 200 * 3 ^ 243 from pow_add 3 200 243]; norm_num : 163897597 ∣ 1 + 3 ^ 443).trans hd)
  have g6547 : 6547 ∈ P := S1 6547 (by norm_num) (by norm_num) (hnz (by norm_num)) 163897597 g163897597 (by norm_num)
  have g1637 : 1637 ∈ P := S1 1637 (by norm_num) (by norm_num) (hnz (by norm_num)) 6547 g6547 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1637 g1637 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1637 g1637 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^449 + 1: 5 divides 490309 + 1 and 19 + 1 (chains 490309; 490309 -> 49031 -> 227 -> 19).
theorem kill3_e449 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 449 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g490309 : 490309 ∈ P := S7 490309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 449 = 3 ^ 200 * 3 ^ 249 from pow_add 3 200 249]; norm_num : 490309 ∣ 1 + 3 ^ 449).trans hd)
  have g49031 : 49031 ∈ P := S1 49031 (by norm_num) (by norm_num) (hnz (by norm_num)) 490309 g490309 (by norm_num)
  have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 49031 g49031 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 490309 g490309 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^452 + 1: 41 divides 3^452 + 1 and 163 + 1 (chain 5675504055555452009 -> 163).
theorem kill3_e452 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 452 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5675504055555452009 : 5675504055555452009 ∈ P := S7 5675504055555452009 prime_5675504055555452009 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 452 = 3 ^ 200 * 3 ^ 252 from pow_add 3 200 252]; norm_num : 5675504055555452009 ∣ 1 + 3 ^ 452).trans hd)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 5675504055555452009 g5675504055555452009 (by norm_num)
  exact S8 41 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 452 = 3 ^ 200 * 3 ^ 252 from pow_add 3 200 252]; norm_num : 41 ∣ 1 + 3 ^ 452).trans hd) 163 g163 (by norm_num)

-- 3^454 + 1: 7 divides 34622041 + 1 and 13 + 1 (chains 34622041; 34622041 -> 13).
theorem kill3_e454 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 454 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g34622041 : 34622041 ∈ P := S7 34622041 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 454 = 3 ^ 200 * 3 ^ 254 from pow_add 3 200 254]; norm_num : 34622041 ∣ 1 + 3 ^ 454).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 34622041 g34622041 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 34622041 g34622041 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^457 + 1: 17^2 divides 9483823 + 1 (chain 35545368601 -> 17772684301 -> 9483823).
theorem kill3_e457 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 457 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g35545368601 : 35545368601 ∈ P := S7 35545368601 prime_35545368601 (by norm_num) (hnz (by norm_num))
    ((by decide : 35545368601 ∣ 1 + 3 ^ 457).trans hd)
  have g17772684301 : 17772684301 ∈ P := S1 17772684301 prime_17772684301 (by norm_num) (hnz (by norm_num)) 35545368601 g35545368601 (by norm_num)
  have g9483823 : 9483823 ∈ P := S1 9483823 (by norm_num) (by norm_num) (hnz (by norm_num)) 17772684301 g17772684301 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 9483823 g9483823 (by norm_num)

-- 3^461 + 1: 11 divides 43 + 1 and 1732006494877 + 1 (chains 297905117118757 -> 43; 297905117118757 -> 3464012989753 -> 1732006494877).
theorem kill3_e461 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 461 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g297905117118757 : 297905117118757 ∈ P := S7 297905117118757 prime_297905117118757 (by norm_num) (hnz (by norm_num))
    ((by decide : 297905117118757 ∣ 1 + 3 ^ 461).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 297905117118757 g297905117118757 (by norm_num)
  have g3464012989753 : 3464012989753 ∈ P := S1 3464012989753 prime_3464012989753 (by norm_num) (hnz (by norm_num)) 297905117118757 g297905117118757 (by norm_num)
  have g1732006494877 : 1732006494877 ∈ P := S1 1732006494877 prime_1732006494877 (by norm_num) (hnz (by norm_num)) 3464012989753 g3464012989753 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 1732006494877 g1732006494877 (by norm_num) (by norm_num)
  omega

-- 3^463 + 1: 7^2 divides 1169028365166332873 + 1 (chain 614908920077491091197 -> 1169028365166332873).
theorem kill3_e463 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 463 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g614908920077491091197 : 614908920077491091197 ∈ P := S7 614908920077491091197 prime_614908920077491091197 (by norm_num) (hnz (by norm_num))
    ((by decide : 614908920077491091197 ∣ 1 + 3 ^ 463).trans hd)
  have g1169028365166332873 : 1169028365166332873 ∈ P := S1 1169028365166332873 prime_1169028365166332873 (by norm_num) (hnz (by norm_num)) 614908920077491091197 g614908920077491091197 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1169028365166332873 g1169028365166332873 (by norm_num)

-- 3^466 + 1: 5 divides 3^466 + 1 and 3733008450772109 + 1 (chain 3733008450772109).
theorem kill3_e466 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 466 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3733008450772109 : 3733008450772109 ∈ P := S7 3733008450772109 prime_3733008450772109 (by norm_num) (hnz (by norm_num))
    ((by decide : 3733008450772109 ∣ 1 + 3 ^ 466).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by decide : 5 ∣ 1 + 3 ^ 466).trans hd) 3733008450772109 g3733008450772109 (by norm_num)

-- 3^467 + 1: 7 divides 13 + 1 and 83 + 1 (chains 2803 -> 701 -> 13; 70051 -> 83).
theorem kill3_e467 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 467 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2803 : 2803 ∈ P := S7 2803 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by decide : 2803 ∣ 1 + 3 ^ 467).trans hd)
  have g701 : 701 ∈ P := S1 701 (by norm_num) (by norm_num) (hnz (by norm_num)) 2803 g2803 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 701 g701 (by norm_num)
  have g70051 : 70051 ∈ P := S7 70051 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by decide : 70051 ∣ 1 + 3 ^ 467).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 70051 g70051 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)
  omega

-- 3^478 + 1: 5 divides 3^478 + 1 and 19 + 1 (chain 5737 -> 19).
theorem kill3_e478 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 478 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5737 : 5737 ∈ P := S7 5737 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by decide : 5737 ∣ 1 + 3 ^ 478).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 5737 g5737 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by decide : 5 ∣ 1 + 3 ^ 478).trans hd) 19 g19 (by norm_num)

-- 3^479 + 1: 5 divides 19759 + 1 and 19 + 1 (chains 158071 -> 19759; 158071 -> 19759 -> 19).
theorem kill3_e479 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 479 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g158071 : 158071 ∈ P := S7 158071 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by decide : 158071 ∣ 1 + 3 ^ 479).trans hd)
  have g19759 : 19759 ∈ P := S1 19759 (by norm_num) (by norm_num) (hnz (by norm_num)) 158071 g158071 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 19759 g19759 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19759 g19759 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^482 + 1: 7^2 divides 41453 + 1 (chain 41453).
theorem kill3_e482 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 482 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41453 : 41453 ∈ P := S7 41453 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by decide : 41453 ∣ 1 + 3 ^ 482).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41453 g41453 (by norm_num)

-- 3^491 + 1: 5 divides 59 + 1 and 1789 + 1 (chains 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 -> 422203 -> 59; 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 -> 422203 -> 1789).
theorem kill3_e491 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 491 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 : 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 ∈ P := S7 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 prime_60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 (by norm_num) (hnz (by norm_num))
    ((by decide : 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 ∣ 1 + 3 ^ 491).trans hd)
  have g422203 : 422203 ∈ P := S1 422203 (by norm_num) (by norm_num) (hnz (by norm_num)) 60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 g60892643104482757573306223567662688740985969197465290654173842691745096014633691396823 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 422203 g422203 (by norm_num)
  have g1789 : 1789 ∈ P := S1 1789 (by norm_num) (by norm_num) (hnz (by norm_num)) 422203 g422203 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 1789 g1789 (by norm_num) (by norm_num)
  omega

-- kernel 3^e: the new excluded classes (201 ≤ d ≤ 500)
theorem core3_residues_new {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    e % 404 ≠ 202 ∧
      e % 412 ≠ 206 ∧
      e % 418 ≠ 209 ∧
      e % 422 ≠ 211 ∧
      e % 424 ≠ 212 ∧
      e % 428 ≠ 214 ∧
      e % 436 ≠ 218 ∧
      e % 446 ≠ 223 ∧
      e % 452 ≠ 226 ∧
      e % 454 ≠ 227 ∧
      e % 458 ≠ 229 ∧
      e % 466 ≠ 233 ∧
      e % 472 ≠ 236 ∧
      e % 478 ≠ 239 ∧
      e % 482 ≠ 241 ∧
      e % 488 ≠ 244 ∧
      e % 494 ≠ 247 ∧
      e % 502 ≠ 251 ∧
      e % 508 ≠ 254 ∧
      e % 512 ≠ 256 ∧
      e % 514 ≠ 257 ∧
      e % 524 ≠ 262 ∧
      e % 526 ≠ 263 ∧
      e % 536 ≠ 268 ∧
      e % 538 ≠ 269 ∧
      e % 542 ≠ 271 ∧
      e % 548 ≠ 274 ∧
      e % 554 ≠ 277 ∧
      e % 556 ≠ 278 ∧
      e % 562 ≠ 281 ∧
      e % 566 ≠ 283 ∧
      e % 568 ≠ 284 ∧
      e % 584 ≠ 292 ∧
      e % 586 ≠ 293 ∧
      e % 596 ≠ 298 ∧
      e % 604 ≠ 302 ∧
      e % 614 ≠ 307 ∧
      e % 622 ≠ 311 ∧
      e % 626 ≠ 313 ∧
      e % 628 ≠ 314 ∧
      e % 632 ≠ 316 ∧
      e % 634 ≠ 317 ∧
      e % 652 ≠ 326 ∧
      e % 662 ≠ 331 ∧
      e % 664 ≠ 332 ∧
      e % 668 ≠ 334 ∧
      e % 674 ≠ 337 ∧
      e % 692 ≠ 346 ∧
      e % 694 ≠ 347 ∧
      e % 698 ≠ 349 ∧
      e % 706 ≠ 353 ∧
      e % 712 ≠ 356 ∧
      e % 716 ≠ 358 ∧
      e % 722 ≠ 361 ∧
      e % 734 ≠ 367 ∧
      e % 746 ≠ 373 ∧
      e % 758 ≠ 379 ∧
      e % 764 ≠ 382 ∧
      e % 766 ≠ 383 ∧
      e % 772 ≠ 386 ∧
      e % 776 ≠ 388 ∧
      e % 778 ≠ 389 ∧
      e % 788 ≠ 394 ∧
      e % 794 ≠ 397 ∧
      e % 796 ≠ 398 ∧
      e % 802 ≠ 401 ∧
      e % 808 ≠ 404 ∧
      e % 818 ≠ 409 ∧
      e % 824 ≠ 412 ∧
      e % 838 ≠ 419 ∧
      e % 842 ≠ 421 ∧
      e % 844 ≠ 422 ∧
      e % 856 ≠ 428 ∧
      e % 862 ≠ 431 ∧
      e % 866 ≠ 433 ∧
      e % 872 ≠ 436 ∧
      e % 878 ≠ 439 ∧
      e % 886 ≠ 443 ∧
      e % 898 ≠ 449 ∧
      e % 904 ≠ 452 ∧
      e % 908 ≠ 454 ∧
      e % 914 ≠ 457 ∧
      e % 922 ≠ 461 ∧
      e % 926 ≠ 463 ∧
      e % 932 ≠ 466 ∧
      e % 934 ≠ 467 ∧
      e % 956 ≠ 478 ∧
      e % 958 ≠ 479 ∧
      e % 964 ≠ 482 ∧
      e % 982 ≠ 491 :=
  ⟨fun h => kill3_e202 hP E (one_add_pow_dvd_of_odd_mul (e0 := 202) (by omega)),
   fun h => kill3_e206 hP E (one_add_pow_dvd_of_odd_mul (e0 := 206) (by omega)),
   fun h => kill3_e209 hP E (one_add_pow_dvd_of_odd_mul (e0 := 209) (by omega)),
   fun h => kill3_e211 hP E (one_add_pow_dvd_of_odd_mul (e0 := 211) (by omega)),
   fun h => kill3_e212 hP E (one_add_pow_dvd_of_odd_mul (e0 := 212) (by omega)),
   fun h => kill3_e214 hP E (one_add_pow_dvd_of_odd_mul (e0 := 214) (by omega)),
   fun h => kill3_e218 hP E (one_add_pow_dvd_of_odd_mul (e0 := 218) (by omega)),
   fun h => kill3_e223 hP E (one_add_pow_dvd_of_odd_mul (e0 := 223) (by omega)),
   fun h => kill3_e226 hP E (one_add_pow_dvd_of_odd_mul (e0 := 226) (by omega)),
   fun h => kill3_e227 hP E (one_add_pow_dvd_of_odd_mul (e0 := 227) (by omega)),
   fun h => kill3_e229 hP E (one_add_pow_dvd_of_odd_mul (e0 := 229) (by omega)),
   fun h => kill3_e233 hP E (one_add_pow_dvd_of_odd_mul (e0 := 233) (by omega)),
   fun h => kill3_e236 hP E (one_add_pow_dvd_of_odd_mul (e0 := 236) (by omega)),
   fun h => kill3_e239 hP E (one_add_pow_dvd_of_odd_mul (e0 := 239) (by omega)),
   fun h => kill3_e241 hP E (one_add_pow_dvd_of_odd_mul (e0 := 241) (by omega)),
   fun h => kill3_e244 hP E (one_add_pow_dvd_of_odd_mul (e0 := 244) (by omega)),
   fun h => kill3_e247 hP E (one_add_pow_dvd_of_odd_mul (e0 := 247) (by omega)),
   fun h => kill3_e251 hP E (one_add_pow_dvd_of_odd_mul (e0 := 251) (by omega)),
   fun h => kill3_e254 hP E (one_add_pow_dvd_of_odd_mul (e0 := 254) (by omega)),
   fun h => kill3_e256 hP E (one_add_pow_dvd_of_odd_mul (e0 := 256) (by omega)),
   fun h => kill3_e257 hP E (one_add_pow_dvd_of_odd_mul (e0 := 257) (by omega)),
   fun h => kill3_e262 hP E (one_add_pow_dvd_of_odd_mul (e0 := 262) (by omega)),
   fun h => kill3_e263 hP E (one_add_pow_dvd_of_odd_mul (e0 := 263) (by omega)),
   fun h => kill3_e268 hP E (one_add_pow_dvd_of_odd_mul (e0 := 268) (by omega)),
   fun h => kill3_e269 hP E (one_add_pow_dvd_of_odd_mul (e0 := 269) (by omega)),
   fun h => kill3_e271 hP E (one_add_pow_dvd_of_odd_mul (e0 := 271) (by omega)),
   fun h => kill3_e274 hP E (one_add_pow_dvd_of_odd_mul (e0 := 274) (by omega)),
   fun h => kill3_e277 hP E (one_add_pow_dvd_of_odd_mul (e0 := 277) (by omega)),
   fun h => kill3_e278 hP E (one_add_pow_dvd_of_odd_mul (e0 := 278) (by omega)),
   fun h => kill3_e281 hP E (one_add_pow_dvd_of_odd_mul (e0 := 281) (by omega)),
   fun h => kill3_e283 hP E (one_add_pow_dvd_of_odd_mul (e0 := 283) (by omega)),
   fun h => kill3_e284 hP E (one_add_pow_dvd_of_odd_mul (e0 := 284) (by omega)),
   fun h => kill3_e292 hP E (one_add_pow_dvd_of_odd_mul (e0 := 292) (by omega)),
   fun h => kill3_e293 hP E (one_add_pow_dvd_of_odd_mul (e0 := 293) (by omega)),
   fun h => kill3_e298 hP E (one_add_pow_dvd_of_odd_mul (e0 := 298) (by omega)),
   fun h => kill3_e302 hP E (one_add_pow_dvd_of_odd_mul (e0 := 302) (by omega)),
   fun h => kill3_e307 hP E (one_add_pow_dvd_of_odd_mul (e0 := 307) (by omega)),
   fun h => kill3_e311 hP E (one_add_pow_dvd_of_odd_mul (e0 := 311) (by omega)),
   fun h => kill3_e313 hP E (one_add_pow_dvd_of_odd_mul (e0 := 313) (by omega)),
   fun h => kill3_e314 hP E (one_add_pow_dvd_of_odd_mul (e0 := 314) (by omega)),
   fun h => kill3_e316 hP E (one_add_pow_dvd_of_odd_mul (e0 := 316) (by omega)),
   fun h => kill3_e317 hP E (one_add_pow_dvd_of_odd_mul (e0 := 317) (by omega)),
   fun h => kill3_e326 hP E (one_add_pow_dvd_of_odd_mul (e0 := 326) (by omega)),
   fun h => kill3_e331 hP E (one_add_pow_dvd_of_odd_mul (e0 := 331) (by omega)),
   fun h => kill3_e332 hP E (one_add_pow_dvd_of_odd_mul (e0 := 332) (by omega)),
   fun h => kill3_e334 hP E (one_add_pow_dvd_of_odd_mul (e0 := 334) (by omega)),
   fun h => kill3_e337 hP E (one_add_pow_dvd_of_odd_mul (e0 := 337) (by omega)),
   fun h => kill3_e346 hP E (one_add_pow_dvd_of_odd_mul (e0 := 346) (by omega)),
   fun h => kill3_e347 hP E (one_add_pow_dvd_of_odd_mul (e0 := 347) (by omega)),
   fun h => kill3_e349 hP E (one_add_pow_dvd_of_odd_mul (e0 := 349) (by omega)),
   fun h => kill3_e353 hP E (one_add_pow_dvd_of_odd_mul (e0 := 353) (by omega)),
   fun h => kill3_e356 hP E (one_add_pow_dvd_of_odd_mul (e0 := 356) (by omega)),
   fun h => kill3_e358 hP E (one_add_pow_dvd_of_odd_mul (e0 := 358) (by omega)),
   fun h => kill3_e361 hP E (one_add_pow_dvd_of_odd_mul (e0 := 361) (by omega)),
   fun h => kill3_e367 hP E (one_add_pow_dvd_of_odd_mul (e0 := 367) (by omega)),
   fun h => kill3_e373 hP E (one_add_pow_dvd_of_odd_mul (e0 := 373) (by omega)),
   fun h => kill3_e379 hP E (one_add_pow_dvd_of_odd_mul (e0 := 379) (by omega)),
   fun h => kill3_e382 hP E (one_add_pow_dvd_of_odd_mul (e0 := 382) (by omega)),
   fun h => kill3_e383 hP E (one_add_pow_dvd_of_odd_mul (e0 := 383) (by omega)),
   fun h => kill3_e386 hP E (one_add_pow_dvd_of_odd_mul (e0 := 386) (by omega)),
   fun h => kill3_e388 hP E (one_add_pow_dvd_of_odd_mul (e0 := 388) (by omega)),
   fun h => kill3_e389 hP E (one_add_pow_dvd_of_odd_mul (e0 := 389) (by omega)),
   fun h => kill3_e394 hP E (one_add_pow_dvd_of_odd_mul (e0 := 394) (by omega)),
   fun h => kill3_e397 hP E (one_add_pow_dvd_of_odd_mul (e0 := 397) (by omega)),
   fun h => kill3_e398 hP E (one_add_pow_dvd_of_odd_mul (e0 := 398) (by omega)),
   fun h => kill3_e401 hP E (one_add_pow_dvd_of_odd_mul (e0 := 401) (by omega)),
   fun h => kill3_e404 hP E (one_add_pow_dvd_of_odd_mul (e0 := 404) (by omega)),
   fun h => kill3_e409 hP E (one_add_pow_dvd_of_odd_mul (e0 := 409) (by omega)),
   fun h => kill3_e412 hP E (one_add_pow_dvd_of_odd_mul (e0 := 412) (by omega)),
   fun h => kill3_e419 hP E (one_add_pow_dvd_of_odd_mul (e0 := 419) (by omega)),
   fun h => kill3_e421 hP E (one_add_pow_dvd_of_odd_mul (e0 := 421) (by omega)),
   fun h => kill3_e422 hP E (one_add_pow_dvd_of_odd_mul (e0 := 422) (by omega)),
   fun h => kill3_e428 hP E (one_add_pow_dvd_of_odd_mul (e0 := 428) (by omega)),
   fun h => kill3_e431 hP E (one_add_pow_dvd_of_odd_mul (e0 := 431) (by omega)),
   fun h => kill3_e433 hP E (one_add_pow_dvd_of_odd_mul (e0 := 433) (by omega)),
   fun h => kill3_e436 hP E (one_add_pow_dvd_of_odd_mul (e0 := 436) (by omega)),
   fun h => kill3_e439 hP E (one_add_pow_dvd_of_odd_mul (e0 := 439) (by omega)),
   fun h => kill3_e443 hP E (one_add_pow_dvd_of_odd_mul (e0 := 443) (by omega)),
   fun h => kill3_e449 hP E (one_add_pow_dvd_of_odd_mul (e0 := 449) (by omega)),
   fun h => kill3_e452 hP E (one_add_pow_dvd_of_odd_mul (e0 := 452) (by omega)),
   fun h => kill3_e454 hP E (one_add_pow_dvd_of_odd_mul (e0 := 454) (by omega)),
   fun h => kill3_e457 hP E (one_add_pow_dvd_of_odd_mul (e0 := 457) (by omega)),
   fun h => kill3_e461 hP E (one_add_pow_dvd_of_odd_mul (e0 := 461) (by omega)),
   fun h => kill3_e463 hP E (one_add_pow_dvd_of_odd_mul (e0 := 463) (by omega)),
   fun h => kill3_e466 hP E (one_add_pow_dvd_of_odd_mul (e0 := 466) (by omega)),
   fun h => kill3_e467 hP E (one_add_pow_dvd_of_odd_mul (e0 := 467) (by omega)),
   fun h => kill3_e478 hP E (one_add_pow_dvd_of_odd_mul (e0 := 478) (by omega)),
   fun h => kill3_e479 hP E (one_add_pow_dvd_of_odd_mul (e0 := 479) (by omega)),
   fun h => kill3_e482 hP E (one_add_pow_dvd_of_odd_mul (e0 := 482) (by omega)),
   fun h => kill3_e491 hP E (one_add_pow_dvd_of_odd_mul (e0 := 491) (by omega))⟩

-- Pure arithmetic: the exponents in 201..500 that avoid all excluded classes.
theorem exponent_sieve_new (e : ℕ) (lo : 200 < e) (hi : e ≤ 500)
    (h0 : e % 12 ≠ 6 ∧
      e % 16 ≠ 8 ∧
      e % 18 ≠ 9 ∧
      e % 20 ≠ 10 ∧
      e % 24 ≠ 12 ∧
      e % 28 ≠ 14 ∧
      e % 30 ≠ 15 ∧
      e % 32 ≠ 16 ∧
      e % 34 ≠ 17 ∧
      e % 40 ≠ 20 ∧
      e % 42 ≠ 21 ∧
      e % 44 ≠ 22 ∧
      e % 46 ≠ 23 ∧
      e % 50 ≠ 25 ∧
      e % 52 ≠ 26 ∧
      e % 56 ≠ 28 ∧
      e % 58 ≠ 29 ∧
      e % 62 ≠ 31 ∧
      e % 64 ≠ 32 ∧
      e % 66 ≠ 33 ∧
      e % 68 ≠ 34 ∧
      e % 70 ≠ 35 ∧
      e % 74 ≠ 37 ∧
      e % 76 ≠ 38 ∧
      e % 78 ≠ 39 ∧
      e % 82 ≠ 41 ∧
      e % 86 ≠ 43 ∧
      e % 88 ≠ 44 ∧
      e % 92 ≠ 46 ∧
      e % 94 ≠ 47 ∧
      e % 98 ≠ 49 ∧
      e % 104 ≠ 52 ∧
      e % 106 ≠ 53 ∧
      e % 110 ≠ 55 ∧
      e % 114 ≠ 57 ∧
      e % 116 ≠ 58 ∧
      e % 118 ≠ 59 ∧
      e % 122 ≠ 61 ∧
      e % 124 ≠ 62 ∧
      e % 128 ≠ 64 ∧
      e % 130 ≠ 65 ∧
      e % 134 ≠ 67 ∧
      e % 136 ≠ 68 ∧
      e % 142 ≠ 71 ∧
      e % 146 ≠ 73 ∧
      e % 148 ≠ 74 ∧
      e % 152 ≠ 76 ∧
      e % 154 ≠ 77 ∧
      e % 158 ≠ 79 ∧
      e % 164 ≠ 82 ∧
      e % 166 ≠ 83 ∧
      e % 172 ≠ 86 ∧
      e % 178 ≠ 89 ∧
      e % 182 ≠ 91 ∧
      e % 184 ≠ 92 ∧
      e % 188 ≠ 94 ∧
      e % 190 ≠ 95 ∧
      e % 194 ≠ 97 ∧
      e % 202 ≠ 101 ∧
      e % 206 ≠ 103 ∧
      e % 212 ≠ 106 ∧
      e % 214 ≠ 107 ∧
      e % 218 ≠ 109 ∧
      e % 226 ≠ 113 ∧
      e % 232 ≠ 116 ∧
      e % 236 ≠ 118 ∧
      e % 242 ≠ 121 ∧
      e % 244 ≠ 122 ∧
      e % 248 ≠ 124 ∧
      e % 254 ≠ 127 ∧
      e % 256 ≠ 128 ∧
      e % 262 ≠ 131 ∧
      e % 266 ≠ 133 ∧
      e % 268 ≠ 134 ∧
      e % 274 ≠ 137 ∧
      e % 278 ≠ 139 ∧
      e % 284 ≠ 142 ∧
      e % 286 ≠ 143 ∧
      e % 292 ≠ 146 ∧
      e % 296 ≠ 148 ∧
      e % 298 ≠ 149 ∧
      e % 302 ≠ 151 ∧
      e % 314 ≠ 157 ∧
      e % 316 ≠ 158 ∧
      e % 326 ≠ 163 ∧
      e % 328 ≠ 164 ∧
      e % 332 ≠ 166 ∧
      e % 334 ≠ 167 ∧
      e % 338 ≠ 169 ∧
      e % 344 ≠ 172 ∧
      e % 346 ≠ 173 ∧
      e % 356 ≠ 178 ∧
      e % 358 ≠ 179 ∧
      e % 362 ≠ 181 ∧
      e % 376 ≠ 188 ∧
      e % 382 ≠ 191 ∧
      e % 386 ≠ 193 ∧
      e % 388 ≠ 194 ∧
      e % 394 ≠ 197 ∧
      e % 398 ≠ 199)
    (h1 : e % 404 ≠ 202 ∧
      e % 412 ≠ 206 ∧
      e % 418 ≠ 209 ∧
      e % 422 ≠ 211 ∧
      e % 424 ≠ 212 ∧
      e % 428 ≠ 214 ∧
      e % 436 ≠ 218 ∧
      e % 446 ≠ 223 ∧
      e % 452 ≠ 226 ∧
      e % 454 ≠ 227 ∧
      e % 458 ≠ 229 ∧
      e % 466 ≠ 233 ∧
      e % 472 ≠ 236 ∧
      e % 478 ≠ 239 ∧
      e % 482 ≠ 241 ∧
      e % 488 ≠ 244 ∧
      e % 494 ≠ 247 ∧
      e % 502 ≠ 251 ∧
      e % 508 ≠ 254 ∧
      e % 512 ≠ 256 ∧
      e % 514 ≠ 257 ∧
      e % 524 ≠ 262 ∧
      e % 526 ≠ 263 ∧
      e % 536 ≠ 268 ∧
      e % 538 ≠ 269 ∧
      e % 542 ≠ 271 ∧
      e % 548 ≠ 274 ∧
      e % 554 ≠ 277 ∧
      e % 556 ≠ 278 ∧
      e % 562 ≠ 281 ∧
      e % 566 ≠ 283 ∧
      e % 568 ≠ 284 ∧
      e % 584 ≠ 292 ∧
      e % 586 ≠ 293 ∧
      e % 596 ≠ 298 ∧
      e % 604 ≠ 302 ∧
      e % 614 ≠ 307 ∧
      e % 622 ≠ 311 ∧
      e % 626 ≠ 313 ∧
      e % 628 ≠ 314 ∧
      e % 632 ≠ 316 ∧
      e % 634 ≠ 317 ∧
      e % 652 ≠ 326 ∧
      e % 662 ≠ 331 ∧
      e % 664 ≠ 332 ∧
      e % 668 ≠ 334 ∧
      e % 674 ≠ 337 ∧
      e % 692 ≠ 346 ∧
      e % 694 ≠ 347 ∧
      e % 698 ≠ 349 ∧
      e % 706 ≠ 353 ∧
      e % 712 ≠ 356 ∧
      e % 716 ≠ 358 ∧
      e % 722 ≠ 361 ∧
      e % 734 ≠ 367 ∧
      e % 746 ≠ 373 ∧
      e % 758 ≠ 379 ∧
      e % 764 ≠ 382 ∧
      e % 766 ≠ 383 ∧
      e % 772 ≠ 386 ∧
      e % 776 ≠ 388 ∧
      e % 778 ≠ 389 ∧
      e % 788 ≠ 394 ∧
      e % 794 ≠ 397 ∧
      e % 796 ≠ 398 ∧
      e % 802 ≠ 401 ∧
      e % 808 ≠ 404 ∧
      e % 818 ≠ 409 ∧
      e % 824 ≠ 412 ∧
      e % 838 ≠ 419 ∧
      e % 842 ≠ 421 ∧
      e % 844 ≠ 422 ∧
      e % 856 ≠ 428 ∧
      e % 862 ≠ 431 ∧
      e % 866 ≠ 433 ∧
      e % 872 ≠ 436 ∧
      e % 878 ≠ 439 ∧
      e % 886 ≠ 443 ∧
      e % 898 ≠ 449 ∧
      e % 904 ≠ 452 ∧
      e % 908 ≠ 454 ∧
      e % 914 ≠ 457 ∧
      e % 922 ≠ 461 ∧
      e % 926 ≠ 463 ∧
      e % 932 ≠ 466 ∧
      e % 934 ≠ 467 ∧
      e % 956 ≠ 478 ∧
      e % 958 ≠ 479 ∧
      e % 964 ≠ 482 ∧
      e % 982 ≠ 491) :
    e = 359 ∨ e = 362 ∨ e = 446 ∨ e = 458 ∨ e = 487 ∨ e = 499 := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99⟩ := h0
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89⟩ := h1
  interval_cases e
  · exact absurd rfl r41
  · exact absurd rfl s0
  · exact absurd rfl r16
  · exact absurd rfl r4
  · exact absurd rfl r25
  · exact absurd rfl s1
  · exact absurd rfl r2
  · exact absurd rfl r7
  · exact absurd rfl s2
  · exact absurd rfl r0
  · exact absurd rfl s3
  · exact absurd rfl s4
  · exact absurd rfl r43
  · exact absurd rfl s5
  · exact absurd rfl r26
  · exact absurd rfl r1
  · exact absurd rfl r17
  · exact absurd rfl s6
  · exact absurd rfl r44
  · exact absurd rfl r9
  · exact absurd rfl r8
  · exact absurd rfl r0
  · exact absurd rfl s7
  · exact absurd rfl r18
  · exact absurd rfl r2
  · exact absurd rfl s8
  · exact absurd rfl s9
  · exact absurd rfl r4
  · exact absurd rfl s10
  · exact absurd rfl r3
  · exact absurd rfl r10
  · exact absurd rfl r1
  · exact absurd rfl s11
  · exact absurd rfl r0
  · exact absurd rfl r29
  · exact absurd rfl s12
  · exact absurd rfl r48
  · exact absurd rfl r5
  · exact absurd rfl s13
  · exact absurd rfl r7
  · exact absurd rfl s14
  · exact absurd rfl r11
  · exact absurd rfl r2
  · exact absurd rfl s15
  · exact absurd rfl r21
  · exact absurd rfl r0
  · exact absurd rfl s16
  · exact absurd rfl r1
  · exact absurd rfl r50
  · exact absurd rfl r3
  · exact absurd rfl s17
  · exact absurd rfl r4
  · exact absurd rfl r12
  · exact absurd rfl s18
  · exact absurd rfl r6
  · exact absurd rfl s19
  · exact absurd rfl s20
  · exact absurd rfl r0
  · exact absurd rfl r22
  · exact absurd rfl r9
  · exact absurd rfl r2
  · exact absurd rfl s21
  · exact absurd rfl s22
  · exact absurd rfl r1
  · exact absurd rfl r32
  · exact absurd rfl r5
  · exact absurd rfl r52
  · exact absurd rfl s23
  · exact absurd rfl s24
  · exact absurd rfl r0
  · exact absurd rfl s25
  · exact absurd rfl r7
  · exact absurd rfl r10
  · exact absurd rfl s26
  · exact absurd rfl r13
  · exact absurd rfl r4
  · exact absurd rfl s27
  · exact absurd rfl s28
  · exact absurd rfl r2
  · exact absurd rfl r1
  · exact absurd rfl s29
  · exact absurd rfl r0
  · exact absurd rfl s30
  · exact absurd rfl s31
  · exact absurd rfl r6
  · exact absurd rfl r11
  · exact absurd rfl r25
  · exact absurd rfl r18
  · exact absurd rfl r8
  · exact absurd rfl r3
  · exact absurd rfl r57
  · exact absurd rfl s32
  · exact absurd rfl s33
  · exact absurd rfl r0
  · exact absurd rfl r36
  · exact absurd rfl r1
  · exact absurd rfl r2
  · exact absurd rfl s34
  · exact absurd rfl r12
  · exact absurd rfl r4
  · exact absurd rfl r26
  · exact absurd rfl s35
  · exact absurd rfl r58
  · exact absurd rfl r7
  · exact absurd rfl r37
  · exact absurd rfl r0
  · exact absurd rfl s36
  · exact absurd rfl r15
  · exact absurd rfl r59
  · exact absurd rfl r3
  · exact absurd rfl s37
  · exact absurd rfl r1
  · exact absurd rfl s38
  · exact absurd rfl s39
  · exact absurd rfl r2
  · exact absurd rfl s40
  · exact absurd rfl s41
  · exact absurd rfl r0
  · exact absurd rfl r16
  · exact absurd rfl r39
  · exact absurd rfl r61
  · exact absurd rfl r5
  · exact absurd rfl r8
  · exact absurd rfl r4
  · exact absurd rfl r13
  · exact absurd rfl s42
  · exact absurd rfl r62
  · exact absurd rfl r1
  · exact absurd rfl r29
  · exact absurd rfl r0
  · exact absurd rfl s43
  · exact absurd rfl s44
  · exact absurd rfl r2
  · exact absurd rfl s45
  · exact absurd rfl r41
  · exact absurd rfl r7
  · exact absurd rfl s46
  · exact absurd rfl r14
  · exact absurd rfl r63
  · exact absurd rfl r9
  · exact absurd rfl r17
  · exact absurd rfl r0
  · exact absurd rfl r30
  · exact absurd rfl r1
  · exact absurd rfl r6
  · exact absurd rfl s47
  · exact absurd rfl s48
  · exact absurd rfl r4
  · exact absurd rfl s49
  · exact absurd rfl r3
  · exact absurd rfl r2
  · exact absurd rfl r18
  · exact absurd rfl s50
  · exact absurd rfl r0
  · exact absurd rfl r43
  · exact absurd rfl s51
  · exact absurd rfl r8
  · exact absurd rfl s52
  · omega
  · exact absurd rfl r1
  · exact absurd rfl s53
  · omega
  · exact absurd rfl r19
  · exact absurd rfl r15
  · exact absurd rfl r44
  · exact absurd rfl r0
  · exact absurd rfl s54
  · exact absurd rfl r7
  · exact absurd rfl r2
  · exact absurd rfl r3
  · exact absurd rfl r32
  · exact absurd rfl r4
  · exact absurd rfl s55
  · exact absurd rfl r11
  · exact absurd rfl r6
  · exact absurd rfl r1
  · exact absurd rfl r16
  · exact absurd rfl r0
  · exact absurd rfl s56
  · exact absurd rfl r9
  · exact absurd rfl r69
  · exact absurd rfl s57
  · exact absurd rfl s58
  · exact absurd rfl r70
  · exact absurd rfl r21
  · exact absurd rfl s59
  · exact absurd rfl r2
  · exact absurd rfl s60
  · exact absurd rfl s61
  · exact absurd rfl r0
  · exact absurd rfl r8
  · exact absurd rfl r1
  · exact absurd rfl r71
  · exact absurd rfl s62
  · exact absurd rfl r48
  · exact absurd rfl r4
  · exact absurd rfl s63
  · exact absurd rfl s64
  · exact absurd rfl r10
  · exact absurd rfl r7
  · exact absurd rfl s65
  · exact absurd rfl r0
  · exact absurd rfl r17
  · exact absurd rfl s66
  · exact absurd rfl r2
  · exact absurd rfl r5
  · exact absurd rfl r22
  · exact absurd rfl r1
  · exact absurd rfl s67
  · exact absurd rfl r3
  · exact absurd rfl r74
  · exact absurd rfl s68
  · exact absurd rfl r36
  · exact absurd rfl r0
  · exact absurd rfl r50
  · exact absurd rfl r18
  · exact absurd rfl r75
  · exact absurd rfl r11
  · exact absurd rfl s69
  · exact absurd rfl r4
  · exact absurd rfl s70
  · exact absurd rfl s71
  · exact absurd rfl r2
  · exact absurd rfl r1
  · exact absurd rfl r8
  · exact absurd rfl r0
  · exact absurd rfl r37
  · exact absurd rfl s72
  · exact absurd rfl r19
  · exact absurd rfl r3
  · exact absurd rfl s73
  · exact absurd rfl r7
  · exact absurd rfl s74
  · exact absurd rfl r5
  · exact absurd rfl r6
  · exact absurd rfl s75
  · exact absurd rfl r12
  · exact absurd rfl r0
  · exact absurd rfl s76
  · exact absurd rfl r1
  · exact absurd rfl r2
  · exact absurd rfl r14
  · exact absurd rfl s77
  · exact absurd rfl r4
  · exact absurd rfl r52
  · omega
  · exact absurd rfl r80
  · exact absurd rfl r39
  · exact absurd rfl s78
  · exact absurd rfl r0
  · exact absurd rfl r25
  · exact absurd rfl s79
  · exact absurd rfl r81
  · exact absurd rfl s80
  · exact absurd rfl r21
  · exact absurd rfl r1
  · exact absurd rfl s81
  · omega
  · exact absurd rfl r2
  · exact absurd rfl r9
  · exact absurd rfl s82
  · exact absurd rfl r0
  · exact absurd rfl s83
  · exact absurd rfl r7
  · exact absurd rfl r6
  · exact absurd rfl s84
  · exact absurd rfl s85
  · exact absurd rfl r4
  · exact absurd rfl r41
  · exact absurd rfl r3
  · exact absurd rfl r82
  · exact absurd rfl r1
  · exact absurd rfl r26
  · exact absurd rfl r0
  · exact absurd rfl r13
  · exact absurd rfl r15
  · exact absurd rfl r2
  · exact absurd rfl s86
  · exact absurd rfl s87
  · exact absurd rfl r18
  · exact absurd rfl r22
  · exact absurd rfl s88
  · exact absurd rfl r10
  · exact absurd rfl r27
  · exact absurd rfl r57
  · exact absurd rfl r0
  · omega
  · exact absurd rfl r1
  · exact absurd rfl r84
  · exact absurd rfl r3
  · exact absurd rfl s89
  · exact absurd rfl r4
  · exact absurd rfl r8
  · exact absurd rfl r14
  · exact absurd rfl r2
  · exact absurd rfl r7
  · exact absurd rfl r43
  · exact absurd rfl r0
  · omega
  · exact absurd rfl r9

-- Pure arithmetic: the classes of D100 and of the new values, in the set form of H1.
set_option maxRecDepth 100000 in
theorem odd_mul_three_new {e : ℕ}
    (h0 : e % 12 ≠ 6 ∧
      e % 16 ≠ 8 ∧
      e % 18 ≠ 9 ∧
      e % 20 ≠ 10 ∧
      e % 24 ≠ 12 ∧
      e % 28 ≠ 14 ∧
      e % 30 ≠ 15 ∧
      e % 32 ≠ 16 ∧
      e % 34 ≠ 17 ∧
      e % 40 ≠ 20 ∧
      e % 42 ≠ 21 ∧
      e % 44 ≠ 22 ∧
      e % 46 ≠ 23 ∧
      e % 50 ≠ 25 ∧
      e % 52 ≠ 26 ∧
      e % 56 ≠ 28 ∧
      e % 58 ≠ 29 ∧
      e % 62 ≠ 31 ∧
      e % 64 ≠ 32 ∧
      e % 66 ≠ 33 ∧
      e % 68 ≠ 34 ∧
      e % 70 ≠ 35 ∧
      e % 74 ≠ 37 ∧
      e % 76 ≠ 38 ∧
      e % 78 ≠ 39 ∧
      e % 82 ≠ 41 ∧
      e % 86 ≠ 43 ∧
      e % 88 ≠ 44 ∧
      e % 92 ≠ 46 ∧
      e % 94 ≠ 47 ∧
      e % 98 ≠ 49 ∧
      e % 104 ≠ 52 ∧
      e % 106 ≠ 53 ∧
      e % 110 ≠ 55 ∧
      e % 114 ≠ 57 ∧
      e % 116 ≠ 58 ∧
      e % 118 ≠ 59 ∧
      e % 122 ≠ 61 ∧
      e % 124 ≠ 62 ∧
      e % 128 ≠ 64 ∧
      e % 130 ≠ 65 ∧
      e % 134 ≠ 67 ∧
      e % 136 ≠ 68 ∧
      e % 142 ≠ 71 ∧
      e % 146 ≠ 73 ∧
      e % 148 ≠ 74 ∧
      e % 152 ≠ 76 ∧
      e % 154 ≠ 77 ∧
      e % 158 ≠ 79 ∧
      e % 164 ≠ 82 ∧
      e % 166 ≠ 83 ∧
      e % 172 ≠ 86 ∧
      e % 178 ≠ 89 ∧
      e % 182 ≠ 91 ∧
      e % 184 ≠ 92 ∧
      e % 188 ≠ 94 ∧
      e % 190 ≠ 95 ∧
      e % 194 ≠ 97 ∧
      e % 202 ≠ 101 ∧
      e % 206 ≠ 103 ∧
      e % 212 ≠ 106 ∧
      e % 214 ≠ 107 ∧
      e % 218 ≠ 109 ∧
      e % 226 ≠ 113 ∧
      e % 232 ≠ 116 ∧
      e % 236 ≠ 118 ∧
      e % 242 ≠ 121 ∧
      e % 244 ≠ 122 ∧
      e % 248 ≠ 124 ∧
      e % 254 ≠ 127 ∧
      e % 256 ≠ 128 ∧
      e % 262 ≠ 131 ∧
      e % 266 ≠ 133 ∧
      e % 268 ≠ 134 ∧
      e % 274 ≠ 137 ∧
      e % 278 ≠ 139 ∧
      e % 284 ≠ 142 ∧
      e % 286 ≠ 143 ∧
      e % 292 ≠ 146 ∧
      e % 296 ≠ 148 ∧
      e % 298 ≠ 149 ∧
      e % 302 ≠ 151 ∧
      e % 314 ≠ 157 ∧
      e % 316 ≠ 158 ∧
      e % 326 ≠ 163 ∧
      e % 328 ≠ 164 ∧
      e % 332 ≠ 166 ∧
      e % 334 ≠ 167 ∧
      e % 338 ≠ 169 ∧
      e % 344 ≠ 172 ∧
      e % 346 ≠ 173 ∧
      e % 356 ≠ 178 ∧
      e % 358 ≠ 179 ∧
      e % 362 ≠ 181 ∧
      e % 376 ≠ 188 ∧
      e % 382 ≠ 191 ∧
      e % 386 ≠ 193 ∧
      e % 388 ≠ 194 ∧
      e % 394 ≠ 197 ∧
      e % 398 ≠ 199)
    (h1 : e % 404 ≠ 202 ∧
      e % 412 ≠ 206 ∧
      e % 418 ≠ 209 ∧
      e % 422 ≠ 211 ∧
      e % 424 ≠ 212 ∧
      e % 428 ≠ 214 ∧
      e % 436 ≠ 218 ∧
      e % 446 ≠ 223 ∧
      e % 452 ≠ 226 ∧
      e % 454 ≠ 227 ∧
      e % 458 ≠ 229 ∧
      e % 466 ≠ 233 ∧
      e % 472 ≠ 236 ∧
      e % 478 ≠ 239 ∧
      e % 482 ≠ 241 ∧
      e % 488 ≠ 244 ∧
      e % 494 ≠ 247 ∧
      e % 502 ≠ 251 ∧
      e % 508 ≠ 254 ∧
      e % 512 ≠ 256 ∧
      e % 514 ≠ 257 ∧
      e % 524 ≠ 262 ∧
      e % 526 ≠ 263 ∧
      e % 536 ≠ 268 ∧
      e % 538 ≠ 269 ∧
      e % 542 ≠ 271 ∧
      e % 548 ≠ 274 ∧
      e % 554 ≠ 277 ∧
      e % 556 ≠ 278 ∧
      e % 562 ≠ 281 ∧
      e % 566 ≠ 283 ∧
      e % 568 ≠ 284 ∧
      e % 584 ≠ 292 ∧
      e % 586 ≠ 293 ∧
      e % 596 ≠ 298 ∧
      e % 604 ≠ 302 ∧
      e % 614 ≠ 307 ∧
      e % 622 ≠ 311 ∧
      e % 626 ≠ 313 ∧
      e % 628 ≠ 314 ∧
      e % 632 ≠ 316 ∧
      e % 634 ≠ 317 ∧
      e % 652 ≠ 326 ∧
      e % 662 ≠ 331 ∧
      e % 664 ≠ 332 ∧
      e % 668 ≠ 334 ∧
      e % 674 ≠ 337 ∧
      e % 692 ≠ 346 ∧
      e % 694 ≠ 347 ∧
      e % 698 ≠ 349 ∧
      e % 706 ≠ 353 ∧
      e % 712 ≠ 356 ∧
      e % 716 ≠ 358 ∧
      e % 722 ≠ 361 ∧
      e % 734 ≠ 367 ∧
      e % 746 ≠ 373 ∧
      e % 758 ≠ 379 ∧
      e % 764 ≠ 382 ∧
      e % 766 ≠ 383 ∧
      e % 772 ≠ 386 ∧
      e % 776 ≠ 388 ∧
      e % 778 ≠ 389 ∧
      e % 788 ≠ 394 ∧
      e % 794 ≠ 397 ∧
      e % 796 ≠ 398 ∧
      e % 802 ≠ 401 ∧
      e % 808 ≠ 404 ∧
      e % 818 ≠ 409 ∧
      e % 824 ≠ 412 ∧
      e % 838 ≠ 419 ∧
      e % 842 ≠ 421 ∧
      e % 844 ≠ 422 ∧
      e % 856 ≠ 428 ∧
      e % 862 ≠ 431 ∧
      e % 866 ≠ 433 ∧
      e % 872 ≠ 436 ∧
      e % 878 ≠ 439 ∧
      e % 886 ≠ 443 ∧
      e % 898 ≠ 449 ∧
      e % 904 ≠ 452 ∧
      e % 908 ≠ 454 ∧
      e % 914 ≠ 457 ∧
      e % 922 ≠ 461 ∧
      e % 926 ≠ 463 ∧
      e % 932 ≠ 466 ∧
      e % 934 ≠ 467 ∧
      e % 956 ≠ 478 ∧
      e % 958 ≠ 479 ∧
      e % 964 ≠ 482 ∧
      e % 982 ≠ 491) :
    ∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37, 38,
      39, 41, 43, 44, 46, 47, 49, 52, 53, 55, 57, 58, 59, 61, 62, 64, 65, 67, 68, 71, 73, 74,
      76, 77, 79, 82, 83, 86, 89, 91, 92, 94, 95, 97, 101, 103, 106, 107, 109, 113, 116, 118,
      121, 122, 124, 127, 128, 131, 133, 134, 137, 139, 142, 143, 146, 148, 149, 151, 157, 158,
      163, 164, 166, 167, 169, 172, 173, 178, 179, 181, 188, 191, 193, 194, 197, 199, 202, 206,
      209, 211, 212, 214, 218, 223, 226, 227, 229, 233, 236, 239, 241, 244, 247, 251, 254, 256,
      257, 262, 263, 268, 269, 271, 274, 277, 278, 281, 283, 284, 292, 293, 298, 302, 307, 311,
      313, 314, 316, 317, 326, 331, 332, 334, 337, 346, 347, 349, 353, 356, 358, 361, 367, 373,
      379, 382, 383, 386, 388, 389, 394, 397, 398, 401, 404, 409, 412, 419, 421, 422, 428, 431,
      433, 436, 439, 443, 449, 452, 454, 457, 461, 463, 466, 467, 478, 479, 482, 491} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99⟩ := h0
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89⟩ := h1
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff hbig _ hG => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have he2 : 2 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).mp h3sq.2.2
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have r0 := three_exponent_residues_200 h h3n hs
  have r1 := core3_residues_new hP E
  rcases Nat.lt_or_ge 500 (n.factorization 3) with hb | hle
  · exact (h1 n h hiff hb (odd_mul_three_new r0 r1) hG).trans (le_max_left _ _)
  · exact (h2 n h hiff (exponent_sieve_new _ hbig hle r0 r1) hG).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1
