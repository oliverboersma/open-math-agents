import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H2.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H2.R1.lean
-- Credit: @adammcarter (agent: Claude Code, model claude-fable-5-2)
--
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1 (3 is the only repeated odd prime
-- of the unitary perfect number n and its exponent is 13) by the power of 2 dividing a, after
-- proving new restrictions on a.  Proving H1, ..., H3 proves the step.
--
-- Notation as in the parent files: e = n.factorization 3 = 13, a = padicValNat 2 n, P = the set of
-- simple odd primes of n.  A number x is an ODD MULTIPLE of d when x mod 2d = d; if a is one then
-- 2^d + 1 divides 2^a + 1.  The balance equation is
--   (2^a + 1)(1 + 3^13) prod_P (p + 1) = 2^(a+1) 3^13 prod_P p,
-- in which every odd prime other than 3 occurs exactly once on the left, 3 occurs exactly 13 times
-- and 2 exactly a + 1 times.  Here 1 + 3^13 = 4 * 398581, so
-- 398581 is a simple prime of n, and so are 17, 19, 617 (398582 = 2 * 17 * 19 * 617), 103 (618 = 6
-- * 103), 13 (104 = 8 * 13), 7 (14 = 2 * 7), 5 (20 = 4 * 5).
--
-- PROVED BELOW (no hypothesis needed):
--  * sieve: a is no odd multiple of any d from 1 to 400 except d in {1, 3, 5, 7, 8, 269, 353, 383}.
--    55 new lemmas k_d<d> (the other d are odd multiples of a d excluded by a parent file):
--    a prime factor of 2^d + 1 is a simple prime of n, the odd primes of p + 1 for simple p are
--    simple again, and the chain ends at a prime with two sources on the left (37 cases), at a
--    square (18 cases).  The 2^d + 1 are fully factored where needed; primes above
--    4.3 * 10^7 carry a Lucas certificate (theorems prime_<p>, 99 of them, up to 104 digits).
--  * fermat: a is no odd multiple of 2^k for k = 9, ..., 19 (known factors of the Fermat numbers
--    F9, ..., F19); with the sieve at 128 and 256 and the parent's cases 2, 4, 8, 16, 32, 64 this
--    leaves a odd, a = 8 mod 16, or 2^20 dividing a.
--  * lower: a >= 262 (count of the factors of 2, then the sieve).
--  * odd_count: for a odd, at most 8 primes p = 2 mod 3 divide a (count of the factors of 3: each
--    such p gives its own prime q = 2 mod 3 dividing 2^p + 1, and 3 divides q + 1).
-- So: for a odd, every prime factor of a is 3 or larger than 400 or one of the exceptions; in the
-- even classes the odd prime factors of a are large as well (a no odd multiple of 2^i * q).
--
-- H1 (OPEN): a is odd.
-- H2 (OPEN): a is 8 mod 16.
-- H3 (OPEN): 2^20 divides a.  No factor of the Fermat number F20 is known, so this class cannot
--   be sieved in the same way.
-- No known unitary perfect number satisfies the hypotheses of any H.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1 hiding H1 H2 H3 main

-- H1: a is bounded when a is odd, with the restrictions proved below.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 13 →
    padicValNat 2 n % 2 = 1 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    (((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 8) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when a is 8 mod 16, that is 8 times an odd number, with the restrictions proved below.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 13 →
    padicValNat 2 n % 16 = 8 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: a is bounded when 2^20 divides a (the sieve says nothing about this class).
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 13 →
    padicValNat 2 n % 1048576 = 0 →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates, the forced-chain lemmas, the sieve and the Fermat levels.

theorem prime_715827883 : Nat.Prime 715827883 := by
  refine lucas_primality 715827883 (5 : ZMod 715827883) ?_ (fun q hq hd => ?_)
  · rw [show 715827883 - 1 = 715827882 from by norm_num]
    reduce_mod_char
  · have e : 715827883 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 31 ^ 1, 151 ^ 1, 331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 2 = 357913941 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 357913941 = ((715827882 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 3 = 238609294 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 238609294 = ((151888732 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 7 = 102261126 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 102261126 = ((131416656 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 11 = 65075262 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 65075262 = ((423957234 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 31 = 23091222 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 23091222 = ((4096 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 151 = 4740582 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 4740582 = ((451339760 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 331 = 2162622 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 2162622 = ((446444286 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4278255361 : Nat.Prime 4278255361 := by
  refine lucas_primality 4278255361 (23 : ZMod 4278255361) ?_ (fun q hq hd => ?_)
  · rw [show 4278255361 - 1 = 4278255360 from by norm_num]
    reduce_mod_char
  · have e : 4278255361 - 1 = [2 ^ 8, 3 ^ 1, 5 ^ 1, 17 ^ 1, 65537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 2 = 2139127680 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 2139127680 = ((4278255360 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 3 = 1426085120 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 1426085120 = ((265752886 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 5 = 855651072 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 855651072 = ((65536 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 17 = 251662080 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 251662080 = ((2887654611 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 65537 = 65280 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 65280 = ((1936053211 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2139127681 : Nat.Prime 2139127681 := by
  refine lucas_primality 2139127681 (14 : ZMod 2139127681) ?_ (fun q hq hd => ?_)
  · rw [show 2139127681 - 1 = 2139127680 from by norm_num]
    reduce_mod_char
  · have e : 2139127681 - 1 = [2 ^ 7, 3 ^ 1, 5 ^ 1, 17 ^ 1, 65537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 2 = 1069563840 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 1069563840 = ((2139127680 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 3 = 713042560 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 713042560 = ((1280083319 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 5 = 427825536 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 427825536 = ((1177214020 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 17 = 125831040 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 125831040 = ((1566319278 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 65537 = 32640 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 32640 = ((574960972 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2932031007403 : Nat.Prime 2932031007403 := by
  refine lucas_primality 2932031007403 (3 : ZMod 2932031007403) ?_ (fun q hq hd => ?_)
  · rw [show 2932031007403 - 1 = 2932031007402 from by norm_num]
    reduce_mod_char
  · have e : 2932031007403 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 2, 43 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 2 = 1466015503701 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 1466015503701 = ((2932031007402 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 3 = 977343669134 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 977343669134 = ((1616581872411 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 7 = 418861572486 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 418861572486 = ((622869028911 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 43 = 68186767614 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 68186767614 = ((2931494136491 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 127 = 23086858326 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 23086858326 = ((1610672779439 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 337 = 8700388746 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 8700388746 = ((1777987394008 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 5419 = 541064958 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 541064958 = ((2145654789947 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_165768537521 : Nat.Prime 165768537521 := by
  refine lucas_primality 165768537521 (3 : ZMod 165768537521) ?_ (fun q hq hd => ?_)
  · rw [show 165768537521 - 1 = 165768537520 from by norm_num]
    reduce_mod_char
  · have e : 165768537521 - 1 = [2 ^ 4, 5 ^ 1, 47 ^ 1, 2887 ^ 1, 15271 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 2 = 82884268760 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 82884268760 = ((165768537520 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 5 = 33153707504 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 33153707504 = ((68616265392 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 47 = 3526990160 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 3526990160 = ((165734983089 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 2887 = 57418960 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 57418960 = ((6910349427 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 15271 = 10855120 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 10855120 = ((78255376458 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4363953127297 : Nat.Prime 4363953127297 := by
  refine lucas_primality 4363953127297 (5 : ZMod 4363953127297) ?_ (fun q hq hd => ?_)
  · rw [show 4363953127297 - 1 = 4363953127296 from by norm_num]
    reduce_mod_char
  · have e : 4363953127297 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 2, 127 ^ 1, 337 ^ 1, 5419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 2 = 2181976563648 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 2181976563648 = ((4363953127296 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 3 = 1454651042432 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 1454651042432 = ((3735730723197 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 7 = 623421875328 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 623421875328 = ((4329593388929 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 127 = 34361835648 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 34361835648 = ((741582913463 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 337 = 12949415808 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 12949415808 = ((551396850060 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 5419 = 805305984 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 805305984 = ((603965658536 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67254877 : Nat.Prime 67254877 := by
  refine lucas_primality 67254877 (2 : ZMod 67254877) ?_ (fun q hq hd => ?_)
  · rw [show 67254877 - 1 = 67254876 from by norm_num]
    reduce_mod_char
  · have e : 67254877 - 1 = [2 ^ 2, 3 ^ 2, 13 ^ 1, 131 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 2 = 33627438 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 33627438 = ((67254876 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 3 = 22418292 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 22418292 = ((32183595 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 13 = 5173452 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 5173452 = ((19873645 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 131 = 513396 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 513396 = ((18959693 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 1097 = 61308 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 61308 = ((36918246 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28059810762433 : Nat.Prime 28059810762433 := by
  refine lucas_primality 28059810762433 (5 : ZMod 28059810762433) ?_ (fun q hq hd => ?_)
  · rw [show 28059810762433 - 1 = 28059810762432 from by norm_num]
    reduce_mod_char
  · have e : 28059810762433 - 1 = [2 ^ 6, 3 ^ 1, 41 ^ 1, 53 ^ 1, 67254877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 2 = 14029905381216 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 14029905381216 = ((28059810762432 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 3 = 9353270254144 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 9353270254144 = ((25962592041197 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 41 = 684385628352 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 684385628352 = ((2428815610770 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 53 = 529430391744 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 529430391744 = ((28059810762305 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_67254877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 67254877 = 417216 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 417216 = ((27349741008203 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1275445943747 : Nat.Prime 1275445943747 := by
  refine lucas_primality 1275445943747 (2 : ZMod 1275445943747) ?_ (fun q hq hd => ?_)
  · rw [show 1275445943747 - 1 = 1275445943746 from by norm_num]
    reduce_mod_char
  · have e : 1275445943747 - 1 = [2 ^ 1, 13 ^ 1, 227 ^ 1, 12239 ^ 1, 17657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 2 = 637722971873 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 637722971873 = ((1275445943746 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 13 = 98111226442 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 98111226442 = ((315239952175 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 227 = 5618704598 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 5618704598 = ((537351048113 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 12239 = 104211614 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 104211614 = ((804237427832 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 17657 = 72234578 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 72234578 = ((1261028853167 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_768614336404564651 : Nat.Prime 768614336404564651 := by
  refine lucas_primality 768614336404564651 (3 : ZMod 768614336404564651) ?_ (fun q hq hd => ?_)
  · rw [show 768614336404564651 - 1 = 768614336404564650 from by norm_num]
    reduce_mod_char
  · have e : 768614336404564651 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 7 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 41 ^ 1, 61 ^ 1, 151 ^ 1, 331 ^ 1, 1321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 2 = 384307168202282325 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 384307168202282325 = ((768614336404564650 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 3 = 256204778801521550 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 256204778801521550 = ((243065045915817725 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 5 = 153722867280912930 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 153722867280912930 = ((754529885435533861 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 7 = 109802048057794950 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 109802048057794950 = ((3782361620868430 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 11 = 69874030582233150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 69874030582233150 = ((258177292182522579 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 13 = 59124179723428050 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 59124179723428050 = ((89030510150922805 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 31 = 24794010851760150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 24794010851760150 = ((478446363355159889 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 41 = 18746691131818650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 18746691131818650 = ((16212047901619696 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 61 = 12600235023025650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 12600235023025650 = ((759607137149823659 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 151 = 5090161168242150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 5090161168242150 = ((273041510166617890 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 331 = 2322097693065150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 2322097693065150 = ((106391769181428972 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 1321 = 581842798186650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 581842798186650 = ((348054768387184126 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56409643 : Nat.Prime 56409643 := by
  refine lucas_primality 56409643 (3 : ZMod 56409643) ?_ (fun q hq hd => ?_)
  · rw [show 56409643 - 1 = 56409642 from by norm_num]
    reduce_mod_char
  · have e : 56409643 - 1 = [2 ^ 1, 3 ^ 3, 71 ^ 1, 14713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 2 = 28204821 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 28204821 = ((56409642 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 3 = 18803214 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 18803214 = ((39676424 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 71 = 794502 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 794502 = ((53765441 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 14713 = 3834 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 3834 = ((53217898 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_201487636602438195784363 : Nat.Prime 201487636602438195784363 := by
  refine lucas_primality 201487636602438195784363 (3 : ZMod 201487636602438195784363) ?_ (fun q hq hd => ?_)
  · rw [show 201487636602438195784363 - 1 = 201487636602438195784362 from by norm_num]
    reduce_mod_char
  · have e : 201487636602438195784363 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 79 ^ 1, 2731 ^ 1, 8191 ^ 1, 121369 ^ 1, 22366891 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 2 = 100743818301219097892181 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 100743818301219097892181 = ((201487636602438195784362 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 3 = 67162545534146065261454 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 67162545534146065261454 = ((174764665359156168207072 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 7 = 28783948086062599397766 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 28783948086062599397766 = ((29273057550190743161093 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 79 = 2550476412689091085878 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 2550476412689091085878 = ((201487636602438195783851 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 2731 = 73777970194960891902 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 73777970194960891902 = ((201259714364220629927590 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 8191 = 24598661531246269782 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 24598661531246269782 = ((14751952106037037567816 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 121369 = 1660124385983555898 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 1660124385983555898 = ((34935602779351748259168 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 22366891 = 9008298766352382 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 9008298766352382 = ((59199625598676820678420 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_845100400152152934331135470251 : Nat.Prime 845100400152152934331135470251 := by
  refine lucas_primality 845100400152152934331135470251 (6 : ZMod 845100400152152934331135470251) ?_ (fun q hq hd => ?_)
  · rw [show 845100400152152934331135470251 - 1 = 845100400152152934331135470250 from by norm_num]
    reduce_mod_char
  · have e : 845100400152152934331135470251 - 1 = [2 ^ 1, 5 ^ 3, 11 ^ 1, 31 ^ 1, 41 ^ 1, 101 ^ 1, 251 ^ 1, 601 ^ 1, 1801 ^ 1, 4051 ^ 1, 8101 ^ 1, 268501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 2 = 422550200076076467165567735125 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 422550200076076467165567735125 = ((845100400152152934331135470250 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 5 = 169020080030430586866227094050 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 169020080030430586866227094050 = ((262235513280179507202218746463 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 11 = 76827309104741175848285042750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 76827309104741175848285042750 = ((643575463884633856536890059931 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 31 = 27261303230714610784875337750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 27261303230714610784875337750 = ((397238571030998904916109490708 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 41 = 20612204881759827666613060250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 20612204881759827666613060250 = ((378774382257504293065163714098 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 101 = 8367330694575771627040945250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 8367330694575771627040945250 = ((845100400152152934331101915819 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 251 = 3366933865148019658689782750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 3366933865148019658689782750 = ((486017372309480382572060270590 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 601 = 1406157071800587245143320250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 1406157071800587245143320250 = ((329185655697627947999692254908 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 1801 = 469239533676931112899020250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 469239533676931112899020250 = ((146795240610035330108268443054 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 4051 = 208615255530030346662832750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 208615255530030346662832750 = ((301830993492707295756446867204 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 8101 = 104320503660307731678945250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 104320503660307731678945250 = ((645687928776479073429150328768 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 268501 = 3147475801401681685845250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 3147475801401681685845250 = ((592269414167863919831068676721 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19616871237013 : Nat.Prime 19616871237013 := by
  refine lucas_primality 19616871237013 (2 : ZMod 19616871237013) ?_ (fun q hq hd => ?_)
  · rw [show 19616871237013 - 1 = 19616871237012 from by norm_num]
    reduce_mod_char
  · have e : 19616871237013 - 1 = [2 ^ 2, 3 ^ 3, 7 ^ 1, 1217 ^ 1, 21321481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 2 = 9808435618506 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 9808435618506 = ((19616871237012 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 3 = 6538957079004 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 6538957079004 = ((14694400646156 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 7 = 2802410176716 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 2802410176716 = ((16893456537515 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 1217 = 16119039636 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 16119039636 = ((13250485890143 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 21321481 = 920052 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 920052 = ((3801259099541 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8142767081771726171 : Nat.Prime 8142767081771726171 := by
  refine lucas_primality 8142767081771726171 (6 : ZMod 8142767081771726171) ?_ (fun q hq hd => ?_)
  · rw [show 8142767081771726171 - 1 = 8142767081771726170 from by norm_num]
    reduce_mod_char
  · have e : 8142767081771726171 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 31 ^ 1, 103 ^ 1, 19616871237013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 2 = 4071383540885863085 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 4071383540885863085 = ((8142767081771726170 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 5 = 1628553416354345234 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 1628553416354345234 = ((1161840165056618686 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 13 = 626366698597825090 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 626366698597825090 = ((356824796340725650 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 31 = 262669905863604070 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 262669905863604070 = ((6182947312878445319 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 103 = 79055991085162390 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 79055991085162390 = ((64 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_19616871237013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 19616871237013 = 415090 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 415090 = ((874678119364056690 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_78919881726271091143763623681 : Nat.Prime 78919881726271091143763623681 := by
  refine lucas_primality 78919881726271091143763623681 (47 : ZMod 78919881726271091143763623681) ?_ (fun q hq hd => ?_)
  · rw [show 78919881726271091143763623681 - 1 = 78919881726271091143763623680 from by norm_num]
    reduce_mod_char
  · have e : 78919881726271091143763623681 - 1 = [2 ^ 8, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 2 = 39459940863135545571881811840 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 39459940863135545571881811840 = ((78919881726271091143763623680 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 3 = 26306627242090363714587874560 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 26306627242090363714587874560 = ((8214642464917845850339246354 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 5 = 15783976345254218228752724736 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 15783976345254218228752724736 = ((31854139748206241317368478197 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 7 = 11274268818038727306251946240 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 11274268818038727306251946240 = ((21302793566101981363153694503 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 13 = 6070760132790083934135663360 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 6070760132790083934135663360 = ((78919881726271090044251995905 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 17 = 4642345983898299479044919040 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 4642345983898299479044919040 = ((39535619060177055188489950195 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 97 = 813607028105887537564573440 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 813607028105887537564573440 = ((51697113434694986693332778386 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 193 = 408911304281197363439189760 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 408911304281197363439189760 = ((48743744806705915190953386915 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 241 = 327468388905689174870388480 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 327468388905689174870388480 = ((76946074205182011108173878933 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 673 = 117265797513032824879292160 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 117265797513032824879292160 = ((39595816621489989450750861552 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 65537 = 1204203453412134994640640 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 1204203453412134994640640 = ((62084221376730397287934025095 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 22253377 = 3546422717157539331840 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 3546422717157539331840 = ((28547152273361814519905640550 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_39459940863135545571881811841 : Nat.Prime 39459940863135545571881811841 := by
  refine lucas_primality 39459940863135545571881811841 (23 : ZMod 39459940863135545571881811841) ?_ (fun q hq hd => ?_)
  · rw [show 39459940863135545571881811841 - 1 = 39459940863135545571881811840 from by norm_num]
    reduce_mod_char
  · have e : 39459940863135545571881811841 - 1 = [2 ^ 7, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 2 = 19729970431567772785940905920 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 19729970431567772785940905920 = ((39459940863135545571881811840 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 3 = 13153313621045181857293937280 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 13153313621045181857293937280 = ((39217345858976652508074178636 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 5 = 7891988172627109114376362368 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 7891988172627109114376362368 = ((20380168119287385906301143989 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 7 = 5637134409019363653125973120 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 5637134409019363653125973120 = ((13380944174232866041095229720 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 13 = 3035380066395041967067831680 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 3035380066395041967067831680 = ((24745956665057359303134273624 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 17 = 2321172991949149739522459520 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 2321172991949149739522459520 = ((9184356594572997438725056611 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 97 = 406803514052943768782286720 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 406803514052943768782286720 = ((4114705258024739740005425002 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 193 = 204455652140598681719594880 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 204455652140598681719594880 = ((15666056825064694354548227679 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 241 = 163734194452844587435194240 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 163734194452844587435194240 = ((14089849546075145621943352980 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 673 = 58632898756516412439646080 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 58632898756516412439646080 = ((8813390274325502539643483010 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 65537 = 602101726706067497320320 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 602101726706067497320320 = ((7728550258037527879866018562 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 22253377 = 1773211358578769665920 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 1773211358578769665920 = ((2059565084969888498130179539 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19729970431567772785940905921 : Nat.Prime 19729970431567772785940905921 := by
  refine lucas_primality 19729970431567772785940905921 (22 : ZMod 19729970431567772785940905921) ?_ (fun q hq hd => ?_)
  · rw [show 19729970431567772785940905921 - 1 = 19729970431567772785940905920 from by norm_num]
    reduce_mod_char
  · have e : 19729970431567772785940905921 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 2 = 9864985215783886392970452960 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 9864985215783886392970452960 = ((19729970431567772785940905920 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 3 = 6576656810522590928646968640 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 6576656810522590928646968640 = ((9622386831297383732792173527 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 5 = 3945994086313554557188181184 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 3945994086313554557188181184 = ((6913475373460510520722007056 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 7 = 2818567204509681826562986560 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 2818567204509681826562986560 = ((14292593964574779767895659196 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 13 = 1517690033197520983533915840 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 1517690033197520983533915840 = ((9431147359863237225918603695 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 17 = 1160586495974574869761229760 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 1160586495974574869761229760 = ((15914327967838321037169770649 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 97 = 203401757026471884391143360 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 203401757026471884391143360 = ((15619466099747315215999803101 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 193 = 102227826070299340859797440 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 102227826070299340859797440 = ((17324429200036549644466141513 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 241 = 81867097226422293717597120 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 81867097226422293717597120 = ((2285300649970218387238211418 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 673 = 29316449378258206219823040 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 29316449378258206219823040 = ((15657842976115509111525984398 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 65537 = 301050863353033748660160 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 301050863353033748660160 = ((18678769332342394453315266862 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 22253377 = 886605679289384832960 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 886605679289384832960 = ((5159055463131104032371628220 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9864985215783886392970452961 : Nat.Prime 9864985215783886392970452961 := by
  refine lucas_primality 9864985215783886392970452961 (22 : ZMod 9864985215783886392970452961) ?_ (fun q hq hd => ?_)
  · rw [show 9864985215783886392970452961 - 1 = 9864985215783886392970452960 from by norm_num]
    reduce_mod_char
  · have e : 9864985215783886392970452961 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 2 = 4932492607891943196485226480 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 4932492607891943196485226480 = ((9864985215783886392970452960 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 3 = 3288328405261295464323484320 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 3288328405261295464323484320 = ((1370950800923509901867947876 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 5 = 1972997043156777278594090592 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 1972997043156777278594090592 = ((2306205942038158337588354256 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 7 = 1409283602254840913281493280 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 1409283602254840913281493280 = ((6694988963205026561048928318 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 13 = 758845016598760491766957920 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 758845016598760491766957920 = ((189032893469805174127725152 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 17 = 580293247987287434880614880 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 580293247987287434880614880 = ((534236587989126161303339127 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 97 = 101700878513235942195571680 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 101700878513235942195571680 = ((9465594342738468873431350388 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 193 = 51113913035149670429898720 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 51113913035149670429898720 = ((9596057805721895791066337269 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 241 = 40933548613211146858798560 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 40933548613211146858798560 = ((8621503188500762433696094400 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 673 = 14658224689129103109911520 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 14658224689129103109911520 = ((2426402769772901353903747413 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 65537 = 150525431676516874330080 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 150525431676516874330080 = ((9630190872468189644976636103 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 22253377 = 443302839644692416480 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 443302839644692416480 = ((6963457736354780959136908660 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_104124649 : Nat.Prime 104124649 := by
  refine lucas_primality 104124649 (7 : ZMod 104124649) ?_ (fun q hq hd => ?_)
  · rw [show 104124649 - 1 = 104124648 from by norm_num]
    reduce_mod_char
  · have e : 104124649 - 1 = [2 ^ 3, 3 ^ 1, 53 ^ 1, 109 ^ 1, 751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 2 = 52062324 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 52062324 = ((104124648 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 3 = 34708216 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 34708216 = ((94708873 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 53 = 1964616 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 1964616 = ((85293978 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 109 = 955272 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 955272 = ((1024 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 751 = 138648 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 138648 = ((57914564 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_77158673929 : Nat.Prime 77158673929 := by
  refine lucas_primality 77158673929 (11 : ZMod 77158673929) ?_ (fun q hq hd => ?_)
  · rw [show 77158673929 - 1 = 77158673928 from by norm_num]
    reduce_mod_char
  · have e : 77158673929 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 73 ^ 1, 699053 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 2 = 38579336964 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 38579336964 = ((77158673928 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 3 = 25719557976 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 25719557976 = ((2097151 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 7 = 11022667704 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 11022667704 = ((8589930496 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 73 = 1056968136 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 1056968136 = ((73884964140 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 699053 = 110376 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 110376 = ((43682531219 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56713727820156410577229101238628035243 : Nat.Prime 56713727820156410577229101238628035243 := by
  refine lucas_primality 56713727820156410577229101238628035243 (3 : ZMod 56713727820156410577229101238628035243) ?_ (fun q hq hd => ?_)
  · rw [show 56713727820156410577229101238628035243 - 1 = 56713727820156410577229101238628035242 from by norm_num]
    reduce_mod_char
  · have e : 56713727820156410577229101238628035243 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 2, 19 ^ 1, 43 ^ 1, 73 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1, 92737 ^ 1, 649657 ^ 1, 77158673929 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 2 = 28356863910078205288614550619314017621 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 28356863910078205288614550619314017621 = ((56713727820156410577229101238628035242 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 3 = 18904575940052136859076367079542678414 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 18904575940052136859076367079542678414 = ((13898838222708156118891936879880683890 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 7 = 8101961117165201511032728748375433606 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 8101961117165201511032728748375433606 = ((22413134788282663057132454040641006030 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 19 = 2984933043166126872485742170454107118 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 2984933043166126872485742170454107118 = ((21686871186406268342679139743340261140 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 43 = 1318923902794335129703002354386698494 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 1318923902794335129703002354386698494 = ((48481389567981860097400250027525513468 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 73 = 776900381098033021605878099159288154 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 776900381098033021605878099159288154 = ((54360113558161921598803107142848346327 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 127 = 446564785985483547852197647548252246 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 446564785985483547852197647548252246 = ((1024 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 337 = 168289993531621396371599706939549066 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 168289993531621396371599706939549066 = ((16262741045374821133307621766389701814 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 5419 = 10465718365040858198418361549848318 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 10465718365040858198418361549848318 = ((47545762000174170391976693409797500763 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 92737 = 611554480090540028006395518925866 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 611554480090540028006395518925866 = ((25499935037649012188329682365827475352 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 649657 = 87297955413635827178386596678906 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 87297955413635827178386596678906 = ((31216958263131545345602498431503910922 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_77158673929).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 77158673929 = 735027248813831938623143898 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 735027248813831938623143898 = ((4890363098866336102523420127418625199 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_55515497 : Nat.Prime 55515497 := by
  refine lucas_primality 55515497 (3 : ZMod 55515497) ?_ (fun q hq hd => ?_)
  · rw [show 55515497 - 1 = 55515496 from by norm_num]
    reduce_mod_char
  · have e : 55515497 - 1 = [2 ^ 3, 6939437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55515497 - 1) / 2 = 27757748 from by norm_num]
      have h2 : (3 : ZMod 55515497) ^ 27757748 = ((55515496 : ℕ) : ZMod 55515497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (55515497 - 1) / 6939437 = 8 from by norm_num]
      have h2 : (3 : ZMod 55515497) ^ 8 = ((6561 : ℕ) : ZMod 55515497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_733803839347 : Nat.Prime 733803839347 := by
  refine lucas_primality 733803839347 (2 : ZMod 733803839347) ?_ (fun q hq hd => ?_)
  · rw [show 733803839347 - 1 = 733803839346 from by norm_num]
    reduce_mod_char
  · have e : 733803839347 - 1 = [2 ^ 1, 3 ^ 1, 2203 ^ 1, 55515497 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (733803839347 - 1) / 2 = 366901919673 from by norm_num]
      have h2 : (2 : ZMod 733803839347) ^ 366901919673 = ((733803839346 : ℕ) : ZMod 733803839347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (733803839347 - 1) / 3 = 244601279782 from by norm_num]
      have h2 : (2 : ZMod 733803839347) ^ 244601279782 = ((401179229705 : ℕ) : ZMod 733803839347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (733803839347 - 1) / 2203 = 333092982 from by norm_num]
      have h2 : (2 : ZMod 733803839347) ^ 333092982 = ((589562106673 : ℕ) : ZMod 733803839347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_55515497).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (733803839347 - 1) / 55515497 = 13218 from by norm_num]
      have h2 : (2 : ZMod 733803839347) ^ 13218 = ((232562832822 : ℕ) : ZMod 733803839347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  refine lucas_primality 5704689200685129054721 (21 : ZMod 5704689200685129054721) ?_ (fun q hq hd => ?_)
  · rw [show 5704689200685129054721 - 1 = 5704689200685129054720 from by norm_num]
    reduce_mod_char
  · have e : 5704689200685129054721 - 1 = [2 ^ 9, 3 ^ 5, 5 ^ 1, 12497 ^ 1, 733803839347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5704689200685129054721 - 1) / 2 = 2852344600342564527360 from by norm_num]
      have h2 : (21 : ZMod 5704689200685129054721) ^ 2852344600342564527360 = ((5704689200685129054720 : ℕ) : ZMod 5704689200685129054721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5704689200685129054721 - 1) / 3 = 1901563066895043018240 from by norm_num]
      have h2 : (21 : ZMod 5704689200685129054721) ^ 1901563066895043018240 = ((2079877874432748107725 : ℕ) : ZMod 5704689200685129054721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5704689200685129054721 - 1) / 5 = 1140937840137025810944 from by norm_num]
      have h2 : (21 : ZMod 5704689200685129054721) ^ 1140937840137025810944 = ((10029027896913374990 : ℕ) : ZMod 5704689200685129054721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5704689200685129054721 - 1) / 12497 = 456484692380981760 from by norm_num]
      have h2 : (21 : ZMod 5704689200685129054721) ^ 456484692380981760 = ((1509085296944985134886 : ℕ) : ZMod 5704689200685129054721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_733803839347).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5704689200685129054721 - 1) / 733803839347 = 7774133760 from by norm_num]
      have h2 : (21 : ZMod 5704689200685129054721) ^ 7774133760 = ((5188443542004454288865 : ℕ) : ZMod 5704689200685129054721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18717738334417 : Nat.Prime 18717738334417 := by
  refine lucas_primality 18717738334417 (5 : ZMod 18717738334417) ?_ (fun q hq hd => ?_)
  · rw [show 18717738334417 - 1 = 18717738334416 from by norm_num]
    reduce_mod_char
  · have e : 18717738334417 - 1 = [2 ^ 4, 3 ^ 2, 11 ^ 1, 19 ^ 1, 23 ^ 1, 131 ^ 1, 151 ^ 1, 1367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 2 = 9358869167208 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 9358869167208 = ((18717738334416 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 3 = 6239246111472 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 6239246111472 = ((1819224690458 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 11 = 1701612575856 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 1701612575856 = ((6892191680092 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 19 = 985144122864 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 985144122864 = ((12835695315599 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 23 = 813814710192 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 813814710192 = ((17914967141951 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 131 = 142883498736 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 142883498736 = ((12753705593516 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 151 = 123958532016 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 123958532016 = ((18493820077975 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 1367 = 13692566448 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 13692566448 = ((11082255859751 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11281292593 : Nat.Prime 11281292593 := by
  refine lucas_primality 11281292593 (5 : ZMod 11281292593) ?_ (fun q hq hd => ?_)
  · rw [show 11281292593 - 1 = 11281292592 from by norm_num]
    reduce_mod_char
  · have e : 11281292593 - 1 = [2 ^ 4, 3 ^ 1, 163 ^ 1, 1441883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 2 = 5640646296 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 5640646296 = ((11281292592 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 3 = 3760430864 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 3760430864 = ((5012914318 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 163 = 69210384 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 69210384 = ((10744421681 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11281292593 - 1) / 1441883 = 7824 from by norm_num]
      have h2 : (5 : ZMod 11281292593) ^ 7824 = ((6708663093 : ℕ) : ZMod 11281292593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2812085643403 : Nat.Prime 2812085643403 := by
  refine lucas_primality 2812085643403 (3 : ZMod 2812085643403) ?_ (fun q hq hd => ?_)
  · rw [show 2812085643403 - 1 = 2812085643402 from by norm_num]
    reduce_mod_char
  · have e : 2812085643403 - 1 = [2 ^ 1, 3 ^ 3, 7 ^ 1, 379 ^ 1, 19628971 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 2 = 1406042821701 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 1406042821701 = ((2812085643402 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 3 = 937361881134 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 937361881134 = ((1861256251728 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 7 = 401726520486 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 401726520486 = ((2411702389629 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 379 = 7419751038 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 7419751038 = ((1756790367693 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 19628971 = 143262 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 143262 = ((2629013928282 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11248342573613 : Nat.Prime 11248342573613 := by
  refine lucas_primality 11248342573613 (2 : ZMod 11248342573613) ?_ (fun q hq hd => ?_)
  · rw [show 11248342573613 - 1 = 11248342573612 from by norm_num]
    reduce_mod_char
  · have e : 11248342573613 - 1 = [2 ^ 2, 2812085643403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11248342573613 - 1) / 2 = 5624171286806 from by norm_num]
      have h2 : (2 : ZMod 11248342573613) ^ 5624171286806 = ((11248342573612 : ℕ) : ZMod 11248342573613) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2812085643403).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11248342573613 - 1) / 2812085643403 = 4 from by norm_num]
      have h2 : (2 : ZMod 11248342573613) ^ 4 = ((16 : ℕ) : ZMod 11248342573613) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_57912614113275649087721 : Nat.Prime 57912614113275649087721 := by
  refine lucas_primality 57912614113275649087721 (6 : ZMod 57912614113275649087721) ?_ (fun q hq hd => ?_)
  · rw [show 57912614113275649087721 - 1 = 57912614113275649087720 from by norm_num]
    reduce_mod_char
  · have e : 57912614113275649087721 - 1 = [2 ^ 3, 5 ^ 1, 83 ^ 1, 383 ^ 1, 4049 ^ 1, 11248342573613 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 2 = 28956307056637824543860 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 28956307056637824543860 = ((57912614113275649087720 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 5 = 11582522822655129817544 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 11582522822655129817544 = ((2789656255697642251826 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 83 = 697742338714164446840 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 697742338714164446840 = ((2048 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 383 = 151207869747456002840 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 151207869747456002840 = ((13840262541632795827357 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 4049 = 14302942482903346280 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 14302942482903346280 = ((49137993049991644527724 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11248342573613).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 11248342573613 = 5148546440 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 5148546440 = ((12190088266157509011350 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13455809771 : Nat.Prime 13455809771 := by
  refine lucas_primality 13455809771 (6 : ZMod 13455809771) ?_ (fun q hq hd => ?_)
  · rw [show 13455809771 - 1 = 13455809770 from by norm_num]
    reduce_mod_char
  · have e : 13455809771 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 83 ^ 1, 1247063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 2 = 6727904885 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 6727904885 = ((13455809770 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 5 = 2691161954 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 2691161954 = ((1965912534 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 13 = 1035062290 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 1035062290 = ((3658939577 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 83 = 162118190 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 162118190 = ((1932386723 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 1247063 = 10790 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 10790 = ((2765812487 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62357403192785191176690552862561408838653121833643 : Nat.Prime 62357403192785191176690552862561408838653121833643 := by
  refine lucas_primality 62357403192785191176690552862561408838653121833643 (5 : ZMod 62357403192785191176690552862561408838653121833643) ?_ (fun q hq hd => ?_)
  · rw [show 62357403192785191176690552862561408838653121833643 - 1 = 62357403192785191176690552862561408838653121833642 from by norm_num]
    reduce_mod_char
  · have e : 62357403192785191176690552862561408838653121833643 - 1 = [2 ^ 1, 167 ^ 1, 499 ^ 1, 1163 ^ 1, 2657 ^ 1, 155377 ^ 1, 13455809771 ^ 1, 57912614113275649087721 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 2 = 31178701596392595588345276431280704419326560916821 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 31178701596392595588345276431280704419326560916821 = ((62357403192785191176690552862561408838653121833642 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 167 = 373397623908893360339464388398571310411096537926 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 373397623908893360339464388398571310411096537926 = ((4722366482869645213696 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 499 = 124964735857284952257896899524171159997300845358 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 124964735857284952257896899524171159997300845358 = ((5654690063819526687114185670138774069384207763612 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 1163 = 53617715556995005310997895840551512329022460734 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 53617715556995005310997895840551512329022460734 = ((52975413414649427173654278002932500914073322812877 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 2657 = 23469101690924046359311461370930150108638736106 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 23469101690924046359311461370930150108638736106 = ((19479191169619287166628604435995117003532175761136 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 155377 = 401329689675982875050300577708164070864111946 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 401329689675982875050300577708164070864111946 = ((25099234347126700213636254703795719764041584271199 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13455809771).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 13455809771 = 4634236382204068183291988132741670047102 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 4634236382204068183291988132741670047102 = ((19230407800519824566556629448312403520362982478802 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_57912614113275649087721).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 57912614113275649087721 = 1076749930003429718271634202 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 1076749930003429718271634202 = ((13225062437438194656646142161181233982784987732573 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_58745093521 : Nat.Prime 58745093521 := by
  refine lucas_primality 58745093521 (19 : ZMod 58745093521) ?_ (fun q hq hd => ?_)
  · rw [show 58745093521 - 1 = 58745093520 from by norm_num]
    reduce_mod_char
  · have e : 58745093521 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 29 ^ 1, 61 ^ 1, 179 ^ 1, 773 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 2 = 29372546760 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 29372546760 = ((58745093520 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 3 = 19581697840 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 19581697840 = ((49792440108 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 5 = 11749018704 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 11749018704 = ((24503522696 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 29 = 2025692880 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 2025692880 = ((40443354632 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 61 = 963034320 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 963034320 = ((57618891522 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 179 = 328184880 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 328184880 = ((58208222609 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 773 = 75996240 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 75996240 = ((56833696861 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43717618369 : Nat.Prime 43717618369 := by
  refine lucas_primality 43717618369 (7 : ZMod 43717618369) ?_ (fun q hq hd => ?_)
  · rw [show 43717618369 - 1 = 43717618368 from by norm_num]
    reduce_mod_char
  · have e : 43717618369 - 1 = [2 ^ 6, 3 ^ 2, 23 ^ 1, 3299941 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 2 = 21858809184 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 21858809184 = ((43717618368 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 3 = 14572539456 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 14572539456 = ((4841435582 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 23 = 1900766016 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 1900766016 = ((21902536539 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 3299941 = 13248 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 13248 = ((21440435857 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_88114244437 : Nat.Prime 88114244437 := by
  refine lucas_primality 88114244437 (2 : ZMod 88114244437) ?_ (fun q hq hd => ?_)
  · rw [show 88114244437 - 1 = 88114244436 from by norm_num]
    reduce_mod_char
  · have e : 88114244437 - 1 = [2 ^ 2, 3 ^ 2, 983 ^ 1, 2489947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 2 = 44057122218 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 44057122218 = ((88114244436 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 3 = 29371414812 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 29371414812 = ((21612683043 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 983 = 89638092 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 89638092 = ((17822603986 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 2489947 = 35388 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 35388 = ((82355390884 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3011347479614249131 : Nat.Prime 3011347479614249131 := by
  refine lucas_primality 3011347479614249131 (11 : ZMod 3011347479614249131) ?_ (fun q hq hd => ?_)
  · rw [show 3011347479614249131 - 1 = 3011347479614249130 from by norm_num]
    reduce_mod_char
  · have e : 3011347479614249131 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 19 ^ 1, 59957 ^ 1, 88114244437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 2 = 1505673739807124565 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 1505673739807124565 = ((3011347479614249130 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 3 = 1003782493204749710 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 1003782493204749710 = ((2895214250005825179 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 5 = 602269495922849826 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 602269495922849826 = ((2867232291538393259 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 19 = 158491972611276270 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 158491972611276270 = ((1433616283207887958 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 59957 = 50225119329090 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 50225119329090 = ((2607332680629660854 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_88114244437).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 88114244437 = 34175490 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 34175490 = ((1746373792546638637 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_30327152671 : Nat.Prime 30327152671 := by
  refine lucas_primality 30327152671 (3 : ZMod 30327152671) ?_ (fun q hq hd => ?_)
  · rw [show 30327152671 - 1 = 30327152670 from by norm_num]
    reduce_mod_char
  · have e : 30327152671 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 19 ^ 1, 17735177 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 2 = 15163576335 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 15163576335 = ((30327152670 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 3 = 10109050890 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 10109050890 = ((29604117504 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 5 = 6065430534 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 6065430534 = ((12694515794 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 19 = 1596165930 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 1596165930 = ((1666875589 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 17735177 = 1710 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 1710 = ((28134759737 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_420778751 : Nat.Prime 420778751 := by
  refine lucas_primality 420778751 (7 : ZMod 420778751) ?_ (fun q hq hd => ?_)
  · rw [show 420778751 - 1 = 420778750 from by norm_num]
    reduce_mod_char
  · have e : 420778751 - 1 = [2 ^ 1, 5 ^ 4, 7 ^ 1, 19 ^ 1, 2531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 2 = 210389375 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 210389375 = ((420778750 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 5 = 84155750 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 84155750 = ((524288 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 7 = 60111250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 60111250 = ((201341668 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 19 = 22146250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 22146250 = ((33554432 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 2531 = 166250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 166250 = ((152440542 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1046183622564446793972631570534611069350392574077339085483 : Nat.Prime 1046183622564446793972631570534611069350392574077339085483 := by
  refine lucas_primality 1046183622564446793972631570534611069350392574077339085483 (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ?_ (fun q hq hd => ?_)
  · rw [show 1046183622564446793972631570534611069350392574077339085483 - 1 = 1046183622564446793972631570534611069350392574077339085482 from by norm_num]
    reduce_mod_char
  · have e : 1046183622564446793972631570534611069350392574077339085483 - 1 = [2 ^ 1, 11 ^ 1, 31 ^ 1, 191 ^ 1, 2281 ^ 1, 174763 ^ 1, 524287 ^ 1, 420778751 ^ 1, 30327152671 ^ 1, 3011347479614249131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 2 = 523091811282223396986315785267305534675196287038669542741 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 523091811282223396986315785267305534675196287038669542741 = ((1046183622564446793972631570534611069350392574077339085482 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 11 = 95107602051313344906602870048601006304581143097939916862 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 95107602051313344906602870048601006304581143097939916862 = ((392627861128721398270385662931499492095119081969670164202 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 31 = 33747858792401509482988115178535840946786857228301260822 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 33747858792401509482988115178535840946786857228301260822 = ((668720009492427274422763613743367331285779503336716402562 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 191 = 5477401165258883738076605081333042247907814523965126102 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 5477401165258883738076605081333042247907814523965126102 = ((1046183622564446793972631570534611069350383566878084344491 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 2281 = 458651303184764048212464520181767237768694683944471322 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 458651303184764048212464520181767237768694683944471322 = ((499429585860639984181308667942268674119909093647835184918 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 174763 = 5986299288547614735227889029912573424296862459887614 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 5986299288547614735227889029912573424296862459887614 = ((248040500576282970343340937908980153625899322235683007836 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 524287 = 1995440708170232704554245233115852709203914218886486 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 1995440708170232704554245233115852709203914218886486 = ((294798488655519398464719949555363020029762437035584062431 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_420778751).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 420778751 = 2486303360324501733151043956909818075272514352982 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 2486303360324501733151043956909818075272514352982 = ((878592421611204831865755714371582403555501104121970642104 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_30327152671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 30327152671 = 34496598936069859374522076132645029917269432342 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 34496598936069859374522076132645029917269432342 = ((789307095480842102922449012624163433968993390143946051487 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3011347479614249131).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 3011347479614249131 = 347413783911268175208721342252213146622 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 347413783911268175208721342252213146622 = ((736362618765011735680597310066553278420759964667086924968 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_197002597249 : Nat.Prime 197002597249 := by
  refine lucas_primality 197002597249 (7 : ZMod 197002597249) ?_ (fun q hq hd => ?_)
  · rw [show 197002597249 - 1 = 197002597248 from by norm_num]
    reduce_mod_char
  · have e : 197002597249 - 1 = [2 ^ 7, 3 ^ 2, 59 ^ 1, 197 ^ 1, 14713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 2 = 98501298624 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 98501298624 = ((197002597248 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 3 = 65667532416 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 65667532416 = ((181261311599 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 59 = 3339027072 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 3339027072 = ((102617846236 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 197 = 1000013184 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 1000013184 = ((154407757021 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 14713 = 13389696 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 13389696 = ((84679904707 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_71925114571 : Nat.Prime 71925114571 := by
  refine lucas_primality 71925114571 (2 : ZMod 71925114571) ?_ (fun q hq hd => ?_)
  · rw [show 71925114571 - 1 = 71925114570 from by norm_num]
    reduce_mod_char
  · have e : 71925114571 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 29527 ^ 1, 81197 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 2 = 35962557285 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 35962557285 = ((71925114570 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 3 = 23975038190 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 23975038190 = ((27391352207 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 5 = 14385022914 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 14385022914 = ((62063425361 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 29527 = 2435910 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 2435910 = ((36912035711 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 81197 = 885810 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 885810 = ((49506324629 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_242099935645987 : Nat.Prime 242099935645987 := by
  refine lucas_primality 242099935645987 (3 : ZMod 242099935645987) ?_ (fun q hq hd => ?_)
  · rw [show 242099935645987 - 1 = 242099935645986 from by norm_num]
    reduce_mod_char
  · have e : 242099935645987 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 17 ^ 1, 71925114571 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 2 = 121049967822993 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 121049967822993 = ((242099935645986 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 3 = 80699978548662 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 80699978548662 = ((8589934591 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 11 = 22009085058726 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 22009085058726 = ((206915563557155 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 17 = 14241172685058 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 14241172685058 = ((22459685976768 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_71925114571).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 71925114571 = 3366 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 3366 = ((186518681366362 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33057806959 : Nat.Prime 33057806959 := by
  refine lucas_primality 33057806959 (3 : ZMod 33057806959) ?_ (fun q hq hd => ?_)
  · rw [show 33057806959 - 1 = 33057806958 from by norm_num]
    reduce_mod_char
  · have e : 33057806959 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 757 ^ 1, 220553 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 2 = 16528903479 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 16528903479 = ((33057806958 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 3 = 11019268986 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 11019268986 = ((24467872366 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 11 = 3005255178 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 3005255178 = ((27851839265 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 757 = 43669494 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 43669494 = ((26031839672 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 220553 = 149886 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 149886 = ((25789327052 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_267823007376498379256993682056860433753700498963798805883563 : Nat.Prime 267823007376498379256993682056860433753700498963798805883563 := by
  refine lucas_primality 267823007376498379256993682056860433753700498963798805883563 (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ?_ (fun q hq hd => ?_)
  · rw [show 267823007376498379256993682056860433753700498963798805883563 - 1 = 267823007376498379256993682056860433753700498963798805883562 from by norm_num]
    reduce_mod_char
  · have e : 267823007376498379256993682056860433753700498963798805883563 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 19 ^ 1, 23 ^ 1, 67 ^ 1, 73 ^ 1, 89 ^ 1, 199 ^ 1, 683 ^ 1, 5347 ^ 1, 20857 ^ 1, 153649 ^ 1, 599479 ^ 1, 33057806959 ^ 1, 242099935645987 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 2 = 133911503688249189628496841028430216876850249481899402941781 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 133911503688249189628496841028430216876850249481899402941781 = ((267823007376498379256993682056860433753700498963798805883562 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 3 = 89274335792166126418997894018953477917900166321266268627854 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 89274335792166126418997894018953477917900166321266268627854 = ((36815630904361092209737552665730480048115022627703598762214 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 7 = 38260429625214054179570526008122919107671499851971257983366 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 38260429625214054179570526008122919107671499851971257983366 = ((35841102619207590198090187545676964691858178623229566806001 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 19 = 14095947756657809434578614845097917565984236787568358204398 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 14095947756657809434578614845097917565984236787568358204398 = ((162098122350280735903543769103673941662665441846796661083647 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 23 = 11644478581586886054651899219863497119726108650599948081894 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 11644478581586886054651899219863497119726108650599948081894 = ((195532894955455271964375805556984722262820899210836174133337 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 67 = 3997358319052214615776025105326275130652246253191026953486 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3997358319052214615776025105326275130652246253191026953486 = ((260787608071257689816131188533459492786583181793112352135733 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 73 = 3668808320226005195301283315847403202105486287175326107994 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3668808320226005195301283315847403202105486287175326107994 = ((150544755313019000406909592466338531119743569782765107761804 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 89 = 3009247273893240216370715528728768918580904482739312425658 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3009247273893240216370715528728768918580904482739312425658 = ((5680635253290054345291260478285785844830877650939100096637 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 199 = 1345844258173358689733636593250554943485932155596978924038 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1345844258173358689733636593250554943485932155596978924038 = ((267823007376498379256993682056857957873621928203249007635115 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 683 = 392127390009514464505115200668902538438800144895752278014 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 392127390009514464505115200668902538438800144895752278014 = ((185153421977849516207155827680995619890575121291734573585466 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 5347 = 50088462198709253648212770162120896531456985031568880846 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 50088462198709253648212770162120896531456985031568880846 = ((199159830018987509148482917892068975782819560271144571588453 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 20857 = 12840917072277814606942210387728840856964112718214451066 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 12840917072277814606942210387728840856964112718214451066 = ((103660928210981162444432134853328150874384371914374611179862 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 153649 = 1743083309207989503719475441147423242284040240833320138 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1743083309207989503719475441147423242284040240833320138 = ((177853284999206938881933068304342199059216080115207607613387 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 599479 = 446759615226719166571295545059727586377004864163379878 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 446759615226719166571295545059727586377004864163379878 = ((137372747932667430846820751479819210735751035080487091239719 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_33057806959).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 33057806959 = 8101656825229402213262336875540965123635698793718 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 8101656825229402213262336875540965123635698793718 = ((183884872936239850816029887793344150731632215969868119171573 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_242099935645987).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 242099935645987 = 1106249808211949269625294237354609307299931726 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1106249808211949269625294237354609307299931726 = ((57029675977955819176377809079584485433380302731697421519818 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5344743097 : Nat.Prime 5344743097 := by
  refine lucas_primality 5344743097 (15 : ZMod 5344743097) ?_ (fun q hq hd => ?_)
  · rw [show 5344743097 - 1 = 5344743096 from by norm_num]
    reduce_mod_char
  · have e : 5344743097 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 11 ^ 1, 211 ^ 1, 1523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 2 = 2672371548 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 2672371548 = ((5344743096 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 3 = 1781581032 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 1781581032 = ((2635540349 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 7 = 763534728 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 763534728 = ((2995612971 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 11 = 485885736 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 485885736 = ((2467030965 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 211 = 25330536 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 25330536 = ((1994125691 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5344743097 - 1) / 1523 = 3509352 from by norm_num]
      have h2 : (15 : ZMod 5344743097) ^ 3509352 = ((3025069280 : ℕ) : ZMod 5344743097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_219256122131 : Nat.Prime 219256122131 := by
  refine lucas_primality 219256122131 (6 : ZMod 219256122131) ?_ (fun q hq hd => ?_)
  · rw [show 219256122131 - 1 = 219256122130 from by norm_num]
    reduce_mod_char
  · have e : 219256122131 - 1 = [2 ^ 1, 5 ^ 1, 223 ^ 1, 293 ^ 1, 335567 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 2 = 109628061065 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 109628061065 = ((219256122130 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 5 = 43851224426 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 43851224426 = ((83775092159 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 223 = 983211310 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 983211310 = ((208026254868 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 293 = 748314410 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 748314410 = ((198591088661 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 335567 = 653390 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 653390 = ((208399723861 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2030149279 : Nat.Prime 2030149279 := by
  refine lucas_primality 2030149279 (3 : ZMod 2030149279) ?_ (fun q hq hd => ?_)
  · rw [show 2030149279 - 1 = 2030149278 from by norm_num]
    reduce_mod_char
  · have e : 2030149279 - 1 = [2 ^ 1, 3 ^ 3, 19 ^ 1, 97 ^ 1, 20399 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 2 = 1015074639 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 1015074639 = ((2030149278 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 3 = 676716426 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 676716426 = ((589861502 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 19 = 106849962 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 106849962 = ((618116451 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 97 = 20929374 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 20929374 = ((90941401 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 20399 = 99522 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 99522 = ((1780601521 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_609216967367 : Nat.Prime 609216967367 := by
  refine lucas_primality 609216967367 (5 : ZMod 609216967367) ?_ (fun q hq hd => ?_)
  · rw [show 609216967367 - 1 = 609216967366 from by norm_num]
    reduce_mod_char
  · have e : 609216967367 - 1 = [2 ^ 1, 7 ^ 3, 17 ^ 1, 19 ^ 1, 2749447 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (609216967367 - 1) / 2 = 304608483683 from by norm_num]
      have h2 : (5 : ZMod 609216967367) ^ 304608483683 = ((609216967366 : ℕ) : ZMod 609216967367) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (609216967367 - 1) / 7 = 87030995338 from by norm_num]
      have h2 : (5 : ZMod 609216967367) ^ 87030995338 = ((221589095278 : ℕ) : ZMod 609216967367) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (609216967367 - 1) / 17 = 35836292198 from by norm_num]
      have h2 : (5 : ZMod 609216967367) ^ 35836292198 = ((580100085845 : ℕ) : ZMod 609216967367) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (609216967367 - 1) / 19 = 32064050914 from by norm_num]
      have h2 : (5 : ZMod 609216967367) ^ 32064050914 = ((211257592941 : ℕ) : ZMod 609216967367) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (609216967367 - 1) / 2749447 = 221578 from by norm_num]
      have h2 : (5 : ZMod 609216967367) ^ 221578 = ((229700245133 : ℕ) : ZMod 609216967367) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_436199348634773 : Nat.Prime 436199348634773 := by
  refine lucas_primality 436199348634773 (2 : ZMod 436199348634773) ?_ (fun q hq hd => ?_)
  · rw [show 436199348634773 - 1 = 436199348634772 from by norm_num]
    reduce_mod_char
  · have e : 436199348634773 - 1 = [2 ^ 2, 179 ^ 1, 609216967367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (436199348634773 - 1) / 2 = 218099674317386 from by norm_num]
      have h2 : (2 : ZMod 436199348634773) ^ 218099674317386 = ((436199348634772 : ℕ) : ZMod 436199348634773) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (436199348634773 - 1) / 179 = 2436867869468 from by norm_num]
      have h2 : (2 : ZMod 436199348634773) ^ 2436867869468 = ((2401681859394 : ℕ) : ZMod 436199348634773) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_609216967367).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (436199348634773 - 1) / 609216967367 = 716 from by norm_num]
      have h2 : (2 : ZMod 436199348634773) ^ 716 = ((298200398616423 : ℕ) : ZMod 436199348634773) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_247446349 : Nat.Prime 247446349 := by
  refine lucas_primality 247446349 (2 : ZMod 247446349) ?_ (fun q hq hd => ?_)
  · rw [show 247446349 - 1 = 247446348 from by norm_num]
    reduce_mod_char
  · have e : 247446349 - 1 = [2 ^ 2, 3 ^ 1, 19 ^ 1, 73 ^ 1, 14867 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (247446349 - 1) / 2 = 123723174 from by norm_num]
      have h2 : (2 : ZMod 247446349) ^ 123723174 = ((247446348 : ℕ) : ZMod 247446349) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (247446349 - 1) / 3 = 82482116 from by norm_num]
      have h2 : (2 : ZMod 247446349) ^ 82482116 = ((49335819 : ℕ) : ZMod 247446349) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (247446349 - 1) / 19 = 13023492 from by norm_num]
      have h2 : (2 : ZMod 247446349) ^ 13023492 = ((32217834 : ℕ) : ZMod 247446349) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (247446349 - 1) / 73 = 3389676 from by norm_num]
      have h2 : (2 : ZMod 247446349) ^ 3389676 = ((143027188 : ℕ) : ZMod 247446349) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (247446349 - 1) / 14867 = 16644 from by norm_num]
      have h2 : (2 : ZMod 247446349) ^ 16644 = ((200623531 : ℕ) : ZMod 247446349) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1511103107581937986112879 : Nat.Prime 1511103107581937986112879 := by
  refine lucas_primality 1511103107581937986112879 (11 : ZMod 1511103107581937986112879) ?_ (fun q hq hd => ?_)
  · rw [show 1511103107581937986112879 - 1 = 1511103107581937986112878 from by norm_num]
    reduce_mod_char
  · have e : 1511103107581937986112879 - 1 = [2 ^ 1, 7 ^ 1, 247446349 ^ 1, 436199348634773 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1511103107581937986112879 - 1) / 2 = 755551553790968993056439 from by norm_num]
      have h2 : (11 : ZMod 1511103107581937986112879) ^ 755551553790968993056439 = ((1511103107581937986112878 : ℕ) : ZMod 1511103107581937986112879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1511103107581937986112879 - 1) / 7 = 215871872511705426587554 from by norm_num]
      have h2 : (11 : ZMod 1511103107581937986112879) ^ 215871872511705426587554 = ((460950680804557974361795 : ℕ) : ZMod 1511103107581937986112879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_247446349).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1511103107581937986112879 - 1) / 247446349 = 6106790880886822 from by norm_num]
      have h2 : (11 : ZMod 1511103107581937986112879) ^ 6106790880886822 = ((610167397158692118316141 : ℕ) : ZMod 1511103107581937986112879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_436199348634773).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1511103107581937986112879 - 1) / 436199348634773 = 3464248886 from by norm_num]
      have h2 : (11 : ZMod 1511103107581937986112879) ^ 3464248886 = ((120463558342953739013230 : ℕ) : ZMod 1511103107581937986112879) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5143794978208916904728240117 : Nat.Prime 5143794978208916904728240117 := by
  refine lucas_primality 5143794978208916904728240117 (3 : ZMod 5143794978208916904728240117) ?_ (fun q hq hd => ?_)
  · rw [show 5143794978208916904728240117 - 1 = 5143794978208916904728240116 from by norm_num]
    reduce_mod_char
  · have e : 5143794978208916904728240117 - 1 = [2 ^ 2, 23 ^ 1, 37 ^ 1, 1511103107581937986112879 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5143794978208916904728240117 - 1) / 2 = 2571897489104458452364120058 from by norm_num]
      have h2 : (3 : ZMod 5143794978208916904728240117) ^ 2571897489104458452364120058 = ((5143794978208916904728240116 : ℕ) : ZMod 5143794978208916904728240117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5143794978208916904728240117 - 1) / 23 = 223643259922126821944706092 from by norm_num]
      have h2 : (3 : ZMod 5143794978208916904728240117) ^ 223643259922126821944706092 = ((2226169550635159783310716884 : ℕ) : ZMod 5143794978208916904728240117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5143794978208916904728240117 - 1) / 37 = 139021485897538294722384868 from by norm_num]
      have h2 : (3 : ZMod 5143794978208916904728240117) ^ 139021485897538294722384868 = ((1601215914027140419260221347 : ℕ) : ZMod 5143794978208916904728240117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1511103107581937986112879).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5143794978208916904728240117 - 1) / 1511103107581937986112879 = 3404 from by norm_num]
      have h2 : (3 : ZMod 5143794978208916904728240117) ^ 3404 = ((4496422430717169094377880610 : ℕ) : ZMod 5143794978208916904728240117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_101592497 : Nat.Prime 101592497 := by
  refine lucas_primality 101592497 (3 : ZMod 101592497) ?_ (fun q hq hd => ?_)
  · rw [show 101592497 - 1 = 101592496 from by norm_num]
    reduce_mod_char
  · have e : 101592497 - 1 = [2 ^ 4, 6349531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101592497 - 1) / 2 = 50796248 from by norm_num]
      have h2 : (3 : ZMod 101592497) ^ 50796248 = ((101592496 : ℕ) : ZMod 101592497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (101592497 - 1) / 6349531 = 16 from by norm_num]
      have h2 : (3 : ZMod 101592497) ^ 16 = ((43046721 : ℕ) : ZMod 101592497) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56688613327 : Nat.Prime 56688613327 := by
  refine lucas_primality 56688613327 (3 : ZMod 56688613327) ?_ (fun q hq hd => ?_)
  · rw [show 56688613327 - 1 = 56688613326 from by norm_num]
    reduce_mod_char
  · have e : 56688613327 - 1 = [2 ^ 1, 3 ^ 2, 31 ^ 1, 101592497 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56688613327 - 1) / 2 = 28344306663 from by norm_num]
      have h2 : (3 : ZMod 56688613327) ^ 28344306663 = ((56688613326 : ℕ) : ZMod 56688613327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56688613327 - 1) / 3 = 18896204442 from by norm_num]
      have h2 : (3 : ZMod 56688613327) ^ 18896204442 = ((56681514300 : ℕ) : ZMod 56688613327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56688613327 - 1) / 31 = 1828664946 from by norm_num]
      have h2 : (3 : ZMod 56688613327) ^ 1828664946 = ((42773606571 : ℕ) : ZMod 56688613327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_101592497).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56688613327 - 1) / 101592497 = 558 from by norm_num]
      have h2 : (3 : ZMod 56688613327) ^ 558 = ((48392896552 : ℕ) : ZMod 56688613327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_146015998229939627978883160681418486308944251 : Nat.Prime 146015998229939627978883160681418486308944251 := by
  refine lucas_primality 146015998229939627978883160681418486308944251 (2 : ZMod 146015998229939627978883160681418486308944251) ?_ (fun q hq hd => ?_)
  · rw [show 146015998229939627978883160681418486308944251 - 1 = 146015998229939627978883160681418486308944250 from by norm_num]
    reduce_mod_char
  · have e : 146015998229939627978883160681418486308944251 - 1 = [2 ^ 1, 5 ^ 3, 2003 ^ 1, 56688613327 ^ 1, 5143794978208916904728240117 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146015998229939627978883160681418486308944251 - 1) / 2 = 73007999114969813989441580340709243154472125 from by norm_num]
      have h2 : (2 : ZMod 146015998229939627978883160681418486308944251) ^ 73007999114969813989441580340709243154472125 = ((146015998229939627978883160681418486308944250 : ℕ) : ZMod 146015998229939627978883160681418486308944251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146015998229939627978883160681418486308944251 - 1) / 5 = 29203199645987925595776632136283697261788850 from by norm_num]
      have h2 : (2 : ZMod 146015998229939627978883160681418486308944251) ^ 29203199645987925595776632136283697261788850 = ((128541415315834180276980018284152919629514606 : ℕ) : ZMod 146015998229939627978883160681418486308944251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146015998229939627978883160681418486308944251 - 1) / 2003 = 72898651138262420358903225502455559814750 from by norm_num]
      have h2 : (2 : ZMod 146015998229939627978883160681418486308944251) ^ 72898651138262420358903225502455559814750 = ((72035792006293026805288594002771223064317851 : ℕ) : ZMod 146015998229939627978883160681418486308944251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_56688613327).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146015998229939627978883160681418486308944251 - 1) / 56688613327 = 2575755335338115140042666238587750 from by norm_num]
      have h2 : (2 : ZMod 146015998229939627978883160681418486308944251) ^ 2575755335338115140042666238587750 = ((4737532898736143591993391610866191804215572 : ℕ) : ZMod 146015998229939627978883160681418486308944251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5143794978208916904728240117).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146015998229939627978883160681418486308944251 - 1) / 5143794978208916904728240117 = 28386823123495250 from by norm_num]
      have h2 : (2 : ZMod 146015998229939627978883160681418486308944251) ^ 28386823123495250 = ((138564684047536938808248648511734732808035096 : ℕ) : ZMod 146015998229939627978883160681418486308944251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1440990623 : Nat.Prime 1440990623 := by
  refine lucas_primality 1440990623 (5 : ZMod 1440990623) ?_ (fun q hq hd => ?_)
  · rw [show 1440990623 - 1 = 1440990622 from by norm_num]
    reduce_mod_char
  · have e : 1440990623 - 1 = [2 ^ 1, 149 ^ 1, 4835539 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440990623 - 1) / 2 = 720495311 from by norm_num]
      have h2 : (5 : ZMod 1440990623) ^ 720495311 = ((1440990622 : ℕ) : ZMod 1440990623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440990623 - 1) / 149 = 9671078 from by norm_num]
      have h2 : (5 : ZMod 1440990623) ^ 9671078 = ((767293013 : ℕ) : ZMod 1440990623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1440990623 - 1) / 4835539 = 298 from by norm_num]
      have h2 : (5 : ZMod 1440990623) ^ 298 = ((1250260208 : ℕ) : ZMod 1440990623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5058345723951854688505665428846313806490903121677364358901199128608233 : Nat.Prime 5058345723951854688505665428846313806490903121677364358901199128608233 := by
  refine lucas_primality 5058345723951854688505665428846313806490903121677364358901199128608233 (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ?_ (fun q hq hd => ?_)
  · rw [show 5058345723951854688505665428846313806490903121677364358901199128608233 - 1 = 5058345723951854688505665428846313806490903121677364358901199128608232 from by norm_num]
    reduce_mod_char
  · have e : 5058345723951854688505665428846313806490903121677364358901199128608233 - 1 = [2 ^ 3, 3 ^ 2, 23 ^ 1, 47 ^ 1, 251 ^ 1, 2029 ^ 1, 606503 ^ 1, 1440990623 ^ 1, 146015998229939627978883160681418486308944251 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 2 = 2529172861975927344252832714423156903245451560838682179450599564304116 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 2529172861975927344252832714423156903245451560838682179450599564304116 = ((5058345723951854688505665428846313806490903121677364358901199128608232 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 3 = 1686115241317284896168555142948771268830301040559121452967066376202744 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 1686115241317284896168555142948771268830301040559121452967066376202744 = ((2329080120938506167288501604742407101342072204630401437739427642974814 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 23 = 219928074954428464717637627341144078543082744420754972126139092548184 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 219928074954428464717637627341144078543082744420754972126139092548184 = ((3908249051212443399618385247990534420549278356392046218277079199602891 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 47 = 107624377105358610393737562315879017159380917482497114019174449544856 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 107624377105358610393737562315879017159380917482497114019174449544856 = ((4032869842563142173016407082213180924584926502205912793057856133535013 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 251 = 20152771808573126249026555493411608790800410843336112983670116050232 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 20152771808573126249026555493411608790800410843336112983670116050232 = ((64 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 2029 = 2493024013776172838100377244379651949970873889441776421341152848008 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 2493024013776172838100377244379651949970873889441776421341152848008 = ((2973730002865523190255823240433498082752530988260811817314931826400629 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 606503 = 8340182528284039301546184320351777001088045931639850683180790744 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 8340182528284039301546184320351777001088045931639850683180790744 = ((230010574883149818292046955125773970990722244586814435691538092859337 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1440990623).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 1440990623 = 3510325218786558813371032900084537057040171399975421185583384 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 3510325218786558813371032900084537057040171399975421185583384 = ((2852693102078470318167553810254039084640113561126390942166604992683365 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_146015998229939627978883160681418486308944251).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5058345723951854688505665428846313806490903121677364358901199128608233 - 1) / 146015998229939627978883160681418486308944251 = 34642407580477533545042232 from by norm_num]
      have h2 : (15 : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) ^ 34642407580477533545042232 = ((685603760622481544593386575310099995518085269614772858651669395986709 : ℕ) : ZMod 5058345723951854688505665428846313806490903121677364358901199128608233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3853149761 : Nat.Prime 3853149761 := by
  refine lucas_primality 3853149761 (6 : ZMod 3853149761) ?_ (fun q hq hd => ?_)
  · rw [show 3853149761 - 1 = 3853149760 from by norm_num]
    reduce_mod_char
  · have e : 3853149761 - 1 = [2 ^ 6, 5 ^ 1, 719 ^ 1, 16747 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 2 = 1926574880 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 1926574880 = ((3853149760 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 5 = 770629952 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 770629952 = ((2694843562 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 719 = 5359040 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 5359040 = ((803003822 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 16747 = 230080 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 230080 = ((3140195378 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1238926361552897 : Nat.Prime 1238926361552897 := by
  refine lucas_primality 1238926361552897 (3 : ZMod 1238926361552897) ?_ (fun q hq hd => ?_)
  · rw [show 1238926361552897 - 1 = 1238926361552896 from by norm_num]
    reduce_mod_char
  · have e : 1238926361552897 - 1 = [2 ^ 11, 157 ^ 1, 3853149761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 2 = 619463180776448 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 619463180776448 = ((1238926361552896 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 157 = 7891250710528 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 7891250710528 = ((196133765836405 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3853149761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 3853149761 = 321536 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 321536 = ((437771075092802 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_611065913 : Nat.Prime 611065913 := by
  refine lucas_primality 611065913 (3 : ZMod 611065913) ?_ (fun q hq hd => ?_)
  · rw [show 611065913 - 1 = 611065912 from by norm_num]
    reduce_mod_char
  · have e : 611065913 - 1 = [2 ^ 3, 1013 ^ 1, 75403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 2 = 305532956 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 305532956 = ((611065912 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 1013 = 603224 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 603224 = ((340408484 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 75403 = 8104 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 8104 = ((306963438 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_206487726925483 : Nat.Prime 206487726925483 := by
  refine lucas_primality 206487726925483 (2 : ZMod 206487726925483) ?_ (fun q hq hd => ?_)
  · rw [show 206487726925483 - 1 = 206487726925482 from by norm_num]
    reduce_mod_char
  · have e : 206487726925483 - 1 = [2 ^ 1, 3 ^ 2, 18773 ^ 1, 611065913 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 2 = 103243863462741 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 103243863462741 = ((206487726925482 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 3 = 68829242308494 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 68829242308494 = ((2152959480421 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 18773 = 10999186434 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 10999186434 = ((204828111120102 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_611065913).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 611065913 = 337914 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 337914 = ((51630314293860 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37239639534523 : Nat.Prime 37239639534523 := by
  refine lucas_primality 37239639534523 (3 : ZMod 37239639534523) ?_ (fun q hq hd => ?_)
  · rw [show 37239639534523 - 1 = 37239639534522 from by norm_num]
    reduce_mod_char
  · have e : 37239639534523 - 1 = [2 ^ 1, 3 ^ 3, 31 ^ 1, 101 ^ 1, 257 ^ 1, 857029 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 2 = 18619819767261 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 18619819767261 = ((37239639534522 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 3 = 12413213178174 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 12413213178174 = ((16089517958325 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 31 = 1201278694662 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 1201278694662 = ((30654602168578 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 101 = 368709302322 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 368709302322 = ((26562140768659 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 257 = 144901321146 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 144901321146 = ((26984191928336 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 857029 = 43452018 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 43452018 = ((37140272816736 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1329987126233 : Nat.Prime 1329987126233 := by
  refine lucas_primality 1329987126233 (3 : ZMod 1329987126233) ?_ (fun q hq hd => ?_)
  · rw [show 1329987126233 - 1 = 1329987126232 from by norm_num]
    reduce_mod_char
  · have e : 1329987126233 - 1 = [2 ^ 3, 337 ^ 1, 3433 ^ 1, 143699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 2 = 664993563116 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 664993563116 = ((1329987126232 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 337 = 3946549336 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 3946549336 = ((342701223758 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 3433 = 387412504 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 387412504 = ((588448814282 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 143699 = 9255368 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 9255368 = ((597682396658 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25792643401363 : Nat.Prime 25792643401363 := by
  refine lucas_primality 25792643401363 (3 : ZMod 25792643401363) ?_ (fun q hq hd => ?_)
  · rw [show 25792643401363 - 1 = 25792643401362 from by norm_num]
    reduce_mod_char
  · have e : 25792643401363 - 1 = [2 ^ 1, 3 ^ 2, 67 ^ 1, 277 ^ 1, 4703 ^ 1, 16417 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 2 = 12896321700681 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 12896321700681 = ((25792643401362 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 3 = 8597547800454 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 8597547800454 = ((2082476935352 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 67 = 384964826886 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 384964826886 = ((10911884704240 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 277 = 93114236106 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 93114236106 = ((4294967296 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 4703 = 5484295854 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 5484295854 = ((16034357117878 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25792643401363 - 1) / 16417 = 1571093586 from by norm_num]
      have h2 : (3 : ZMod 25792643401363) ^ 1571093586 = ((24194372565776 : ℕ) : ZMod 25792643401363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5203536083 : Nat.Prime 5203536083 := by
  refine lucas_primality 5203536083 (5 : ZMod 5203536083) ?_ (fun q hq hd => ?_)
  · rw [show 5203536083 - 1 = 5203536082 from by norm_num]
    reduce_mod_char
  · have e : 5203536083 - 1 = [2 ^ 1, 281 ^ 1, 9258961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 2 = 2601768041 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 2601768041 = ((5203536082 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 281 = 18517922 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 18517922 = ((624792695 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5203536083 - 1) / 9258961 = 562 from by norm_num]
      have h2 : (5 : ZMod 5203536083) ^ 562 = ((153330139 : ℕ) : ZMod 5203536083) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_144542669 : Nat.Prime 144542669 := by
  refine lucas_primality 144542669 (2 : ZMod 144542669) ?_ (fun q hq hd => ?_)
  · rw [show 144542669 - 1 = 144542668 from by norm_num]
    reduce_mod_char
  · have e : 144542669 - 1 = [2 ^ 2, 383 ^ 1, 94349 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 2 = 72271334 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 72271334 = ((144542668 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 383 = 377396 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 377396 = ((126585098 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (144542669 - 1) / 94349 = 1532 from by norm_num]
      have h2 : (2 : ZMod 144542669) ^ 1532 = ((85830596 : ℕ) : ZMod 144542669) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1249678499 : Nat.Prime 1249678499 := by
  refine lucas_primality 1249678499 (6 : ZMod 1249678499) ?_ (fun q hq hd => ?_)
  · rw [show 1249678499 - 1 = 1249678498 from by norm_num]
    reduce_mod_char
  · have e : 1249678499 - 1 = [2 ^ 1, 29 ^ 1, 307 ^ 1, 70183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 2 = 624839249 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 624839249 = ((1249678498 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 29 = 43092362 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 43092362 = ((648079883 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 307 = 4070614 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 4070614 = ((266073297 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1249678499 - 1) / 70183 = 17806 from by norm_num]
      have h2 : (6 : ZMod 1249678499) ^ 17806 = ((121319156 : ℕ) : ZMod 1249678499) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_84159375948762099254554456081 : Nat.Prime 84159375948762099254554456081 := by
  refine lucas_primality 84159375948762099254554456081 (83 : ZMod 84159375948762099254554456081) ?_ (fun q hq hd => ?_)
  · rw [show 84159375948762099254554456081 - 1 = 84159375948762099254554456080 from by norm_num]
    reduce_mod_char
  · have e : 84159375948762099254554456081 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 257 ^ 1, 421 ^ 1, 673 ^ 1, 859 ^ 1, 90841 ^ 1, 137089 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 2 = 42079687974381049627277228040 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 42079687974381049627277228040 = ((84159375948762099254554456080 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 3 = 28053125316254033084851485360 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 28053125316254033084851485360 = ((4503599627370495 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 5 = 16831875189752419850910891216 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 16831875189752419850910891216 = ((11435863083980520899450414520 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 7 = 12022767992680299893507779440 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 12022767992680299893507779440 = ((74662600791481927477124672443 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 13 = 6473798149904776865734958160 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 6473798149904776865734958160 = ((4722366482869645213696 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 17 = 4950551526397770544385556240 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 4950551526397770544385556240 = ((39348875729423789757659641382 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 97 = 867622432461464940768602640 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 867622432461464940768602640 = ((21918906206941868732369675763 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 257 = 327468388905689102157799440 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 327468388905689102157799440 = ((10704966249718233285857030436 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 421 = 199903505816537052861174480 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 199903505816537052861174480 = ((59121302119014873351613202389 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 673 = 125051078675723773037970960 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 125051078675723773037970960 = ((63661248640154215113310086442 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 859 = 97973662338489056175267120 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 97973662338489056175267120 = ((79124199601514526835032928488 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 90841 = 926447044272543226676880 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 926447044272543226676880 = ((68725869389557593960862862298 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84159375948762099254554456081 - 1) / 137089 = 613903201196026663368720 from by norm_num]
      have h2 : (83 : ZMod 84159375948762099254554456081) ^ 613903201196026663368720 = ((66527993628709433932574257657 : ℕ) : ZMod 84159375948762099254554456081) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_308761441 : Nat.Prime 308761441 := by
  refine lucas_primality 308761441 (17 : ZMod 308761441) ?_ (fun q hq hd => ?_)
  · rw [show 308761441 - 1 = 308761440 from by norm_num]
    reduce_mod_char
  · have e : 308761441 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 49481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 2 = 154380720 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 154380720 = ((308761440 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 3 = 102920480 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 102920480 = ((282204286 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 5 = 61752288 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 61752288 = ((35908262 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 13 = 23750880 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 23750880 = ((308761425 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (308761441 - 1) / 49481 = 6240 from by norm_num]
      have h2 : (17 : ZMod 308761441) ^ 6240 = ((241085963 : ℕ) : ZMod 308761441) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : Nat.Prime 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 := by
  refine lucas_primality 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ?_ (fun q hq hd => ?_)
  · rw [show 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1 = 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434730 from by norm_num]
    reduce_mod_char
  · have e : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 2, 17 ^ 1, 53 ^ 1, 79 ^ 1, 157 ^ 1, 241 ^ 1, 313 ^ 1, 1249 ^ 1, 1613 ^ 1, 2731 ^ 1, 3121 ^ 1, 8191 ^ 1, 21841 ^ 1, 121369 ^ 1, 858001 ^ 1, 22366891 ^ 1, 308761441 ^ 1, 84159375948762099254554456081 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 2 = 2781233119688685003118517846574937649222271513485224960868543760185181934610209049509065217365 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 2781233119688685003118517846574937649222271513485224960868543760185181934610209049509065217365 = ((5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434730 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 3 = 1854155413125790002079011897716625099481514342323483307245695840123454623073472699672710144910 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1854155413125790002079011897716625099481514342323483307245695840123454623073472699672710144910 = ((1148504657410833284440608587668779155666248184225405704863726330908455569217291479709947850692 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 5 = 1112493247875474001247407138629975059688908605394089984347417504074072773844083619803626086946 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1112493247875474001247407138629975059688908605394089984347417504074072773844083619803626086946 = ((64134290553828539322300395429908966854750532514834125250991538572967316465076832271021204106 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 7 = 794638034196767143748147956164267899777791860995778560248155360052909124174345442716875776390 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 794638034196767143748147956164267899777791860995778560248155360052909124174345442716875776390 = ((2523612606383337294930810904675955568317097786481482904749163998845605618482740172620478432246 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 13 = 427882018413643846633618130242298099880349463613111532441314424643874143786186007616779264210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 427882018413643846633618130242298099880349463613111532441314424643874143786186007616779264210 = ((1964497429657288840644871349015733497987862001485101820861049101150487282201370435953963809517 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 17 = 327203896433962941543355040773522076379090766292379407161005148257080227601201064648125319690 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 327203896433962941543355040773522076379090766292379407161005148257080227601201064648125319690 = ((662509048925326108742283503172463961772887096079463558144217012109036755498925020034383555862 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 53 = 104952193195799434079944069682073118838576283527744338145982783403214412626800341490908121410 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 104952193195799434079944069682073118838576283527744338145982783403214412626800341490908121410 = ((807124117453346232919122871885059055055777664772752405048564378809476404981695731033954440126 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 79 = 70410965055409746914392856875314877195500544645195568629583386333802074293929343025545954870 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 70410965055409746914392856875314877195500544645195568629583386333802074293929343025545954870 = ((4942426453298087275995734738762103249677305014680653006648719635346430683396253860344988299235 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 157 = 35429721269919554179853730529617040117481165776881846635268073378155183880384828656166435890 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 35429721269919554179853730529617040117481165776881846635268073378155183880384828656166435890 = ((5118746375564093776493183768967647026358798417168845965800946080778421954823710739948674340839 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 241 = 23080772777499460606792679224688279246657854883694812953265923321038854229130365556091827530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 23080772777499460606792679224688279246657854883694812953265923321038854229130365556091827530 = ((1190289953441627444766027962273950824114996786959264696222528604119478894653846822357151414920 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 313 = 17771457633793514396923436719328675074902693376902395916092931374985188080576415651815113210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 17771457633793514396923436719328675074902693376902395916092931374985188080576415651815113210 = ((5562466239377370006237035693149875298444543026970449921737087520370363869219841638265827011243 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 1249 = 4453535820158022422927970931264912168490426762986749336859157342170027117069990471591777770 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 4453535820158022422927970931264912168490426762986749336859157342170027117069990471591777770 = ((1240246910053325187569073588705511250097474499074471688950411692796605522043238780203692333326 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 1613 = 3448522157084544331207089704370660445408892143193087366235020161419940402492509670810992210 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 3448522157084544331207089704370660445408892143193087366235020161419940402492509670810992210 = ((1752915670359520218124682744265679413251468294908754357228809853101247220183812265021322015006 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 2731 = 2036787345066777739376431963804421566621949112768381516564294222032355865697699779940728830 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 2036787345066777739376431963804421566621949112768381516564294222032355865697699779940728830 = ((364578046764427133811116089391640525672155862137977927795022696736924764242266802901980247823 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 3121 = 1782270502844399233014109481944849502865922148981239962107365434274387654348099358865149130 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 1782270502844399233014109481944849502865922148981239962107365434274387654348099358865149130 = ((1959121451270987998626504546907139138797261668605801021124960942376432891314256784910963622205 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 8191 = 679094889436866073280067841917943510980898916734275414691379260208810141523674532904179030 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 679094889436866073280067841917943510980898916734275414691379260208810141523674532904179030 = ((4899418649307493505685239241355456611554468578147396250593043907496998442512956526378681639114 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 21841 = 254680016454254384242344017817401918339111900873149119625341674848695749701040158372699530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 254680016454254384242344017817401918339111900873149119625341674848695749701040158372699530 = ((260584756137046828058080426314459465124248848232284802396987498225481043865867099429088689314 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 121369 = 45831029664719739029216980391614623985074796916596906308341401184572369132318945521658170 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 45831029664719739029216980391614623985074796916596906308341401184572369132318945521658170 = ((3128795496370520344992407813013770333363989257365549840894728419796942140074601972085631235633 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 858001 = 6483053329048998784659966239141767082374662764927371788304544540589537622007920852094730 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 6483053329048998784659966239141767082374662764927371788304544540589537622007920852094730 = ((1917588924765716630815125116354718840833852817288658825307571276113488896612225349488460600483 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 22366891 = 248691972405881980031871022805533200767354883026454142497367538491172683285326427308030 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 248691972405881980031871022805533200767354883026454142497367538491172683285326427308030 = ((525002842868030329039464996228210703213682624362731244788674565290945043926129844058957394125 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_308761441).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 308761441 = 18015417408864113981891397161700237363656244326733952254540383235128002493097634231530 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 18015417408864113981891397161700237363656244326733952254540383235128002493097634231530 = ((3694600170349377137466168278447248975685304982674608247806615879735738514191222276019948895194 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_84159375948762099254554456081).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1) / 84159375948762099254554456081 = 66094433052401790702470203697203715578808419128233868549360888330 from by norm_num]
      have h2 : (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) ^ 66094433052401790702470203697203715578808419128233868549360888330 = ((703138134328676702400538470149617951556345484969042910801983515034314942029246730771554676983 : ℕ) : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_326330579 : Nat.Prime 326330579 := by
  refine lucas_primality 326330579 (7 : ZMod 326330579) ?_ (fun q hq hd => ?_)
  · rw [show 326330579 - 1 = 326330578 from by norm_num]
    reduce_mod_char
  · have e : 326330579 - 1 = [2 ^ 1, 7 ^ 1, 23 ^ 2, 139 ^ 1, 317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 2 = 163165289 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 163165289 = ((326330578 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 7 = 46618654 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 46618654 = ((20452803 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 23 = 14188286 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 14188286 = ((96455745 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 139 = 2347702 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 2347702 = ((253936550 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (326330579 - 1) / 317 = 1029434 from by norm_num]
      have h2 : (7 : ZMod 326330579) ^ 1029434 = ((324233427 : ℕ) : ZMod 326330579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12239719573537 : Nat.Prime 12239719573537 := by
  refine lucas_primality 12239719573537 (5 : ZMod 12239719573537) ?_ (fun q hq hd => ?_)
  · rw [show 12239719573537 - 1 = 12239719573536 from by norm_num]
    reduce_mod_char
  · have e : 12239719573537 - 1 = [2 ^ 5, 3 ^ 6, 7 ^ 1, 13 ^ 1, 41 ^ 1, 140627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 2 = 6119859786768 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 6119859786768 = ((12239719573536 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 3 = 4079906524512 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 4079906524512 = ((9858806733279 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 7 = 1748531367648 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 1748531367648 = ((5872900686124 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 13 = 941516890272 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 941516890272 = ((8823581046230 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 41 = 298529745696 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 298529745696 = ((6812326238690 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12239719573537 - 1) / 140627 = 87036768 from by norm_num]
      have h2 : (5 : ZMod 12239719573537) ^ 87036768 = ((4440558378602 : ℕ) : ZMod 12239719573537) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70084436712553223 : Nat.Prime 70084436712553223 := by
  refine lucas_primality 70084436712553223 (5 : ZMod 70084436712553223) ?_ (fun q hq hd => ?_)
  · rw [show 70084436712553223 - 1 = 70084436712553222 from by norm_num]
    reduce_mod_char
  · have e : 70084436712553223 - 1 = [2 ^ 1, 173 ^ 1, 3181 ^ 1, 37987 ^ 1, 1676281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 2 = 35042218356276611 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 35042218356276611 = ((70084436712553222 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 173 = 405112350939614 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 405112350939614 = ((4503599627370496 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 3181 = 22032202676062 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 22032202676062 = ((25063569565806733 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 37987 = 1844958451906 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 1844958451906 = ((54191323626226478 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70084436712553223 - 1) / 1676281 = 41809479862 from by norm_num]
      have h2 : (5 : ZMod 70084436712553223) ^ 41809479862 = ((64078222363299230 : ℕ) : ZMod 70084436712553223) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47635010587 : Nat.Prime 47635010587 := by
  refine lucas_primality 47635010587 (3 : ZMod 47635010587) ?_ (fun q hq hd => ?_)
  · rw [show 47635010587 - 1 = 47635010586 from by norm_num]
    reduce_mod_char
  · have e : 47635010587 - 1 = [2 ^ 1, 3 ^ 2, 173 ^ 1, 2437 ^ 1, 6277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 2 = 23817505293 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 23817505293 = ((47635010586 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 3 = 15878336862 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 15878336862 = ((40922807174 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 173 = 275346882 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 275346882 = ((47601456155 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 2437 = 19546578 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 19546578 = ((30710277692 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 6277 = 7588818 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 7588818 = ((35717200669 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_35374479827 : Nat.Prime 35374479827 := by
  refine lucas_primality 35374479827 (7 : ZMod 35374479827) ?_ (fun q hq hd => ?_)
  · rw [show 35374479827 - 1 = 35374479826 from by norm_num]
    reduce_mod_char
  · have e : 35374479827 - 1 = [2 ^ 1, 7 ^ 1, 23 ^ 1, 173 ^ 1, 635021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 2 = 17687239913 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 17687239913 = ((35374479826 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 7 = 5053497118 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 5053497118 = ((16285941327 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 23 = 1538020862 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 1538020862 = ((12909266343 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 173 = 204476762 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 204476762 = ((1474550170 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (35374479827 - 1) / 635021 = 55706 from by norm_num]
      have h2 : (7 : ZMod 35374479827) ^ 55706 = ((16123704047 : ℕ) : ZMod 35374479827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_179299534877 : Nat.Prime 179299534877 := by
  refine lucas_primality 179299534877 (2 : ZMod 179299534877) ?_ (fun q hq hd => ?_)
  · rw [show 179299534877 - 1 = 179299534876 from by norm_num]
    reduce_mod_char
  · have e : 179299534877 - 1 = [2 ^ 2, 7 ^ 1, 11 ^ 1, 53 ^ 1, 73 ^ 1, 379 ^ 1, 397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 2 = 89649767438 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 89649767438 = ((179299534876 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 7 = 25614219268 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 25614219268 = ((97433609777 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 11 = 16299957716 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 16299957716 = ((143566895690 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 53 = 3383010092 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 3383010092 = ((154769305081 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 73 = 2456158012 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 2456158012 = ((67327353113 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 379 = 473085844 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 473085844 = ((102841375754 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (179299534877 - 1) / 397 = 451636108 from by norm_num]
      have h2 : (2 : ZMod 179299534877) ^ 451636108 = ((31482535414 : ℕ) : ZMod 179299534877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_155285743288572277679887 : Nat.Prime 155285743288572277679887 := by
  refine lucas_primality 155285743288572277679887 (7 : ZMod 155285743288572277679887) ?_ (fun q hq hd => ?_)
  · rw [show 155285743288572277679887 - 1 = 155285743288572277679886 from by norm_num]
    reduce_mod_char
  · have e : 155285743288572277679887 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 37 ^ 2, 83 ^ 1, 173 ^ 1, 1049 ^ 1, 179299534877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 2 = 77642871644286138839943 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 77642871644286138839943 = ((155285743288572277679886 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 3 = 51761914429524092559962 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 51761914429524092559962 = ((45173811239863550073009 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 7 = 22183677612653182525698 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 22183677612653182525698 = ((145819477496274857736139 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 37 = 4196911980772223721078 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 4196911980772223721078 = ((136566097260737592495614 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 83 = 1870912569741834670842 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 1870912569741834670842 = ((120156020248387100991375 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 173 = 897605452535099870982 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 897605452535099870982 = ((64 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 1049 = 148032167100640874814 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 148032167100640874814 = ((139924100744100887877009 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_179299534877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (155285743288572277679887 - 1) / 179299534877 = 866068857318 from by norm_num]
      have h2 : (7 : ZMod 155285743288572277679887) ^ 866068857318 = ((75604042182166458491079 : ℕ) : ZMod 155285743288572277679887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28046273581 : Nat.Prime 28046273581 := by
  refine lucas_primality 28046273581 (2 : ZMod 28046273581) ?_ (fun q hq hd => ?_)
  · rw [show 28046273581 - 1 = 28046273580 from by norm_num]
    reduce_mod_char
  · have e : 28046273581 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 13 ^ 1, 307 ^ 1, 39041 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 2 = 14023136790 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 14023136790 = ((28046273580 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 3 = 9348757860 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 9348757860 = ((22251013166 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 5 = 5609254716 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 5609254716 = ((22358905908 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 13 = 2157405660 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 2157405660 = ((6871355745 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 307 = 91355940 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 91355940 = ((8310140850 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28046273581 - 1) / 39041 = 718380 from by norm_num]
      have h2 : (2 : ZMod 28046273581) ^ 718380 = ((18298241638 : ℕ) : ZMod 28046273581) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1643464247728189221623609 : Nat.Prime 1643464247728189221623609 := by
  refine lucas_primality 1643464247728189221623609 (3 : ZMod 1643464247728189221623609) ?_ (fun q hq hd => ?_)
  · rw [show 1643464247728189221623609 - 1 = 1643464247728189221623608 from by norm_num]
    reduce_mod_char
  · have e : 1643464247728189221623609 - 1 = [2 ^ 3, 17 ^ 1, 173 ^ 1, 22541 ^ 1, 110491 ^ 1, 28046273581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 2 = 821732123864094610811804 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 821732123864094610811804 = ((1643464247728189221623608 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 17 = 96674367513422895389624 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 96674367513422895389624 = ((291555683615566311676479 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 173 = 9499793339469301859096 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 9499793339469301859096 = ((4194304 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 22541 = 72909997237398040088 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 72909997237398040088 = ((714575637068173386075171 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 110491 = 14874191090027144488 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 14874191090027144488 = ((178427696342233853775396 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_28046273581).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1643464247728189221623609 - 1) / 28046273581 = 58598310502168 from by norm_num]
      have h2 : (3 : ZMod 1643464247728189221623609) ^ 58598310502168 = ((1058537451063726728928090 : ℕ) : ZMod 1643464247728189221623609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 : Nat.Prime 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 := by
  refine lucas_primality 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ?_ (fun q hq hd => ?_)
  · rw [show 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1 = 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606442 from by norm_num]
    reduce_mod_char
  · have e : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1 = [2 ^ 1, 347 ^ 1, 4153 ^ 1, 730753 ^ 1, 1505447 ^ 1, 35374479827 ^ 1, 47635010587 ^ 1, 70084436712553223 ^ 1, 155285743288572277679887 ^ 1, 1643464247728189221623609 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 2 = 47781221166459823158558768652126811266595103941005856744533100820560893251843433501458719856460951803221 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 47781221166459823158558768652126811266595103941005856744533100820560893251843433501458719856460951803221 = ((95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606442 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 347 = 275396087414754023968638436035313033236859388708967474031891071011878347272872815570367261420524217886 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 275396087414754023968638436035313033236859388708967474031891071011878347272872815570367261420524217886 = ((295147905179352825856 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 4153 = 23010460470243112525190834891464874195326320222011007341455863626564359861229681435809641154086661114 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 23010460470243112525190834891464874195326320222011007341455863626564359861229681435809641154086661114 = ((74797293787698466550751863501757396910657567963487480625152498631695589161160249376584218422897450991778 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 730753 = 130772562456698291101257931618828280599860976119169833704502344350446438815423086874658659920550314 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 130772562456698291101257931618828280599860976119169833704502344350446438815423086874658659920550314 = ((32541282119383636475833603355699798712820715194565271724134958738894487231181265573558099891549724164134 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 1505447 = 63477785888788941966816193000652711475854153538458486741191288461913163667460141076316495840054086 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 63477785888788941966816193000652711475854153538458486741191288461913163667460141076316495840054086 = ((28613855188095900229276816659869554853989989587960776396589459205384840468455481894703443201519013052741 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_35374479827).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 35374479827 = 2701451520991142751740385536560263793506387773293538117559559772438368765718242740873461147246 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 2701451520991142751740385536560263793506387773293538117559559772438368765718242740873461147246 = ((5787781112995194852964444892620204404624229725688165730830993319458933250484764351772718054285457720119 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47635010587).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 47635010587 = 2006138786479024118057923783457846689723256088630198449903541776263776659999650836288738027166 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 2006138786479024118057923783457846689723256088630198449903541776263776659999650836288738027166 = ((13852109047059171500480485738715756626307602158531106897892820855629330643549769120255469894161377114972 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_70084436712553223).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 70084436712553223 = 1363533001269066524213465815356508195351495719511673329015865732696018849832538515198854 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 1363533001269066524213465815356508195351495719511673329015865732696018849832538515198854 = ((62931673970413538746766529349926070678504744039875963370370673208247039552507785073889486433836373666996 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_155285743288572277679887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 155285743288572277679887 = 615397397785146428799856951317872592976325069779811900630357740743364600116099766 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 615397397785146428799856951317872592976325069779811900630357740743364600116099766 = ((75134861385319161114679106953695567577277333364346609619566247886244669224396481010703929437225754777865 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1643464247728189221623609).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 - 1) / 1643464247728189221623609 = 58146955411423477176677745056351683940160605230824674265581295625654125614687738 from by norm_num]
      have h2 : (5 : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) ^ 58146955411423477176677745056351683940160605230824674265581295625654125614687738 = ((42081577357977622002035050103974842816381499524525597922964868693950441037044553862973460117423412110823 : ℕ) : ZMod 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_131282633 : Nat.Prime 131282633 := by
  refine lucas_primality 131282633 (3 : ZMod 131282633) ?_ (fun q hq hd => ?_)
  · rw [show 131282633 - 1 = 131282632 from by norm_num]
    reduce_mod_char
  · have e : 131282633 - 1 = [2 ^ 3, 13 ^ 1, 349 ^ 1, 3617 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 2 = 65641316 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 65641316 = ((131282632 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 13 = 10098664 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 10098664 = ((54006941 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 349 = 376168 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 376168 = ((55294763 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (131282633 - 1) / 3617 = 36296 from by norm_num]
      have h2 : (3 : ZMod 131282633) ^ 36296 = ((16105574 : ℕ) : ZMod 131282633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3536450843 : Nat.Prime 3536450843 := by
  refine lucas_primality 3536450843 (5 : ZMod 3536450843) ?_ (fun q hq hd => ?_)
  · rw [show 3536450843 - 1 = 3536450842 from by norm_num]
    reduce_mod_char
  · have e : 3536450843 - 1 = [2 ^ 1, 359 ^ 1, 4925419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 2 = 1768225421 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 1768225421 = ((3536450842 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 359 = 9850838 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 9850838 = ((2755820094 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3536450843 - 1) / 4925419 = 718 from by norm_num]
      have h2 : (5 : ZMod 3536450843) ^ 718 = ((686407923 : ℕ) : ZMod 3536450843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15012732261073 : Nat.Prime 15012732261073 := by
  refine lucas_primality 15012732261073 (5 : ZMod 15012732261073) ?_ (fun q hq hd => ?_)
  · rw [show 15012732261073 - 1 = 15012732261072 from by norm_num]
    reduce_mod_char
  · have e : 15012732261073 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 13 ^ 1, 379 ^ 1, 9068551 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 2 = 7506366130536 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 7506366130536 = ((15012732261072 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 3 = 5004244087024 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 5004244087024 = ((13887784478104 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 7 = 2144676037296 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 2144676037296 = ((9947256681909 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 13 = 1154825558544 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 1154825558544 = ((4268161966146 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 379 = 39611430768 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 39611430768 = ((4194304 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15012732261073 - 1) / 9068551 = 1655472 from by norm_num]
      have h2 : (5 : ZMod 15012732261073) ^ 1655472 = ((9790516762563 : ℕ) : ZMod 15012732261073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1492616053 : Nat.Prime 1492616053 := by
  refine lucas_primality 1492616053 (2 : ZMod 1492616053) ?_ (fun q hq hd => ?_)
  · rw [show 1492616053 - 1 = 1492616052 from by norm_num]
    reduce_mod_char
  · have e : 1492616053 - 1 = [2 ^ 2, 3 ^ 3, 409 ^ 1, 33791 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 2 = 746308026 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 746308026 = ((1492616052 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 3 = 497538684 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 497538684 = ((1262591326 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 409 = 3649428 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 3649428 = ((855230646 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1492616053 - 1) / 33791 = 44172 from by norm_num]
      have h2 : (2 : ZMod 1492616053) ^ 44172 = ((676933573 : ℕ) : ZMod 1492616053) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1074456464321 : Nat.Prime 1074456464321 := by
  refine lucas_primality 1074456464321 (13 : ZMod 1074456464321) ?_ (fun q hq hd => ?_)
  · rw [show 1074456464321 - 1 = 1074456464320 from by norm_num]
    reduce_mod_char
  · have e : 1074456464321 - 1 = [2 ^ 6, 5 ^ 1, 179 ^ 1, 389 ^ 1, 48221 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 2 = 537228232160 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 537228232160 = ((1074456464320 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 5 = 214891292864 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 214891292864 = ((129507674464 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 179 = 6002550080 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 6002550080 = ((59277748998 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 389 = 2762098880 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 2762098880 = ((384973636596 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1074456464321 - 1) / 48221 = 22281920 from by norm_num]
      have h2 : (13 : ZMod 1074456464321) ^ 22281920 = ((939390341753 : ℕ) : ZMod 1074456464321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_45592577 : Nat.Prime 45592577 := by
  refine lucas_primality 45592577 (3 : ZMod 45592577) ?_ (fun q hq hd => ?_)
  · rw [show 45592577 - 1 = 45592576 from by norm_num]
    reduce_mod_char
  · have e : 45592577 - 1 = [2 ^ 12, 11131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45592577 - 1) / 2 = 22796288 from by norm_num]
      have h2 : (3 : ZMod 45592577) ^ 22796288 = ((45592576 : ℕ) : ZMod 45592577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45592577 - 1) / 11131 = 4096 from by norm_num]
      have h2 : (3 : ZMod 45592577) ^ 4096 = ((6181419 : ℕ) : ZMod 45592577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1069660739759 : Nat.Prime 1069660739759 := by
  refine lucas_primality 1069660739759 (17 : ZMod 1069660739759) ?_ (fun q hq hd => ?_)
  · rw [show 1069660739759 - 1 = 1069660739758 from by norm_num]
    reduce_mod_char
  · have e : 1069660739759 - 1 = [2 ^ 1, 13 ^ 1, 73 ^ 1, 563 ^ 1, 1001017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 2 = 534830369879 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 534830369879 = ((1069660739758 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 13 = 82281595366 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 82281595366 = ((1144950070 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 73 = 14652886846 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 14652886846 = ((1061627935906 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 563 = 1899930266 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1899930266 = ((368040485674 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 1001017 = 1068574 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1068574 = ((50491089679 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2663848877152141313 : Nat.Prime 2663848877152141313 := by
  refine lucas_primality 2663848877152141313 (3 : ZMod 2663848877152141313) ?_ (fun q hq hd => ?_)
  · rw [show 2663848877152141313 - 1 = 2663848877152141312 from by norm_num]
    reduce_mod_char
  · have e : 2663848877152141313 - 1 = [2 ^ 17, 19 ^ 1, 1069660739759 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 2 = 1331924438576070656 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 1331924438576070656 = ((2663848877152141312 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 19 = 140202572481691648 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 140202572481691648 = ((1712054958658763820 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1069660739759).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 1069660739759 = 2490368 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 2490368 = ((2177351900160986599 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_643620696810643 : Nat.Prime 643620696810643 := by
  refine lucas_primality 643620696810643 (2 : ZMod 643620696810643) ?_ (fun q hq hd => ?_)
  · rw [show 643620696810643 - 1 = 643620696810642 from by norm_num]
    reduce_mod_char
  · have e : 643620696810643 - 1 = [2 ^ 1, 3 ^ 2, 127 ^ 1, 50153 ^ 1, 5613799 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 2 = 321810348405321 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 321810348405321 = ((643620696810642 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 3 = 214540232270214 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 214540232270214 = ((11262356464105 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 127 = 5067879502446 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 5067879502446 = ((371599021910739 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 50153 = 12833144514 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 12833144514 = ((250277297141578 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 5613799 = 114649758 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 114649758 = ((497809978569278 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8717008205877092841673 : Nat.Prime 8717008205877092841673 := by
  refine lucas_primality 8717008205877092841673 (10 : ZMod 8717008205877092841673) ?_ (fun q hq hd => ?_)
  · rw [show 8717008205877092841673 - 1 = 8717008205877092841672 from by norm_num]
    reduce_mod_char
  · have e : 8717008205877092841673 - 1 = [2 ^ 3, 3 ^ 2, 188107 ^ 1, 643620696810643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 2 = 4358504102938546420836 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 4358504102938546420836 = ((8717008205877092841672 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 3 = 2905669401959030947224 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 2905669401959030947224 = ((7343390186032111538464 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 188107 = 46340690170366296 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 46340690170366296 = ((2202464808706072287353 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_643620696810643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 643620696810643 = 13543704 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 13543704 = ((7313602266967842624858 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2937316727 : Nat.Prime 2937316727 := by
  refine lucas_primality 2937316727 (5 : ZMod 2937316727) ?_ (fun q hq hd => ?_)
  · rw [show 2937316727 - 1 = 2937316726 from by norm_num]
    reduce_mod_char
  · have e : 2937316727 - 1 = [2 ^ 1, 2833 ^ 1, 518411 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2 = 1468658363 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1468658363 = ((2937316726 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2833 = 1036822 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1036822 = ((559649464 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 518411 = 5666 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 5666 = ((1096917264 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_761145015334071629 : Nat.Prime 761145015334071629 := by
  refine lucas_primality 761145015334071629 (2 : ZMod 761145015334071629) ?_ (fun q hq hd => ?_)
  · rw [show 761145015334071629 - 1 = 761145015334071628 from by norm_num]
    reduce_mod_char
  · have e : 761145015334071629 - 1 = [2 ^ 2, 13 ^ 1, 1439 ^ 1, 3463 ^ 1, 2937316727 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2 = 380572507667035814 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 380572507667035814 = ((761145015334071628 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 13 = 58549616564159356 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 58549616564159356 = ((338322455532595746 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 1439 = 528940246931252 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 528940246931252 = ((329189789386551514 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 3463 = 219793536047956 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 219793536047956 = ((294223303145502828 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2937316727).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2937316727 = 259129364 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 259129364 = ((48063209786497848 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116928085873074369829035993834596371340386703423373313 : Nat.Prime 116928085873074369829035993834596371340386703423373313 := by
  refine lucas_primality 116928085873074369829035993834596371340386703423373313 (5 : ZMod 116928085873074369829035993834596371340386703423373313) ?_ (fun q hq hd => ?_)
  · rw [show 116928085873074369829035993834596371340386703423373313 - 1 = 116928085873074369829035993834596371340386703423373312 from by norm_num]
    reduce_mod_char
  · have e : 116928085873074369829035993834596371340386703423373313 - 1 = [2 ^ 16, 3 ^ 3, 9959563 ^ 1, 761145015334071629 ^ 1, 8717008205877092841673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 2 = 58464042936537184914517996917298185670193351711686656 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 58464042936537184914517996917298185670193351711686656 = ((116928085873074369829035993834596371340386703423373312 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 3 = 38976028624358123276345331278198790446795567807791104 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 38976028624358123276345331278198790446795567807791104 = ((49067573676489472842253551286141007228252506114172807 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 9959563 = 11740282768739388447970658334567126222343962624 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 11740282768739388447970658334567126222343962624 = ((42667818912291893027423909550891575419819132189033998 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_761145015334071629).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 761145015334071629 = 153621298855585163717133222561251328 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 153621298855585163717133222561251328 = ((113675781698961535315298001192578299458232658608361774 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8717008205877092841673).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 8717008205877092841673 = 13413786371594821026416520658944 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 13413786371594821026416520658944 = ((88896328563985109771361010271091762988159944350705466 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9661881871 : Nat.Prime 9661881871 := by
  refine lucas_primality 9661881871 (11 : ZMod 9661881871) ?_ (fun q hq hd => ?_)
  · rw [show 9661881871 - 1 = 9661881870 from by norm_num]
    reduce_mod_char
  · have e : 9661881871 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 127 ^ 1, 845309 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 2 = 4830940935 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 4830940935 = ((9661881870 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 3 = 3220627290 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 3220627290 = ((3357650980 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 5 = 1932376374 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 1932376374 = ((4559789779 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 127 = 76077810 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 76077810 = ((3475361764 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 845309 = 11430 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 11430 = ((41311167 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_603867617 : Nat.Prime 603867617 := by
  refine lucas_primality 603867617 (3 : ZMod 603867617) ?_ (fun q hq hd => ?_)
  · rw [show 603867617 - 1 = 603867616 from by norm_num]
    reduce_mod_char
  · have e : 603867617 - 1 = [2 ^ 5, 11 ^ 1, 1715533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 2 = 301933808 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 301933808 = ((603867616 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 11 = 54897056 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 54897056 = ((218029995 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 1715533 = 352 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 352 = ((321754386 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1214251009 : Nat.Prime 1214251009 := by
  refine lucas_primality 1214251009 (7 : ZMod 1214251009) ?_ (fun q hq hd => ?_)
  · rw [show 1214251009 - 1 = 1214251008 from by norm_num]
    reduce_mod_char
  · have e : 1214251009 - 1 = [2 ^ 21, 3 ^ 1, 193 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 2 = 607125504 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 607125504 = ((1214251008 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 3 = 404750336 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 404750336 = ((1178454085 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 193 = 6291456 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 6291456 = ((566651089 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_825753601 : Nat.Prime 825753601 := by
  refine lucas_primality 825753601 (23 : ZMod 825753601) ?_ (fun q hq hd => ?_)
  · rw [show 825753601 - 1 = 825753600 from by norm_num]
    reduce_mod_char
  · have e : 825753601 - 1 = [2 ^ 19, 3 ^ 2, 5 ^ 2, 7 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 2 = 412876800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 412876800 = ((825753600 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 3 = 275251200 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 275251200 = ((769286199 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 5 = 165150720 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 165150720 = ((50952529 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 7 = 117964800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 117964800 = ((709772069 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31065037602817 : Nat.Prime 31065037602817 := by
  refine lucas_primality 31065037602817 (5 : ZMod 31065037602817) ?_ (fun q hq hd => ?_)
  · rw [show 31065037602817 - 1 = 31065037602816 from by norm_num]
    reduce_mod_char
  · have e : 31065037602817 - 1 = [2 ^ 19, 3 ^ 1, 7 ^ 1, 2821517 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2 = 15532518801408 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 15532518801408 = ((31065037602816 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 3 = 10355012534272 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 10355012534272 = ((8563864821674 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 7 = 4437862514688 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 4437862514688 = ((8857347445025 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2821517 = 11010048 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 11010048 = ((23804604093954 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70525124609 : Nat.Prime 70525124609 := by
  refine lucas_primality 70525124609 (3 : ZMod 70525124609) ?_ (fun q hq hd => ?_)
  · rw [show 70525124609 - 1 = 70525124608 from by norm_num]
    reduce_mod_char
  · have e : 70525124609 - 1 = [2 ^ 21, 33629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 2 = 35262562304 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 35262562304 = ((70525124608 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 33629 = 2097152 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 2097152 = ((41758406289 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- a an odd multiple of 23: 5 divides 5419 + 1 and 19 + 1 (2^23+1 -> 2796203 -> 5419; 3^13+1 -> 398581 -> 19).
theorem k_d23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 23 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 2 ^ 23 + 1).trans hd)
  have g5419 : 5419 ∈ P := S1 5419 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 31: 5 divides 59 + 1 and 3033169 + 1 (2^31+1 -> 715827883 -> 59; 2^31+1 -> 715827883 -> 3033169).
theorem k_d31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 31 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g715827883 : 715827883 ∈ P := S2 715827883 prime_715827883 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 715827883 ∣ 2 ^ 31 + 1).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  have g3033169 : 3033169 ∈ P := S1 3033169 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 3033169 g3033169 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 40: 17 divides 398581 + 1 and 101 + 1 (3^13+1 -> 398581; 2^40+1 -> 4278255361 -> 2139127681 -> 101).
theorem k_d40 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 40 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g4278255361 : 4278255361 ∈ P := S2 4278255361 prime_4278255361 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4278255361 ∣ 2 ^ 40 + 1).trans hd)
  have g2139127681 : 2139127681 ∈ P := S1 2139127681 prime_2139127681 (by norm_num) (hnz (by norm_num)) 4278255361 g4278255361 (by norm_num)
  have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 2139127681 g2139127681 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 101 g101 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 43: 7 divides 83 + 1 and 13 + 1 (2^43+1 -> 2932031007403 -> 83; 3^13+1 -> 398581 -> 617 -> 103 -> 13).
theorem k_d43 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 43 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2932031007403 : 2932031007403 ∈ P := S2 2932031007403 prime_2932031007403 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2932031007403 ∣ 2 ^ 43 + 1).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 2932031007403 g2932031007403 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 47: 7^2 divides 165768537521 + 1 (2^47+1 -> 165768537521).
theorem k_d47 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 47 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g165768537521 : 165768537521 ∈ P := S2 165768537521 prime_165768537521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 165768537521 ∣ 2 ^ 47 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 165768537521 g165768537521 (by norm_num)

-- a an odd multiple of 49: 19^2 divides 4363953127297 + 1 (2^49+1 -> 4363953127297).
theorem k_d49 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 49 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4363953127297 : 4363953127297 ∈ P := S2 4363953127297 prime_4363953127297 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4363953127297 ∣ 2 ^ 49 + 1).trans hd)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 4363953127297 g4363953127297 (by norm_num)

-- a an odd multiple of 53: 5 divides 19 + 1 and 29 + 1 (3^13+1 -> 398581 -> 19; 2^53+1 -> 28059810762433 -> 1275445943747 -> 29).
theorem k_d53 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 53 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g28059810762433 : 28059810762433 ∈ P := S2 28059810762433 prime_28059810762433 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28059810762433 ∣ 2 ^ 53 + 1).trans hd)
  have g1275445943747 : 1275445943747 ∈ P := S1 1275445943747 prime_1275445943747 (by norm_num) (hnz (by norm_num)) 28059810762433 g28059810762433 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 61: 5^2 divides 1549 + 1 (2^61+1 -> 768614336404564651 -> 37171 -> 9293 -> 1549).
theorem k_d61 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 61 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g768614336404564651 : 768614336404564651 ∈ P := S2 768614336404564651 prime_768614336404564651 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 768614336404564651 ∣ 2 ^ 61 + 1).trans hd)
  have g37171 : 37171 ∈ P := S1 37171 (by norm_num) (by norm_num) (hnz (by norm_num)) 768614336404564651 g768614336404564651 (by norm_num)
  have g9293 : 9293 ∈ P := S1 9293 (by norm_num) (by norm_num) (hnz (by norm_num)) 37171 g37171 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 9293 g9293 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

-- a an odd multiple of 71: 11 divides 131 + 1 and 2243 + 1 (2^71+1 -> 56409643 -> 14102411 -> 131; 2^71+1 -> 56409643 -> 14102411 -> 8971 -> 2243).
theorem k_d71 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 71 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56409643 : 56409643 ∈ P := S2 56409643 prime_56409643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56409643 ∣ 2 ^ 71 + 1).trans hd)
  have g14102411 : 14102411 ∈ P := S1 14102411 (by norm_num) (by norm_num) (hnz (by norm_num)) 56409643 g56409643 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g8971 : 8971 ∈ P := S1 8971 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g2243 : 2243 ∈ P := S1 2243 (by norm_num) (by norm_num) (hnz (by norm_num)) 8971 g8971 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 2243 g2243 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 79: 617 divides 201487636602438195784363 + 1 and 398581 + 1 (2^79+1 -> 201487636602438195784363; 3^13+1 -> 398581).
theorem k_d79 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 79 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g201487636602438195784363 : 201487636602438195784363 ∈ P := S2 201487636602438195784363 prime_201487636602438195784363 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 201487636602438195784363 ∣ 2 ^ 79 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 201487636602438195784363 g201487636602438195784363 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 101: 19 divides 845100400152152934331135470251 + 1 and 398581 + 1 (2^101+1 -> 845100400152152934331135470251; 3^13+1 -> 398581).
theorem k_d101 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 101 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g845100400152152934331135470251 : 845100400152152934331135470251 ∈ P := S2 845100400152152934331135470251 prime_845100400152152934331135470251 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 845100400152152934331135470251 ∣ 2 ^ 101 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 845100400152152934331135470251 g845100400152152934331135470251 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 103: 17 divides 398581 + 1 and 6221 + 1 (3^13+1 -> 398581; 2^103+1 -> 8142767081771726171 -> 6221).
theorem k_d103 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 103 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g8142767081771726171 : 8142767081771726171 ∈ P := S2 8142767081771726171 prime_8142767081771726171 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8142767081771726171 ∣ 2 ^ 103 + 1).trans hd)
  have g6221 : 6221 ∈ P := S1 6221 (by norm_num) (by norm_num) (hnz (by norm_num)) 8142767081771726171 g8142767081771726171 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 6221 g6221 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 104: 11 divides 43 + 1 and 9864985215783886392970452961 + 1 (2^104+1 -> 257 -> 43; 2^104+1 -> 78919881726271091143763623681 -> 39459940863135545571881811841 -> 19729970431567772785940905921 -> 9864985215783886392970452961).
theorem k_d104 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 104 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 104 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g78919881726271091143763623681 : 78919881726271091143763623681 ∈ P := S2 78919881726271091143763623681 prime_78919881726271091143763623681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 78919881726271091143763623681 ∣ 2 ^ 104 + 1).trans hd)
  have g39459940863135545571881811841 : 39459940863135545571881811841 ∈ P := S1 39459940863135545571881811841 prime_39459940863135545571881811841 (by norm_num) (hnz (by norm_num)) 78919881726271091143763623681 g78919881726271091143763623681 (by norm_num)
  have g19729970431567772785940905921 : 19729970431567772785940905921 ∈ P := S1 19729970431567772785940905921 prime_19729970431567772785940905921 (by norm_num) (hnz (by norm_num)) 39459940863135545571881811841 g39459940863135545571881811841 (by norm_num)
  have g9864985215783886392970452961 : 9864985215783886392970452961 ∈ P := S1 9864985215783886392970452961 prime_9864985215783886392970452961 (by norm_num) (hnz (by norm_num)) 19729970431567772785940905921 g19729970431567772785940905921 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 9864985215783886392970452961 g9864985215783886392970452961 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 109: 5^2 divides 104124649 + 1 (2^109+1 -> 104124649).
theorem k_d109 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 109 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g104124649 : 104124649 ∈ P := S2 104124649 prime_104124649 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 104124649 ∣ 2 ^ 109 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 104124649 g104124649 (by norm_num)

-- a an odd multiple of 127: 13^2 divides 1013 + 1 (2^127+1 -> 56713727820156410577229101238628035243 -> 4051 -> 1013).
theorem k_d127 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 127 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56713727820156410577229101238628035243 : 56713727820156410577229101238628035243 ∈ P := S2 56713727820156410577229101238628035243 prime_56713727820156410577229101238628035243 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56713727820156410577229101238628035243 ∣ 2 ^ 127 + 1).trans hd)
  have g4051 : 4051 ∈ P := S1 4051 (by norm_num) (by norm_num) (hnz (by norm_num)) 56713727820156410577229101238628035243 g56713727820156410577229101238628035243 (by norm_num)
  have g1013 : 1013 ∈ P := S1 1013 (by norm_num) (by norm_num) (hnz (by norm_num)) 4051 g4051 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1013 g1013 (by norm_num)

-- a an odd multiple of 128: 7 divides 5704689200685129054721 + 1 and 13 + 1 (2^128+1 -> 5704689200685129054721; 3^13+1 -> 398581 -> 617 -> 103 -> 13).
theorem k_d128 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 128 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5704689200685129054721 : 5704689200685129054721 ∈ P := S2 5704689200685129054721 prime_5704689200685129054721 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5704689200685129054721 ∣ 2 ^ 128 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 5704689200685129054721 g5704689200685129054721 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 139: 17 divides 4506937 + 1 and 398581 + 1 (2^139+1 -> 4506937; 3^13+1 -> 398581).
theorem k_d139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 139 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4506937 : 4506937 ∈ P := S2 4506937 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4506937 ∣ 2 ^ 139 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 151: 7^2 divides 2351 + 1 (2^151+1 -> 18717738334417 -> 2351).
theorem k_d151 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 151 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18717738334417 : 18717738334417 ∈ P := S2 18717738334417 prime_18717738334417 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18717738334417 ∣ 2 ^ 151 + 1).trans hd)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (hnz (by norm_num)) 18717738334417 g18717738334417 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2351 g2351 (by norm_num)

-- a an odd multiple of 163: 13 divides 11281292593 + 1 and 103 + 1 (2^163+1 -> 11281292593; 3^13+1 -> 398581 -> 617 -> 103).
theorem k_d163 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 163 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11281292593 : 11281292593 ∈ P := S2 11281292593 prime_11281292593 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11281292593 ∣ 2 ^ 163 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 11281292593 g11281292593 103 g103 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 167: 11^2 divides 62357403192785191176690552862561408838653121833643 + 1 (2^167+1 -> 62357403192785191176690552862561408838653121833643).
theorem k_d167 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 167 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g62357403192785191176690552862561408838653121833643 : 62357403192785191176690552862561408838653121833643 ∈ P := S2 62357403192785191176690552862561408838653121833643 prime_62357403192785191176690552862561408838653121833643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 62357403192785191176690552862561408838653121833643 ∣ 2 ^ 167 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 62357403192785191176690552862561408838653121833643 g62357403192785191176690552862561408838653121833643 (by norm_num)

-- a an odd multiple of 179: 5 divides 359 + 1 and 19 + 1 (2^179+1 -> 58745093521 -> 359; 3^13+1 -> 398581 -> 19).
theorem k_d179 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 179 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58745093521 : 58745093521 ∈ P := S2 58745093521 prime_58745093521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58745093521 ∣ 2 ^ 179 + 1).trans hd)
  have g359 : 359 ∈ P := S1 359 (by norm_num) (by norm_num) (hnz (by norm_num)) 58745093521 g58745093521 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 359 g359 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 184: 17 divides 43717618369 + 1 and 398581 + 1 (2^184+1 -> 43717618369; 3^13+1 -> 398581).
theorem k_d184 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 184 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43717618369 : 43717618369 ∈ P := S2 43717618369 prime_43717618369 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43717618369 ∣ 2 ^ 184 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 43717618369 g43717618369 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 191: 19 divides 1046183622564446793972631570534611069350392574077339085483 + 1 and 398581 + 1 (2^191+1 -> 1046183622564446793972631570534611069350392574077339085483; 3^13+1 -> 398581).
theorem k_d191 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 191 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1046183622564446793972631570534611069350392574077339085483 : 1046183622564446793972631570534611069350392574077339085483 ∈ P := S2 1046183622564446793972631570534611069350392574077339085483 prime_1046183622564446793972631570534611069350392574077339085483 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1046183622564446793972631570534611069350392574077339085483 ∣ 2 ^ 191 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046183622564446793972631570534611069350392574077339085483 g1046183622564446793972631570534611069350392574077339085483 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 193: 5 divides 35679139 + 1 and 19 + 1 (2^193+1 -> 35679139; 3^13+1 -> 398581 -> 19).
theorem k_d193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 193 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g35679139 : 35679139 ∈ P := S2 35679139 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 35679139 ∣ 2 ^ 193 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 35679139 g35679139 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 197: 5^2 divides 197002597249 + 1 (2^197+1 -> 197002597249).
theorem k_d197 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 197 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g197002597249 : 197002597249 ∈ P := S2 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 197002597249 ∣ 2 ^ 197 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a an odd multiple of 199: 5^2 divides 197002597249 + 1 (2^199+1 -> 267823007376498379256993682056860433753700498963798805883563 -> 197002597249).
theorem k_d199 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 199 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g267823007376498379256993682056860433753700498963798805883563 : 267823007376498379256993682056860433753700498963798805883563 ∈ P := S2 267823007376498379256993682056860433753700498963798805883563 prime_267823007376498379256993682056860433753700498963798805883563 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 267823007376498379256993682056860433753700498963798805883563 ∣ 2 ^ 199 + 1).trans hd)
  have g197002597249 : 197002597249 ∈ P := S1 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num)) 267823007376498379256993682056860433753700498963798805883563 g267823007376498379256993682056860433753700498963798805883563 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a an odd multiple of 211: 7 divides 32381 + 1 and 82529 + 1 (2^211+1 -> 5344743097 -> 32381; 2^211+1 -> 5344743097 -> 82529).
theorem k_d211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 211 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5344743097 : 5344743097 ∈ P := S2 5344743097 prime_5344743097 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5344743097 ∣ 2 ^ 211 + 1).trans hd)
  have g32381 : 32381 ∈ P := S1 32381 (by norm_num) (by norm_num) (hnz (by norm_num)) 5344743097 g5344743097 (by norm_num)
  have g82529 : 82529 ∈ P := S1 82529 (by norm_num) (by norm_num) (hnz (by norm_num)) 5344743097 g5344743097 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 32381 g32381 82529 g82529 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 223: 5 divides 2030149279 + 1 and 19 + 1 (2^223+1 -> 219256122131 -> 2030149279; 3^13+1 -> 398581 -> 19).
theorem k_d223 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 223 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g219256122131 : 219256122131 ∈ P := S2 219256122131 prime_219256122131 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 219256122131 ∣ 2 ^ 223 + 1).trans hd)
  have g2030149279 : 2030149279 ∈ P := S1 2030149279 prime_2030149279 (by norm_num) (hnz (by norm_num)) 219256122131 g219256122131 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2030149279 g2030149279 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 229: 5 divides 19 + 1 and 29 + 1 (3^13+1 -> 398581 -> 19; 2^229+1 -> 18754643 -> 1562887 -> 347 -> 29).
theorem k_d229 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 229 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g18754643 : 18754643 ∈ P := S2 18754643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18754643 ∣ 2 ^ 229 + 1).trans hd)
  have g1562887 : 1562887 ∈ P := S1 1562887 (by norm_num) (by norm_num) (hnz (by norm_num)) 18754643 g18754643 (by norm_num)
  have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 1562887 g1562887 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 251: 31 divides 238451 + 1 and 5058345723951854688505665428846313806490903121677364358901199128608233 + 1 (2^251+1 -> 238451; 2^251+1 -> 5058345723951854688505665428846313806490903121677364358901199128608233).
theorem k_d251 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 251 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g238451 : 238451 ∈ P := S2 238451 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 238451 ∣ 2 ^ 251 + 1).trans hd)
  have g5058345723951854688505665428846313806490903121677364358901199128608233 : 5058345723951854688505665428846313806490903121677364358901199128608233 ∈ P := S2 5058345723951854688505665428846313806490903121677364358901199128608233 prime_5058345723951854688505665428846313806490903121677364358901199128608233 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5058345723951854688505665428846313806490903121677364358901199128608233 ∣ 2 ^ 251 + 1).trans hd)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 238451 g238451 5058345723951854688505665428846313806490903121677364358901199128608233 g5058345723951854688505665428846313806490903121677364358901199128608233 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 256: 5^2 divides 149 + 1 (2^256+1 -> 1238926361552897 -> 206487726925483 -> 11621 -> 149).
theorem k_d256 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 256 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1238926361552897 : 1238926361552897 ∈ P := S2 1238926361552897 prime_1238926361552897 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1238926361552897 ∣ 2 ^ 256 + 1).trans hd)
  have g206487726925483 : 206487726925483 ∈ P := S1 206487726925483 prime_206487726925483 (by norm_num) (hnz (by norm_num)) 1238926361552897 g1238926361552897 (by norm_num)
  have g11621 : 11621 ∈ P := S1 11621 (by norm_num) (by norm_num) (hnz (by norm_num)) 206487726925483 g206487726925483 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 11621 g11621 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- a an odd multiple of 257: 7 divides 37239639534523 + 1 and 13 + 1 (2^257+1 -> 37239639534523; 2^257+1 -> 37239639534523 -> 1329987126233 -> 13).
theorem k_d257 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 257 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37239639534523 : 37239639534523 ∈ P := S2 37239639534523 prime_37239639534523 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 257 = 2 ^ 256 * 2 ^ 1 from pow_add 2 256 1]; norm_num : 37239639534523 ∣ 2 ^ 257 + 1).trans hd)
  have g1329987126233 : 1329987126233 ∈ P := S1 1329987126233 prime_1329987126233 (by norm_num) (hnz (by norm_num)) 37239639534523 g37239639534523 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1329987126233 g1329987126233 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 37239639534523 g37239639534523 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 277: 19 divides 398581 + 1 and 113 + 1 (3^13+1 -> 398581; 2^277+1 -> 25792643401363 -> 113).
theorem k_d277 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 277 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g25792643401363 : 25792643401363 ∈ P := S2 25792643401363 prime_25792643401363 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 277 = 2 ^ 256 * 2 ^ 21 from pow_add 2 256 21]; norm_num : 25792643401363 ∣ 2 ^ 277 + 1).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 25792643401363 g25792643401363 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 113 g113 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 281: 29^2 divides 144542669 + 1 (2^281+1 -> 5203536083 -> 144542669).
theorem k_d281 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 281 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5203536083 : 5203536083 ∈ P := S2 5203536083 prime_5203536083 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 281 = 2 ^ 256 * 2 ^ 25 from pow_add 2 256 25]; norm_num : 5203536083 ∣ 2 ^ 281 + 1).trans hd)
  have g144542669 : 144542669 ∈ P := S1 144542669 prime_144542669 (by norm_num) (hnz (by norm_num)) 5203536083 g5203536083 (by norm_num)
  exact S6 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 144542669 g144542669 (by norm_num)

-- a an odd multiple of 307: 5^2 divides 1249678499 + 1 (2^307+1 -> 1249678499).
theorem k_d307 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 307 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1249678499 : 1249678499 ∈ P := S2 1249678499 prime_1249678499 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 307 = 2 ^ 256 * 2 ^ 51 from pow_add 2 256 51]; norm_num : 1249678499 ∣ 2 ^ 307 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1249678499 g1249678499 (by norm_num)

-- a an odd multiple of 313: 19 divides 398581 + 1 and 64067 + 1 (3^13+1 -> 398581; 2^313+1 -> 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 -> 64067).
theorem k_d313 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 313 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 ∈ P := S2 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 313 = 2 ^ 256 * 2 ^ 57 from pow_add 2 256 57]; norm_num : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 ∣ 2 ^ 313 + 1).trans hd)
  have g64067 : 64067 ∈ P := S1 64067 (by norm_num) (by norm_num) (hnz (by norm_num)) 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 64067 g64067 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 317: 13^2 divides 337 + 1 (2^317+1 -> 326330579 -> 337).
theorem k_d317 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 317 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g326330579 : 326330579 ∈ P := S2 326330579 prime_326330579 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 317 = 2 ^ 256 * 2 ^ 61 from pow_add 2 256 61]; norm_num : 326330579 ∣ 2 ^ 317 + 1).trans hd)
  have g337 : 337 ∈ P := S1 337 (by norm_num) (by norm_num) (hnz (by norm_num)) 326330579 g326330579 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 337 g337 (by norm_num)

-- a an odd multiple of 328: 7 divides 83 + 1 and 13 + 1 (2^328+1 -> 12239719573537 -> 83; 3^13+1 -> 398581 -> 617 -> 103 -> 13).
theorem k_d328 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 328 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12239719573537 : 12239719573537 ∈ P := S2 12239719573537 prime_12239719573537 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 328 = 2 ^ 256 * 2 ^ 72 from pow_add 2 256 72]; norm_num : 12239719573537 ∣ 2 ^ 328 + 1).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 12239719573537 g12239719573537 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 347: 11 divides 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 + 1 and 43 + 1 (2^347+1 -> 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443; 2^347+1 -> 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 -> 2796203 -> 43).
theorem k_d347 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 347 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 ∈ P := S2 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 prime_95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 347 = 2 ^ 256 * 2 ^ 91 from pow_add 2 256 91]; norm_num : 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 ∣ 2 ^ 347 + 1).trans hd)
  have g2796203 : 2796203 ∈ P := S1 2796203 (by norm_num) (by norm_num) (hnz (by norm_num)) 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 g95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 g95562442332919646317117537304253622533190207882011713489066201641121786503686867002917439712921903606443 43 g43 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 349: 7^2 divides 130241 + 1 (2^349+1 -> 131282633 -> 3125777 -> 520963 -> 130241).
theorem k_d349 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 349 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g131282633 : 131282633 ∈ P := S2 131282633 prime_131282633 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 349 = 2 ^ 256 * 2 ^ 93 from pow_add 2 256 93]; norm_num : 131282633 ∣ 2 ^ 349 + 1).trans hd)
  have g3125777 : 3125777 ∈ P := S1 3125777 (by norm_num) (by norm_num) (hnz (by norm_num)) 131282633 g131282633 (by norm_num)
  have g520963 : 520963 ∈ P := S1 520963 (by norm_num) (by norm_num) (hnz (by norm_num)) 3125777 g3125777 (by norm_num)
  have g130241 : 130241 ∈ P := S1 130241 (by norm_num) (by norm_num) (hnz (by norm_num)) 520963 g520963 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 130241 g130241 (by norm_num)

-- a an odd multiple of 359: 13 divides 3769 + 1 and 103 + 1 (2^359+1 -> 3536450843 -> 7537 -> 3769; 3^13+1 -> 398581 -> 617 -> 103).
theorem k_d359 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 359 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3536450843 : 3536450843 ∈ P := S2 3536450843 prime_3536450843 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 359 = 2 ^ 256 * 2 ^ 103 from pow_add 2 256 103]; norm_num : 3536450843 ∣ 2 ^ 359 + 1).trans hd)
  have g7537 : 7537 ∈ P := S1 7537 (by norm_num) (by norm_num) (hnz (by norm_num)) 3536450843 g3536450843 (by norm_num)
  have g3769 : 3769 ∈ P := S1 3769 (by norm_num) (by norm_num) (hnz (by norm_num)) 7537 g7537 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 103 g103 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 376: 5^2 divides 3853249 + 1 (2^376+1 -> 3853249).
theorem k_d376 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 376 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3853249 : 3853249 ∈ P := S2 3853249 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 376 = 2 ^ 256 * 2 ^ 120 from pow_add 2 256 120]; norm_num : 3853249 ∣ 2 ^ 376 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3853249 g3853249 (by norm_num)

-- a an odd multiple of 379: 103 divides 1492616053 + 1 and 617 + 1 (2^379+1 -> 15012732261073 -> 1492616053; 3^13+1 -> 398581 -> 617).
theorem k_d379 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 379 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15012732261073 : 15012732261073 ∈ P := S2 15012732261073 prime_15012732261073 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 379 = 2 ^ 256 * 2 ^ 123 from pow_add 2 256 123]; norm_num : 15012732261073 ∣ 2 ^ 379 + 1).trans hd)
  have g1492616053 : 1492616053 ∈ P := S1 1492616053 prime_1492616053 (by norm_num) (hnz (by norm_num)) 15012732261073 g15012732261073 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 1492616053 g1492616053 617 g617 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 389: 5 divides 1019 + 1 and 19 + 1 (2^389+1 -> 1074456464321 -> 1019; 3^13+1 -> 398581 -> 19).
theorem k_d389 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 389 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1074456464321 : 1074456464321 ∈ P := S2 1074456464321 prime_1074456464321 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 389 = 2 ^ 256 * 2 ^ 133 from pow_add 2 256 133]; norm_num : 1074456464321 ∣ 2 ^ 389 + 1).trans hd)
  have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 1074456464321 g1074456464321 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1019 g1019 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 512: 5 divides 1259 + 1 and 19 + 1 (2^512+1 -> 2424833 -> 1259; 3^13+1 -> 398581 -> 19).
theorem k_d512 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 512 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2424833 : 2424833 ∈ P := S2 2424833 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 from pow_add 2 256 256]; norm_num : 2424833 ∣ 2 ^ 512 + 1).trans hd)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 2424833 g2424833 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1259 g1259 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1024: 17 divides 398581 + 1 and 3671 + 1 (3^13+1 -> 398581; 2^1024+1 -> 45592577 -> 36709 -> 3671).
theorem k_d1024 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 1024 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g45592577 : 45592577 ∈ P := S2 45592577 prime_45592577 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1024 = (2 ^ 256) ^ 4 from pow_mul 2 256 4]; norm_num : 45592577 ∣ 2 ^ 1024 + 1).trans hd)
  have g36709 : 36709 ∈ P := S1 36709 (by norm_num) (by norm_num) (hnz (by norm_num)) 45592577 g45592577 (by norm_num)
  have g3671 : 3671 ∈ P := S1 3671 (by norm_num) (by norm_num) (hnz (by norm_num)) 36709 g36709 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 3671 g3671 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 2048: 5^2 divides 974849 + 1 (2^2048+1 -> 974849).
theorem k_d2048 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 2048 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g974849 : 974849 ∈ P := S2 974849 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 2048 = (2 ^ 256) ^ 8 from pow_mul 2 256 8]; norm_num : 974849 ∣ 2 ^ 2048 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 974849 g974849 (by norm_num)

-- a an odd multiple of 4096: 11^2 divides 43801 + 1 (2^4096+1 -> 26017793 -> 43801).
theorem k_d4096 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 4096 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g26017793 : 26017793 ∈ P := S2 26017793 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 4096 = (2 ^ 256) ^ 16 from pow_mul 2 256 16]; norm_num : 26017793 ∣ 2 ^ 4096 + 1).trans hd)
  have g43801 : 43801 ∈ P := S1 43801 (by norm_num) (by norm_num) (hnz (by norm_num)) 26017793 g26017793 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43801 g43801 (by norm_num)

-- a an odd multiple of 8192: 19 divides 398581 + 1 and 37 + 1 (3^13+1 -> 398581; 2^8192+1 -> 2663848877152141313 -> 37).
theorem k_d8192 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 8192 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g2663848877152141313 : 2663848877152141313 ∈ P := S2 2663848877152141313 prime_2663848877152141313 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 8192 = (2 ^ 256) ^ 32 from pow_mul 2 256 32]; norm_num : 2663848877152141313 ∣ 2 ^ 8192 + 1).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 2663848877152141313 g2663848877152141313 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 37 g37 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 16384: 5 divides 19 + 1 and 29 + 1 (3^13+1 -> 398581 -> 19; 2^16384+1 -> 116928085873074369829035993834596371340386703423373313 -> 9661881871 -> 603867617 -> 2551 -> 29).
theorem k_d16384 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 16384 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g116928085873074369829035993834596371340386703423373313 : 116928085873074369829035993834596371340386703423373313 ∈ P := S2 116928085873074369829035993834596371340386703423373313 prime_116928085873074369829035993834596371340386703423373313 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 16384 = (2 ^ 256) ^ 64 from pow_mul 2 256 64]; norm_num : 116928085873074369829035993834596371340386703423373313 ∣ 2 ^ 16384 + 1).trans hd)
  have g9661881871 : 9661881871 ∈ P := S1 9661881871 prime_9661881871 (by norm_num) (hnz (by norm_num)) 116928085873074369829035993834596371340386703423373313 g116928085873074369829035993834596371340386703423373313 (by norm_num)
  have g603867617 : 603867617 ∈ P := S1 603867617 prime_603867617 (by norm_num) (hnz (by norm_num)) 9661881871 g9661881871 (by norm_num)
  have g2551 : 2551 ∈ P := S1 2551 (by norm_num) (by norm_num) (hnz (by norm_num)) 603867617 g603867617 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2551 g2551 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 32768: 17 divides 1214251009 + 1 and 398581 + 1 (2^32768+1 -> 1214251009; 3^13+1 -> 398581).
theorem k_d32768 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 32768 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1214251009 : 1214251009 ∈ P := S2 1214251009 prime_1214251009 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 32768 = (2 ^ 256) ^ 128 from pow_mul 2 256 128]; norm_num : 1214251009 ∣ 2 ^ 32768 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1214251009 g1214251009 398581 g398581 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 65536: 19 divides 398581 + 1 and 113 + 1 (3^13+1 -> 398581; 2^65536+1 -> 825753601 -> 113).
theorem k_d65536 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 65536 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g825753601 : 825753601 ∈ P := S2 825753601 prime_825753601 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 65536 = (2 ^ 256) ^ 256 from pow_mul 2 256 256]; norm_num : 825753601 ∣ 2 ^ 65536 + 1).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 825753601 g825753601 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 113 g113 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 131072: 17 divides 398581 + 1 and 67 + 1 (3^13+1 -> 398581; 2^131072+1 -> 31065037602817 -> 67).
theorem k_d131072 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 131072 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g31065037602817 : 31065037602817 ∈ P := S2 31065037602817 prime_31065037602817 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 131072 = ((2 ^ 256) ^ 256) ^ 2 from by rw [← pow_mul, ← pow_mul]]; norm_num : 31065037602817 ∣ 2 ^ 131072 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 31065037602817 g31065037602817 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 67 g67 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 262144: 5 divides 13631489 + 1 and 16829 + 1 (2^262144+1 -> 13631489; 2^262144+1 -> 13631489 -> 16829).
theorem k_d262144 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 262144 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13631489 : 13631489 ∈ P := S2 13631489 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 262144 = ((2 ^ 256) ^ 256) ^ 4 from by rw [← pow_mul, ← pow_mul]]; norm_num : 13631489 ∣ 2 ^ 262144 + 1).trans hd)
  have g16829 : 16829 ∈ P := S1 16829 (by norm_num) (by norm_num) (hnz (by norm_num)) 13631489 g13631489 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13631489 g13631489 16829 g16829 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 524288: 17^2 divides 3467 + 1 (2^524288+1 -> 70525124609 -> 3467).
theorem k_d524288 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 524288 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g70525124609 : 70525124609 ∈ P := S2 70525124609 prime_70525124609 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 524288 = ((2 ^ 256) ^ 256) ^ 8 from by rw [← pow_mul, ← pow_mul]]; norm_num : 70525124609 ∣ 2 ^ 524288 + 1).trans hd)
  have g3467 : 3467 ∈ P := S1 3467 (by norm_num) (by norm_num) (hnz (by norm_num)) 70525124609 g70525124609 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 3467 g3467 (by norm_num)

-- a is no odd multiple of any d in 1..400 outside the exception list.
theorem sieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p) :
    ∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →
      m % (2 * d) ≠ d := by
  intro d lo hi hex h
  interval_cases d
  · exact absurd (by decide) hex
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact absurd (by decide) hex
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact absurd (by decide) hex
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact absurd (by decide) hex
  · exact absurd (by decide) hex
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d21 hP E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d23 hP E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact k_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact kE13_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k_d49 hP E (two_pow_add_one_dvd_of_odd_mul (d := 49) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2_d56 hP E (two_pow_add_one_dvd_of_odd_mul (d := 56) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d23 hP E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kE13_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kE13_d88 hP E (two_pow_add_one_dvd_of_odd_mul (d := 88) (by omega))
  · exact kE13_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill2_d97 hP E (two_pow_add_one_dvd_of_odd_mul (d := 97) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d101 hP E (two_pow_add_one_dvd_of_odd_mul (d := 101) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d103 hP E (two_pow_add_one_dvd_of_odd_mul (d := 103) (by omega))
  · exact k_d104 hP E (two_pow_add_one_dvd_of_odd_mul (d := 104) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d109 hP E (two_pow_add_one_dvd_of_odd_mul (d := 109) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d23 hP E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d127 hP E (two_pow_add_one_dvd_of_odd_mul (d := 127) (by omega))
  · exact k_d128 hP E (two_pow_add_one_dvd_of_odd_mul (d := 128) (by omega))
  · exact k_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d131 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kE13_d136 hP E (two_pow_add_one_dvd_of_odd_mul (d := 136) (by omega))
  · exact kE13_d137 hP E (two_pow_add_one_dvd_of_odd_mul (d := 137) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d139 hP E (two_pow_add_one_dvd_of_odd_mul (d := 139) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d21 hP E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d149 hP E (two_pow_add_one_dvd_of_odd_mul (d := 149) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d151 hP E (two_pow_add_one_dvd_of_odd_mul (d := 151) (by omega))
  · exact kill2_d152 hP E (two_pow_add_one_dvd_of_odd_mul (d := 152) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d157 hP E (two_pow_add_one_dvd_of_odd_mul (d := 157) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact k_d23 hP E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d163 hP E (two_pow_add_one_dvd_of_odd_mul (d := 163) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d167 hP E (two_pow_add_one_dvd_of_odd_mul (d := 167) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d173 hP E (two_pow_add_one_dvd_of_odd_mul (d := 173) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d179 hP E (two_pow_add_one_dvd_of_odd_mul (d := 179) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d181 hP E (two_pow_add_one_dvd_of_odd_mul (d := 181) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact k_d184 hP E (two_pow_add_one_dvd_of_odd_mul (d := 184) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d191 hP E (two_pow_add_one_dvd_of_odd_mul (d := 191) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact k_d193 hP E (two_pow_add_one_dvd_of_odd_mul (d := 193) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d197 hP E (two_pow_add_one_dvd_of_odd_mul (d := 197) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d199 hP E (two_pow_add_one_dvd_of_odd_mul (d := 199) (by omega))
  · exact k_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d211 hP E (two_pow_add_one_dvd_of_odd_mul (d := 211) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d223 hP E (two_pow_add_one_dvd_of_odd_mul (d := 223) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d229 hP E (two_pow_add_one_dvd_of_odd_mul (d := 229) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kE13_d232 hP E (two_pow_add_one_dvd_of_odd_mul (d := 232) (by omega))
  · exact kE13_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d239 hP E (two_pow_add_one_dvd_of_odd_mul (d := 239) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d241 hP E (two_pow_add_one_dvd_of_odd_mul (d := 241) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kE13_d248 hP E (two_pow_add_one_dvd_of_odd_mul (d := 248) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d251 hP E (two_pow_add_one_dvd_of_odd_mul (d := 251) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k_d256 hP E (two_pow_add_one_dvd_of_odd_mul (d := 256) (by omega))
  · exact k_d257 hP E (two_pow_add_one_dvd_of_odd_mul (d := 257) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d263 hP E (two_pow_add_one_dvd_of_odd_mul (d := 263) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact absurd (by decide) hex
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d271 hP E (two_pow_add_one_dvd_of_odd_mul (d := 271) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d277 hP E (two_pow_add_one_dvd_of_odd_mul (d := 277) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact k_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact k_d281 hP E (two_pow_add_one_dvd_of_odd_mul (d := 281) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d283 hP E (two_pow_add_one_dvd_of_odd_mul (d := 283) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d97 hP E (two_pow_add_one_dvd_of_odd_mul (d := 97) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d293 hP E (two_pow_add_one_dvd_of_odd_mul (d := 293) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact kE13_d296 hP E (two_pow_add_one_dvd_of_odd_mul (d := 296) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d101 hP E (two_pow_add_one_dvd_of_odd_mul (d := 101) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d307 hP E (two_pow_add_one_dvd_of_odd_mul (d := 307) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d103 hP E (two_pow_add_one_dvd_of_odd_mul (d := 103) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d311 hP E (two_pow_add_one_dvd_of_odd_mul (d := 311) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k_d313 hP E (two_pow_add_one_dvd_of_odd_mul (d := 313) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d317 hP E (two_pow_add_one_dvd_of_odd_mul (d := 317) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact kE13_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d109 hP E (two_pow_add_one_dvd_of_odd_mul (d := 109) (by omega))
  · exact k_d328 hP E (two_pow_add_one_dvd_of_odd_mul (d := 328) (by omega))
  · exact k_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d331 hP E (two_pow_add_one_dvd_of_odd_mul (d := 331) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d337 hP E (two_pow_add_one_dvd_of_odd_mul (d := 337) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d49 hP E (two_pow_add_one_dvd_of_odd_mul (d := 49) (by omega))
  · exact kE13_d344 hP E (two_pow_add_one_dvd_of_odd_mul (d := 344) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d347 hP E (two_pow_add_one_dvd_of_odd_mul (d := 347) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d349 hP E (two_pow_add_one_dvd_of_odd_mul (d := 349) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact absurd (by decide) hex
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d359 hP E (two_pow_add_one_dvd_of_odd_mul (d := 359) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d367 hP E (two_pow_add_one_dvd_of_odd_mul (d := 367) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d373 hP E (two_pow_add_one_dvd_of_odd_mul (d := 373) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k_d376 hP E (two_pow_add_one_dvd_of_odd_mul (d := 376) (by omega))
  · exact kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d379 hP E (two_pow_add_one_dvd_of_odd_mul (d := 379) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d127 hP E (two_pow_add_one_dvd_of_odd_mul (d := 127) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact absurd (by decide) hex
  · exact k_d128 hP E (two_pow_add_one_dvd_of_odd_mul (d := 128) (by omega))
  · exact kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact k_d389 hP E (two_pow_add_one_dvd_of_odd_mul (d := 389) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d56 hP E (two_pow_add_one_dvd_of_odd_mul (d := 56) (by omega))
  · exact kill2_d131 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact k_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega))
  · exact kE13_d397 hP E (two_pow_add_one_dvd_of_odd_mul (d := 397) (by omega))
  · exact kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega))
  · exact kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))

-- a is no odd multiple of 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288 (factors of Fermat numbers).
theorem fermat {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p) :
    ∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k_d512 hP E (two_pow_add_one_dvd_of_odd_mul (d := 512) h)
  · exact k_d1024 hP E (two_pow_add_one_dvd_of_odd_mul (d := 1024) h)
  · exact k_d2048 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2048) h)
  · exact k_d4096 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4096) h)
  · exact k_d8192 hP E (two_pow_add_one_dvd_of_odd_mul (d := 8192) h)
  · exact k_d16384 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16384) h)
  · exact k_d32768 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32768) h)
  · exact k_d65536 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65536) h)
  · exact k_d131072 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131072) h)
  · exact k_d262144 hP E (two_pow_add_one_dvd_of_odd_mul (d := 262144) h)
  · exact k_d524288 hP E (two_pow_add_one_dvd_of_odd_mul (d := 524288) h)

-- Section 2. Small a, the classes of a, and the count for odd a.

-- Small a.  One more simple prime q with 2^i dividing q + 1 joins the 2-adic count.
theorem two_cons {j i q : ℕ} {P S : Finset ℕ}
    (h : S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) (hq : q ∈ P) (hqS : q ∉ S)
    (h2 : 2 ^ i ∣ q + 1) :
    insert q S ⊆ P ∧ 2 ^ (j + i) ∣ ∏ p ∈ insert q S, (p + 1) := by
  refine ⟨Finset.insert_subset hq h.1, ?_⟩
  rw [Finset.prod_insert hqS, pow_add, mul_comm]
  exact mul_dvd_mul h2 h.2

-- The left side of the balance equation holds exactly a + 1 factors of 2; 3^e + 1 gives two.
theorem two_budget {m e j : ℕ} {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (h4 : 4 ∣ 1 + 3 ^ e) (h : S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) (hj : m ≤ j) : False := by
  have h3 : ¬ 2 ∣ 3 ^ e := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
      (Nat.prime_two.dvd_of_dvd_pow hd)
    omega
  apply not_two_pow_dvd hP h3 E
  have h1 : 2 ^ (m + 2) ∣ 2 ^ (j + 2) := pow_dvd_pow 2 (by omega)
  have h2 : 2 ^ (j + 2) ∣ (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) := by
    rw [pow_add, mul_comm]
    exact mul_dvd_mul h4 (h.2.trans (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) h.1))
  rw [mul_assoc]
  exact (h1.trans h2).mul_left _

-- a >= 262: the forced primes 19, 103, 7 already hold 8 factors of 2, so a > 8;
-- every other a below 262 is an odd multiple of a sieved d.
theorem lower {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p) :
    262 ≤ m := by
  by_contra hlt
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 2 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by simp⟩
  have b1 := two_cons b0 g19 (by simp) (by norm_num : 2 ^ 2 ∣ 19 + 1)
  have b2 := two_cons b1 g103 (by simp) (by norm_num : 2 ^ 3 ∣ 103 + 1)
  have b3 := two_cons b2 g7 (by simp) (by norm_num : 2 ^ 3 ∣ 7 + 1)
  have hs := sieve hP h3P E
  by_cases h0 : m ≤ 8
  · exact two_budget hP E (by norm_num) b3 (by omega)
  refine hs m (by omega) (by omega) ?_ (Nat.mod_eq_of_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

-- Pure arithmetic: a multiple of k that is no odd multiple of k is a multiple of 2k.
theorem dbl {m k : ℕ} (hk : 0 < k) (h : m % k = 0) (h2 : m % (2 * k) ≠ k) : m % (2 * k) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · rw [show k * (2 * s) = 2 * k * s from by ring]
    exact Nat.mul_mod_right _ _
  · exfalso
    apply h2
    rw [show k * (2 * s + 1) = 2 * k * s + k from by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)

-- So a multiple of 128 that is no odd multiple of 128, 256, ..., 524288 is a multiple of 2^20.
theorem high_class {m : ℕ} (h : m % 128 = 0)
    (hs : ∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 5, 7, 8, 269, 353, 383} : Finset ℕ) →
      m % (2 * d) ≠ d)
    (hf : ∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288} : Finset ℕ),
      m % (2 * d) ≠ d) :
    m % 1048576 = 0 := by
  have c256 : m % 256 = 0 :=
    dbl (k := 128) (by norm_num) h (hs 128 (by norm_num) (by norm_num) (by simp))
  have c512 : m % 512 = 0 :=
    dbl (k := 256) (by norm_num) c256 (hs 256 (by norm_num) (by norm_num) (by simp))
  have c1024 : m % 1024 = 0 := dbl (k := 512) (by norm_num) c512 (hf 512 (by simp))
  have c2048 : m % 2048 = 0 := dbl (k := 1024) (by norm_num) c1024 (hf 1024 (by simp))
  have c4096 : m % 4096 = 0 := dbl (k := 2048) (by norm_num) c2048 (hf 2048 (by simp))
  have c8192 : m % 8192 = 0 := dbl (k := 4096) (by norm_num) c4096 (hf 4096 (by simp))
  have c16384 : m % 16384 = 0 := dbl (k := 8192) (by norm_num) c8192 (hf 8192 (by simp))
  have c32768 : m % 32768 = 0 := dbl (k := 16384) (by norm_num) c16384 (hf 16384 (by simp))
  have c65536 : m % 65536 = 0 := dbl (k := 32768) (by norm_num) c32768 (hf 32768 (by simp))
  have c131072 : m % 131072 = 0 := dbl (k := 65536) (by norm_num) c65536 (hf 65536 (by simp))
  have c262144 : m % 262144 = 0 := dbl (k := 131072) (by norm_num) c131072 (hf 131072 (by simp))
  have c524288 : m % 524288 = 0 := dbl (k := 262144) (by norm_num) c262144 (hf 262144 (by simp))
  have c1048576 : m % 1048576 = 0 := dbl (k := 524288) (by norm_num) c524288 (hf 524288 (by simp))
  exact c1048576

-- Uniform count for odd a (no factorization needed).  For an odd prime p = 2 mod 3 the number
-- (2^p + 1) / 3 is 2 mod 3, so 2^p + 1 has a prime factor q = 2 mod 3.
theorem root_mod3 {p : ℕ} (hp2 : p % 2 = 1) (hp3 : p % 3 = 2) :
    ∃ q, q.Prime ∧ q ∣ 2 ^ p + 1 ∧ q % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 6 * k + 5 := ⟨p / 6, by omega⟩
  have h9 : (2 ^ (6 * k + 5) + 1) % 9 = 6 := by
    have h1 : (2 ^ (6 * k)) % 9 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    rw [pow_add, Nat.add_mod, Nat.mul_mod, h1]
    norm_num
  obtain ⟨q, hq, hqd, hq3⟩ := exists_prime_mod3 ((2 ^ (6 * k + 5) + 1) / 3) (by omega)
  exact ⟨q, hq, hqd.trans (Nat.div_dvd_of_dvd (by omega)), hq3⟩

-- Two different odd primes p, p' cannot share such a factor: it would divide 2^2 - 1 = 3.
theorem root_inj {p p' q : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') (hq : q.Prime)
    (hq3 : q % 3 = 2) (h : q ∣ 2 ^ p + 1) (h' : q ∣ 2 ^ p' + 1) : False := by
  have key : ∀ r : ℕ, q ∣ 2 ^ r + 1 → q ∣ 2 ^ (2 * r) - 1 := by
    intro r hr
    have e1 : 2 ^ (2 * r) - 1 = (2 ^ r + 1) * (2 ^ r - 1) := by
      have := Nat.sq_sub_sq (2 ^ r) 1
      rw [mul_comm 2 r, pow_mul]
      simpa using this
    rw [e1]
    exact hr.mul_right _
  have hg := Nat.dvd_gcd (key p h) (key p' h')
  rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left,
    (Nat.coprime_primes hp hp').mpr hne] at hg
  have h3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (by simpa using hg)
  omega

-- Kernel 3^e, a = m odd: 1 + (number of primes p = 2 mod 3 dividing m) + j <= e, where 3^j
-- divides the product of x + 1 over a set X of simple primes not dividing 2^m + 1.
theorem odd_ledger {m e j : ℕ} {P T X : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (hT : ∀ p ∈ T, p.Prime ∧ p % 3 = 2 ∧ p ∣ m)
    (hX : X ⊆ P) (hXr : ∀ x ∈ X, ¬ x ∣ 2 ^ m + 1) (hXj : 3 ^ j ∣ ∏ x ∈ X, (x + 1)) :
    1 + T.card + j ≤ e := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hodd : ∀ p ∈ T, p % 2 = 1 := by
    intro p hp
    obtain ⟨t, rfl⟩ := (hT p hp).2.2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0] at hm; simp at hm
    · exact h1
  have hdvd : ∀ p ∈ T, 2 ^ p + 1 ∣ 2 ^ m + 1 := by
    intro p hp
    have hp1 := hodd p hp
    have hpos := (hT p hp).1.pos
    obtain ⟨t, rfl⟩ := (hT p hp).2.2
    have ht : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · rw [Nat.mul_mod, h0] at hm; simp at hm
      · exact h1
    apply two_pow_add_one_dvd_of_odd_mul
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    rw [show p * (2 * s + 1) = 2 * p * s + p from by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : ∀ p : ℕ, ∃ q : ℕ, p ∈ T → q.Prime ∧ q ∣ 2 ^ p + 1 ∧ q % 3 = 2 := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨q, hq⟩ := root_mod3 (hodd p hp) (hT p hp).2.1
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using hex
  have hinj : Set.InjOn f (T : Set ℕ) := by
    intro p hp p' hp' heq
    by_contra hne
    have h1 := hf p hp
    have h2 := hf p' hp'
    rw [← heq] at h2
    exact root_inj (hT p hp).1 (hT p' hp').1 hne h1.1 h1.2.2 h1.2.1 h2.2.1
  have hQd : ∀ q ∈ T.image f, q.Prime ∧ q ∣ 2 ^ m + 1 ∧ q % 3 = 2 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(hf p hp).1, (hf p hp).2.1.trans (hdvd p hp), (hf p hp).2.2⟩
  have hQP : T.image f ⊆ P := by
    intro q hq
    obtain ⟨hqp, hqd, hq3⟩ := hQd q hq
    refine S2 q hqp ?_ ?_ hqd
    · rintro rfl
      have := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : m ≠ 0))).mp hqd
      omega
    · intro h3
      rw [Finset.mem_singleton.mp h3] at hq3
      omega
  have hdisj : Disjoint (T.image f) X := by
    rw [Finset.disjoint_left]
    intro q hq hqX
    exact hXr q hqX (hQd q hq).2.1
  have h3Q : 3 ^ T.card ∣ ∏ q ∈ T.image f, (q + 1) := by
    rw [← Finset.card_image_of_injOn hinj, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => by
      have := (hQd q hq).2.2
      omega)
  by_contra hlt
  refine budget_kernel3 hP h3P E (Finset.union_subset hQP hX) ?_
  rw [Finset.prod_union hdisj]
  have h3 : 3 ^ (1 + T.card + j) ∣ (2 ^ m + 1) * ((∏ q ∈ T.image f, (q + 1)) * ∏ x ∈ X, (x + 1)) := by
    rw [pow_add, pow_add, pow_one, mul_assoc]
    exact mul_dvd_mul (three_dvd_two_pow_add_one hm) (mul_dvd_mul h3Q hXj)
  exact (pow_dvd_pow 3 (by omega)).trans h3

-- a odd: at most 8 primes p = 2 mod 3 divide a, since 17, 617, 5 already use 4 factors of 3.
theorem odd_count {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) : (m.primeFactors.filter (fun p => p % 3 = 2)).card ≤ 8 := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 (by norm_num)
  have h := odd_ledger (j := 4) (T := m.primeFactors.filter (fun p => p % 3 = 2))
    (X := {17, 617, 5}) hP h3P E hm
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩)
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact g17
      · exact g617
      · exact g5)
    (by
      intro x hx hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 398581 g398581 (by norm_num)
      · exact S4 617 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 398581 g398581 (by norm_num)
      · exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 19 g19 (by norm_num))
    (by norm_num [Finset.prod_insert])
  omega

-- The step.
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he _ _ _ => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  have s1 := sieve hP h3P E
  have s2 := fermat hP h3P E
  have s3 := lower hP h3P E
  have s4 := odd_count hP h3P E
  have s5 := core3e13_two_adic_shape hP E
  rw [ha] at s1 s2 s3 s4 s5
  rcases s5 with c | c | c
  · exact (h1 n h hiff he c s3 s1 (s4 c)).trans (le_max_left _ _)
  · exact (h2 n h hiff he c s3 s1).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 n h hiff he (high_class c s1 s2)).trans ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1
