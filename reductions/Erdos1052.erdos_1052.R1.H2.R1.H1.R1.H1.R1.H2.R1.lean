import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.lean
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Builds on the reductions of @adammcarter (R1 and its descendants), whose balance-equation
-- lemmas (kernel_balance_one, facts, two_pow_add_one_dvd_of_odd_mul) are imported, not copied.
--
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1 (3 is the only repeated odd prime and
-- its exponent e is 11, 13 or 19) by the exponent e, with new 2-adic restrictions proved below.
-- Proving the three H proves the step.
--
-- Notation as in the parent file: n unitary perfect with 3 the only repeated odd prime, e =
-- n.factorization 3, a = padicValNat 2 n, P = the set of simple odd primes of n.  A number x is an
-- ODD MULTIPLE of d when x mod 2d = d; then 2^d + 1 divides 2^a + 1 (for x = a).  The balance
-- equation is (2^a + 1)(1 + 3^e) prod_P (p + 1) = 2^(a+1) 3^e prod_P p.
--
-- PROVED BELOW (no hypothesis needed): for e = 11, 13, 19, a is no odd multiple of any d in the
-- e-specific sets NEW11, NEW13, NEW19 (theorems new_e11, new_e13, new_e19; one lemma kE<e>_d<d>
-- per d).  These sets contain every d at most 400 that is not already implied by the parent's
-- restrictions (an odd multiple of a parent value) and that a forced chain decides:
--   e = 11: 1 + 3^11 = 4 * 67 * 661, so 67, 661 are simple primes of n, and then so are 17, 331,
--     83, 7 (the odd prime factors of p + 1 for p in P are again in P);
--   e = 13: 1 + 3^13 = 4 * 398581, giving 398581, 17, 19, 617, 103, 13, 7, 5 in P;
--   e = 19: 1 + 3^19 = 4 * 2851 * 101917, giving 2851, 101917, 23, 31, 131, 389, 11, 5, 13, 7 in P.
-- A small prime factor c of 2^d + 1 (c below 2 * 10^6) is in P as well, and the chain it starts
-- ends at an odd prime with two sources in the balance equation (two p + 1, or p + 1 and 2^a + 1,
-- or p + 1 and 1 + 3^e) or at a square c^2 dividing p + 1 or 2^d + 1.  Every prime used is below
-- 4.3 * 10^7, so plain norm_num certifies it.  Example (e = 11, d = 6): 13 | 2^6 + 1 and 7 | 13 + 1,
-- while 661 -> 331 -> 83 and 7 | 83 + 1, so 7 has two sources.
-- Consequences: for e = 19 and a odd, a has no prime factor 5, 7, 11, 13, 17, 19, 41, ...; for
-- e = 13 and a odd, none of 11, 13, 17, 19, 41, ... and 9 does not divide a; for e = 11 and
-- a odd, none of 17, 19, 41, ...; for e = 11, a mod 12 is not 6.
--
-- H1 (OPEN): e = 11, with the parent's restrictions and a no odd multiple of NEW11.
-- H2 (OPEN): e = 13, with the parent's restrictions and a no odd multiple of NEW13.
-- H3 (OPEN): e = 19, with the parent's restrictions and a no odd multiple of NEW19.
-- No known unitary perfect number satisfies the hypotheses of H1, H2 or H3.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 11, a no odd multiple of any d in DA (the parent's
-- list), of 4 or 16, or of any d in NEW11 (the last list).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214,
        218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293,
        296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382,
        386, 394, 395, 397, 398} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the same with e = 13, a no odd multiple of any d in DA, of 2, 4 or 16, or of any d in NEW13.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 13 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({2, 4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({9, 11, 13, 15, 17, 19, 21, 41, 73, 88, 89, 107, 113, 136, 137, 159, 173, 181, 200,
        213, 227, 232, 233, 237, 239, 241, 248, 263, 271, 283, 293, 296, 301, 305, 309, 311, 327,
        329, 331, 337, 344, 367, 373, 381, 395, 397} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: the same with e = 19, a no odd multiple of any d in DA, of 2, 8 or 16, or of any d in NEW19.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 19 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({2, 8, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({5, 7, 9, 11, 13, 17, 19, 41, 44, 73, 89, 107, 113, 129, 137, 159, 173, 181, 193, 211,
        213, 227, 233, 236, 237, 239, 244, 251, 263, 268, 271, 283, 284, 293, 309, 311, 316, 327,
        331, 332, 337, 367, 373, 381, 397} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1. The forced-chain lemmas (generated case by case; each is a short chain of facts).

theorem kE11_d6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 6 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 6 + 1).trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 15 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact S4 331 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 331 ∣ 2 ^ 15 + 1).trans hd) 661 g661 (by norm_num)

theorem kE11_d17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 17 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 17 + 1).trans hd)
  have := S3 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kE11_d19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 19 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 19 + 1).trans hd)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hnz (by norm_num)) 174763 g174763 (by norm_num)
  have := S3 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kE11_d21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 21 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 21 + 1).trans hd)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 271 g271 (by norm_num) (by norm_num)
  omega

theorem kE11_d41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 41 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  exact S4 83 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 83 ∣ 2 ^ 41 + 1).trans hd) 331 g331 (by norm_num)

theorem kE11_d107 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 107 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 2 ^ 107 + 1).trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 643 g643 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d113 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 113 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g48817 : 48817 ∈ P := S2 48817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 48817 ∣ 2 ^ 113 + 1).trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d159 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 159 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6043 : 6043 ∈ P := S2 6043 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6043 ∣ 2 ^ 159 + 1).trans hd)
  have g1511 : 1511 ∈ P := S1 1511 (by norm_num) (by norm_num) (hnz (by norm_num)) 6043 g6043 (by norm_num)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1511 g1511 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d166 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 166 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g997 : 997 ∈ P := S2 997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 997 ∣ 2 ^ 166 + 1).trans hd)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 997 g997 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

theorem kE11_d173 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 173 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4153 : 4153 ∈ P := S2 4153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4153 ∣ 2 ^ 173 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 4153 g4153 (by norm_num)

theorem kE11_d178 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 178 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1069 : 1069 ∈ P := S2 1069 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1069 ∣ 2 ^ 178 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 178 + 1).trans hd) 1069 g1069 (by norm_num)

theorem kE11_d194 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 194 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g389 : 389 ∈ P := S2 389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 389 ∣ 2 ^ 194 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 194 + 1).trans hd) 389 g389 (by norm_num)

theorem kE11_d200 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 200 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g25601 : 25601 ∈ P := S2 25601 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 25601 ∣ 2 ^ 200 + 1).trans hd)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 25601 g25601 (by norm_num) (by norm_num)
  omega

theorem kE11_d202 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 202 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g809 : 809 ∈ P := S2 809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 809 ∣ 2 ^ 202 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 202 + 1).trans hd) 809 g809 (by norm_num)

theorem kE11_d206 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 206 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41201 : 41201 ∈ P := S2 41201 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41201 ∣ 2 ^ 206 + 1).trans hd)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 41201 g41201 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 206 + 1).trans hd) 109 g109 (by norm_num)

theorem kE11_d213 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 213 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g102241 : 102241 ∈ P := S2 102241 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 102241 ∣ 2 ^ 213 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 102241 g102241 (by norm_num)

theorem kE11_d214 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 214 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g843589 : 843589 ∈ P := S2 843589 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 843589 ∣ 2 ^ 214 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 214 + 1).trans hd) 843589 g843589 (by norm_num)

theorem kE11_d218 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 218 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5669 : 5669 ∈ P := S2 5669 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5669 ∣ 2 ^ 218 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 218 + 1).trans hd) 5669 g5669 (by norm_num)

theorem kE11_d226 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 226 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58309 : 58309 ∈ P := S2 58309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58309 ∣ 2 ^ 226 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 226 + 1).trans hd) 58309 g58309 (by norm_num)

theorem kE11_d227 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 227 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g297371 : 297371 ∈ P := S2 297371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 297371 ∣ 2 ^ 227 + 1).trans hd)
  have g24781 : 24781 ∈ P := S1 24781 (by norm_num) (by norm_num) (hnz (by norm_num)) 297371 g297371 (by norm_num)
  have g12391 : 12391 ∈ P := S1 12391 (by norm_num) (by norm_num) (hnz (by norm_num)) 24781 g24781 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 12391 g12391 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

theorem kE11_d232 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 232 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g929 : 929 ∈ P := S2 929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 929 ∣ 2 ^ 232 + 1).trans hd)
  have g5569 : 5569 ∈ P := S2 5569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5569 ∣ 2 ^ 232 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 929 g929 5569 g5569 (by norm_num) (by norm_num)
  omega

theorem kE11_d233 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 233 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g467 : 467 ∈ P := S2 467 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 467 ∣ 2 ^ 233 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 467 g467 (by norm_num)
  have g27961 : 27961 ∈ P := S2 27961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 27961 ∣ 2 ^ 233 + 1).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 27961 g27961 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem kE11_d237 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 237 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g647011 : 647011 ∈ P := S2 647011 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 647011 ∣ 2 ^ 237 + 1).trans hd)
  have g161753 : 161753 ∈ P := S1 161753 (by norm_num) (by norm_num) (hnz (by norm_num)) 647011 g647011 (by norm_num)
  have g26959 : 26959 ∈ P := S1 26959 (by norm_num) (by norm_num) (hnz (by norm_num)) 161753 g161753 (by norm_num)
  have g337 : 337 ∈ P := S1 337 (by norm_num) (by norm_num) (hnz (by norm_num)) 26959 g26959 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 337 g337 (by norm_num)

theorem kE11_d239 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 239 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g340337 : 340337 ∈ P := S2 340337 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 340337 ∣ 2 ^ 239 + 1).trans hd)
  have g433 : 433 ∈ P := S1 433 (by norm_num) (by norm_num) (hnz (by norm_num)) 340337 g340337 (by norm_num)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 433 g433 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d241 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 241 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2411 : 2411 ∈ P := S2 2411 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2411 ∣ 2 ^ 241 + 1).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 2411 g2411 (by norm_num)

theorem kE11_d248 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 248 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8929 : 8929 ∈ P := S2 8929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8929 ∣ 2 ^ 248 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 8929 g8929 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8929 g8929 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE11_d253 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 253 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4049 : 4049 ∈ P := S2 4049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4049 ∣ 2 ^ 253 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4049 g4049 (by norm_num)

theorem kE11_d254 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 254 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g509 : 509 ∈ P := S2 509 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 509 ∣ 2 ^ 254 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 254 + 1).trans hd) 509 g509 (by norm_num)

theorem kE11_d263 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 263 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 63 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1579 : 1579 ∈ P := S2 1579 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1579 ∣ 2 ^ 200 * 2 ^ 63 + 1).trans hd')
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 79 g79 (by norm_num) (by norm_num)
  omega

theorem kE11_d267 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 267 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 67 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g179 : 179 ∈ P := S2 179 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 179 ∣ 2 ^ 200 * 2 ^ 67 + 1).trans hd')
  have g3739 : 3739 ∈ P := S2 3739 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3739 ∣ 2 ^ 200 * 2 ^ 67 + 1).trans hd')
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 3739 g3739 (by norm_num) (by norm_num)
  omega

theorem kE11_d274 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 274 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 74 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g189061 : 189061 ∈ P := S2 189061 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 189061 ∣ 2 ^ 200 * 2 ^ 74 + 1).trans hd')
  have g94531 : 94531 ∈ P := S1 94531 (by norm_num) (by norm_num) (hnz (by norm_num)) 189061 g189061 (by norm_num)
  have g23633 : 23633 ∈ P := S1 23633 (by norm_num) (by norm_num) (hnz (by norm_num)) 94531 g94531 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 23633 g23633 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE11_d278 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 278 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 78 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1408349 : 1408349 ∈ P := S2 1408349 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1408349 ∣ 2 ^ 200 * 2 ^ 78 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1408349 g1408349 (by norm_num)

theorem kE11_d279 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 279 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 79 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g26227 : 26227 ∈ P := S2 26227 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 26227 ∣ 2 ^ 200 * 2 ^ 79 + 1).trans hd')
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have := S3 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 26227 g26227 331 g331 (by norm_num) (by norm_num)
  omega

theorem kE11_d283 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 283 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 83 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1699 : 1699 ∈ P := S2 1699 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1699 ∣ 2 ^ 200 * 2 ^ 83 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1699 g1699 (by norm_num)

theorem kE11_d293 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 293 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 93 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g587 : 587 ∈ P := S2 587 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 587 ∣ 2 ^ 200 * 2 ^ 93 + 1).trans hd')
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 587 g587 (by norm_num)

theorem kE11_d296 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 296 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 96 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g80513 : 80513 ∈ P := S2 80513 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 80513 ∣ 2 ^ 200 * 2 ^ 96 + 1).trans hd')
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 80513 g80513 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d298 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 298 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 98 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1789 : 1789 ∈ P := S2 1789 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1789 ∣ 2 ^ 200 * 2 ^ 98 + 1).trans hd')
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 200 * 2 ^ 98 + 1).trans hd') 1789 g1789 (by norm_num)

theorem kE11_d299 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 299 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 99 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g2393 : 2393 ∈ P := S2 2393 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2393 ∣ 2 ^ 200 * 2 ^ 99 + 1).trans hd')
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 2 ^ 200 * 2 ^ 99 + 1).trans hd')
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2393 g2393 683 g683 (by norm_num) (by norm_num)
  omega

theorem kE11_d301 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 301 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 101 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  exact S5 43 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 43 * 43 ∣ 2 ^ 200 * 2 ^ 101 + 1).trans hd')

theorem kE11_d305 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 305 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 105 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g331841 : 331841 ∈ P := S2 331841 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 331841 ∣ 2 ^ 200 * 2 ^ 105 + 1).trans hd')
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 331841 g331841 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d309 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 309 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 109 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g2473 : 2473 ∈ P := S2 2473 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2473 ∣ 2 ^ 200 * 2 ^ 109 + 1).trans hd')
  have g1237 : 1237 ∈ P := S1 1237 (by norm_num) (by norm_num) (hnz (by norm_num)) 2473 g2473 (by norm_num)
  exact S4 619 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 619 ∣ 2 ^ 200 * 2 ^ 109 + 1).trans hd') 1237 g1237 (by norm_num)

theorem kE11_d326 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 326 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 126 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g9781 : 9781 ∈ P := S2 9781 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9781 ∣ 2 ^ 200 * 2 ^ 126 + 1).trans hd')
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 9781 g9781 (by norm_num)

theorem kE11_d327 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 327 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 127 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g666427 : 666427 ∈ P := S2 666427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 666427 ∣ 2 ^ 200 * 2 ^ 127 + 1).trans hd')
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 666427 g666427 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE11_d329 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 329 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 129 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 200 * 2 ^ 129 + 1).trans hd')
  have g659 : 659 ∈ P := S2 659 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 659 ∣ 2 ^ 200 * 2 ^ 129 + 1).trans hd')
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 659 g659 (by norm_num) (by norm_num)
  omega

theorem kE11_d331 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 331 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 131 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g5297 : 5297 ∈ P := S2 5297 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5297 ∣ 2 ^ 200 * 2 ^ 131 + 1).trans hd')
  have g883 : 883 ∈ P := S1 883 (by norm_num) (by norm_num) (hnz (by norm_num)) 5297 g5297 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 883 g883 (by norm_num) (by norm_num)
  omega

theorem kE11_d337 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 337 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 137 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g21569 : 21569 ∈ P := S2 21569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 21569 ∣ 2 ^ 200 * 2 ^ 137 + 1).trans hd')
  have g719 : 719 ∈ P := S1 719 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 719 g719 (by norm_num) (by norm_num)
  omega

theorem kE11_d341 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 341 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 141 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g647219 : 647219 ∈ P := S2 647219 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 647219 ∣ 2 ^ 200 * 2 ^ 141 + 1).trans hd')
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 647219 g647219 (by norm_num)

theorem kE11_d344 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 344 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 144 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g4129 : 4129 ∈ P := S2 4129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4129 ∣ 2 ^ 200 * 2 ^ 144 + 1).trans hd')
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 4129 g4129 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4129 g4129 59 g59 (by norm_num) (by norm_num)
  omega

theorem kE11_d365 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 365 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 165 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 2 ^ 200 * 2 ^ 165 + 1).trans hd')
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 200 * 2 ^ 165 + 1).trans hd') 439 g439 (by norm_num)

theorem kE11_d367 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 367 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 167 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g19819 : 19819 ∈ P := S2 19819 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19819 ∣ 2 ^ 200 * 2 ^ 167 + 1).trans hd')
  have g2203 : 2203 ∈ P := S2 2203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2203 ∣ 2 ^ 200 * 2 ^ 167 + 1).trans hd')
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19819 g19819 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE11_d373 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 373 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 173 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 60427 ∣ 2 ^ 200 * 2 ^ 173 + 1).trans hd')
  have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 1259 g1259 (by norm_num) (by norm_num)
  omega

theorem kE11_d381 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 381 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 181 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g3049 : 3049 ∈ P := S2 3049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3049 ∣ 2 ^ 200 * 2 ^ 181 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3049 g3049 (by norm_num)

theorem kE11_d382 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 382 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 182 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g3821 : 3821 ∈ P := S2 3821 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3821 ∣ 2 ^ 200 * 2 ^ 182 + 1).trans hd')
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 3821 g3821 (by norm_num)

theorem kE11_d386 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 386 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 186 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g3089 : 3089 ∈ P := S2 3089 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3089 ∣ 2 ^ 200 * 2 ^ 186 + 1).trans hd')
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 200 * 2 ^ 186 + 1).trans hd') 3089 g3089 (by norm_num)

theorem kE11_d394 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 394 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 194 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g4729 : 4729 ∈ P := S2 4729 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4729 ∣ 2 ^ 200 * 2 ^ 194 + 1).trans hd')
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 200 * 2 ^ 194 + 1).trans hd') 4729 g4729 (by norm_num)

theorem kE11_d395 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 395 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 195 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g5531 : 5531 ∈ P := S2 5531 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5531 ∣ 2 ^ 200 * 2 ^ 195 + 1).trans hd')
  have g461 : 461 ∈ P := S1 461 (by norm_num) (by norm_num) (hnz (by norm_num)) 5531 g5531 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 200 * 2 ^ 195 + 1).trans hd') 461 g461 (by norm_num)

theorem kE11_d397 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 397 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 197 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g13499 : 13499 ∈ P := S2 13499 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13499 ∣ 2 ^ 200 * 2 ^ 197 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13499 g13499 (by norm_num)

theorem kE11_d398 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 398 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 198 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g797 : 797 ∈ P := S2 797 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 797 ∣ 2 ^ 200 * 2 ^ 198 + 1).trans hd')
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 797 g797 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 200 * 2 ^ 198 + 1).trans hd') 19 g19 (by norm_num)

theorem new_e11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    ∀ d ∈ ({6, 15, 17, 19, 21, 41, 107, 113, 159, 166, 173, 178, 194, 200, 202, 206, 213, 214, 218, 226, 227, 232, 233, 237, 239, 241, 248, 253, 254, 263, 267, 274, 278, 279, 283, 293, 296, 298, 299, 301, 305, 309, 326, 327, 329, 331, 337, 341, 344, 365, 367, 373, 381, 382, 386, 394, 395, 397, 398} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun h => kE11_d6 hP E (two_pow_add_one_dvd_of_odd_mul (d := 6) h)
  · exact fun h => kE11_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) h)
  · exact fun h => kE11_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) h)
  · exact fun h => kE11_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) h)
  · exact fun h => kE11_d21 hP E (two_pow_add_one_dvd_of_odd_mul (d := 21) h)
  · exact fun h => kE11_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) h)
  · exact fun h => kE11_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) h)
  · exact fun h => kE11_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) h)
  · exact fun h => kE11_d159 hP E (two_pow_add_one_dvd_of_odd_mul (d := 159) h)
  · exact fun h => kE11_d166 hP E (two_pow_add_one_dvd_of_odd_mul (d := 166) h)
  · exact fun h => kE11_d173 hP E (two_pow_add_one_dvd_of_odd_mul (d := 173) h)
  · exact fun h => kE11_d178 hP E (two_pow_add_one_dvd_of_odd_mul (d := 178) h)
  · exact fun h => kE11_d194 hP E (two_pow_add_one_dvd_of_odd_mul (d := 194) h)
  · exact fun h => kE11_d200 hP E (two_pow_add_one_dvd_of_odd_mul (d := 200) h)
  · exact fun h => kE11_d202 hP E (two_pow_add_one_dvd_of_odd_mul (d := 202) h)
  · exact fun h => kE11_d206 hP E (two_pow_add_one_dvd_of_odd_mul (d := 206) h)
  · exact fun h => kE11_d213 hP E (two_pow_add_one_dvd_of_odd_mul (d := 213) h)
  · exact fun h => kE11_d214 hP E (two_pow_add_one_dvd_of_odd_mul (d := 214) h)
  · exact fun h => kE11_d218 hP E (two_pow_add_one_dvd_of_odd_mul (d := 218) h)
  · exact fun h => kE11_d226 hP E (two_pow_add_one_dvd_of_odd_mul (d := 226) h)
  · exact fun h => kE11_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) h)
  · exact fun h => kE11_d232 hP E (two_pow_add_one_dvd_of_odd_mul (d := 232) h)
  · exact fun h => kE11_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) h)
  · exact fun h => kE11_d237 hP E (two_pow_add_one_dvd_of_odd_mul (d := 237) h)
  · exact fun h => kE11_d239 hP E (two_pow_add_one_dvd_of_odd_mul (d := 239) h)
  · exact fun h => kE11_d241 hP E (two_pow_add_one_dvd_of_odd_mul (d := 241) h)
  · exact fun h => kE11_d248 hP E (two_pow_add_one_dvd_of_odd_mul (d := 248) h)
  · exact fun h => kE11_d253 hP E (two_pow_add_one_dvd_of_odd_mul (d := 253) h)
  · exact fun h => kE11_d254 hP E (two_pow_add_one_dvd_of_odd_mul (d := 254) h)
  · exact fun h => kE11_d263 hP E (two_pow_add_one_dvd_of_odd_mul (d := 263) h)
  · exact fun h => kE11_d267 hP E (two_pow_add_one_dvd_of_odd_mul (d := 267) h)
  · exact fun h => kE11_d274 hP E (two_pow_add_one_dvd_of_odd_mul (d := 274) h)
  · exact fun h => kE11_d278 hP E (two_pow_add_one_dvd_of_odd_mul (d := 278) h)
  · exact fun h => kE11_d279 hP E (two_pow_add_one_dvd_of_odd_mul (d := 279) h)
  · exact fun h => kE11_d283 hP E (two_pow_add_one_dvd_of_odd_mul (d := 283) h)
  · exact fun h => kE11_d293 hP E (two_pow_add_one_dvd_of_odd_mul (d := 293) h)
  · exact fun h => kE11_d296 hP E (two_pow_add_one_dvd_of_odd_mul (d := 296) h)
  · exact fun h => kE11_d298 hP E (two_pow_add_one_dvd_of_odd_mul (d := 298) h)
  · exact fun h => kE11_d299 hP E (two_pow_add_one_dvd_of_odd_mul (d := 299) h)
  · exact fun h => kE11_d301 hP E (two_pow_add_one_dvd_of_odd_mul (d := 301) h)
  · exact fun h => kE11_d305 hP E (two_pow_add_one_dvd_of_odd_mul (d := 305) h)
  · exact fun h => kE11_d309 hP E (two_pow_add_one_dvd_of_odd_mul (d := 309) h)
  · exact fun h => kE11_d326 hP E (two_pow_add_one_dvd_of_odd_mul (d := 326) h)
  · exact fun h => kE11_d327 hP E (two_pow_add_one_dvd_of_odd_mul (d := 327) h)
  · exact fun h => kE11_d329 hP E (two_pow_add_one_dvd_of_odd_mul (d := 329) h)
  · exact fun h => kE11_d331 hP E (two_pow_add_one_dvd_of_odd_mul (d := 331) h)
  · exact fun h => kE11_d337 hP E (two_pow_add_one_dvd_of_odd_mul (d := 337) h)
  · exact fun h => kE11_d341 hP E (two_pow_add_one_dvd_of_odd_mul (d := 341) h)
  · exact fun h => kE11_d344 hP E (two_pow_add_one_dvd_of_odd_mul (d := 344) h)
  · exact fun h => kE11_d365 hP E (two_pow_add_one_dvd_of_odd_mul (d := 365) h)
  · exact fun h => kE11_d367 hP E (two_pow_add_one_dvd_of_odd_mul (d := 367) h)
  · exact fun h => kE11_d373 hP E (two_pow_add_one_dvd_of_odd_mul (d := 373) h)
  · exact fun h => kE11_d381 hP E (two_pow_add_one_dvd_of_odd_mul (d := 381) h)
  · exact fun h => kE11_d382 hP E (two_pow_add_one_dvd_of_odd_mul (d := 382) h)
  · exact fun h => kE11_d386 hP E (two_pow_add_one_dvd_of_odd_mul (d := 386) h)
  · exact fun h => kE11_d394 hP E (two_pow_add_one_dvd_of_odd_mul (d := 394) h)
  · exact fun h => kE11_d395 hP E (two_pow_add_one_dvd_of_odd_mul (d := 395) h)
  · exact fun h => kE11_d397 hP E (two_pow_add_one_dvd_of_odd_mul (d := 397) h)
  · exact fun h => kE11_d398 hP E (two_pow_add_one_dvd_of_odd_mul (d := 398) h)

theorem kE13_d9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 9 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact S4 19 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 19 ∣ 2 ^ 9 + 1).trans hd) 398581 g398581 (by norm_num)

theorem kE13_d11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 11 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 683 ∣ 2 ^ 11 + 1).trans hd)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 683 g683 (by norm_num) (by norm_num)
  omega

theorem kE13_d13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 13 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 2 ^ 13 + 1).trans hd)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 683 g683 (by norm_num) (by norm_num)
  omega

theorem kE13_d15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 15 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g331 : 331 ∈ P := S2 331 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 331 ∣ 2 ^ 15 + 1).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 17 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 17 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 43691 g43691 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 19 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 19 + 1).trans hd)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hnz (by norm_num)) 174763 g174763 (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 43691 g43691 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)
  omega

theorem kE13_d21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 21 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 21 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 41 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g83 : 83 ∈ P := S2 83 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 83 ∣ 2 ^ 41 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d73 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 73 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 2 ^ 73 + 1).trans hd)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 439 g439 (by norm_num) (by norm_num)
  omega

theorem kE13_d88 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 88 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g229153 : 229153 ∈ P := S2 229153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 229153 ∣ 2 ^ 88 + 1).trans hd)
  have g114577 : 114577 ∈ P := S1 114577 (by norm_num) (by norm_num) (hnz (by norm_num)) 229153 g229153 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 114577 g114577 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 59 g59 (by norm_num) (by norm_num)
  omega

theorem kE13_d89 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 89 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g179 : 179 ∈ P := S2 179 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 179 ∣ 2 ^ 89 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d107 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 107 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 2 ^ 107 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 643 g643 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d113 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 113 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g227 : 227 ∈ P := S2 227 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 227 ∣ 2 ^ 113 + 1).trans hd)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 227 g227 (by norm_num) (by norm_num)
  omega

theorem kE13_d136 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 136 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g383521 : 383521 ∈ P := S2 383521 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 383521 ∣ 2 ^ 136 + 1).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 383521 g383521 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 113 g113 (by norm_num) (by norm_num)
  omega

theorem kE13_d137 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 137 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15619 : 15619 ∈ P := S2 15619 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15619 ∣ 2 ^ 137 + 1).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 15619 g15619 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d159 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 159 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6043 : 6043 ∈ P := S2 6043 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6043 ∣ 2 ^ 159 + 1).trans hd)
  have g1511 : 1511 ∈ P := S1 1511 (by norm_num) (by norm_num) (hnz (by norm_num)) 6043 g6043 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1511 g1511 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d173 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 173 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g347 : 347 ∈ P := S2 347 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 347 ∣ 2 ^ 173 + 1).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

theorem kE13_d181 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 181 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g1811 : 1811 ∈ P := S2 1811 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1811 ∣ 2 ^ 181 + 1).trans hd)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 1811 g1811 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 151 g151 (by norm_num) (by norm_num)
  omega

theorem kE13_d200 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 200 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g25601 : 25601 ∈ P := S2 25601 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 25601 ∣ 2 ^ 200 + 1).trans hd)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 25601 g25601 (by norm_num) (by norm_num)
  omega

theorem kE13_d213 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 213 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g102241 : 102241 ∈ P := S2 102241 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 102241 ∣ 2 ^ 213 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 102241 g102241 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 67 g67 (by norm_num) (by norm_num)
  omega

theorem kE13_d227 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 227 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g297371 : 297371 ∈ P := S2 297371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 297371 ∣ 2 ^ 227 + 1).trans hd)
  have g24781 : 24781 ∈ P := S1 24781 (by norm_num) (by norm_num) (hnz (by norm_num)) 297371 g297371 (by norm_num)
  have g12391 : 12391 ∈ P := S1 12391 (by norm_num) (by norm_num) (hnz (by norm_num)) 24781 g24781 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 12391 g12391 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

theorem kE13_d232 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 232 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g929 : 929 ∈ P := S2 929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 929 ∣ 2 ^ 232 + 1).trans hd)
  have g5569 : 5569 ∈ P := S2 5569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5569 ∣ 2 ^ 232 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 929 g929 5569 g5569 (by norm_num) (by norm_num)
  omega

theorem kE13_d233 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 233 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g467 : 467 ∈ P := S2 467 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 467 ∣ 2 ^ 233 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 467 g467 (by norm_num)
  have g27961 : 27961 ∈ P := S2 27961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 27961 ∣ 2 ^ 233 + 1).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 27961 g27961 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem kE13_d237 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 237 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g647011 : 647011 ∈ P := S2 647011 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 647011 ∣ 2 ^ 237 + 1).trans hd)
  have g161753 : 161753 ∈ P := S1 161753 (by norm_num) (by norm_num) (hnz (by norm_num)) 647011 g647011 (by norm_num)
  have g26959 : 26959 ∈ P := S1 26959 (by norm_num) (by norm_num) (hnz (by norm_num)) 161753 g161753 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 26959 g26959 (by norm_num) (by norm_num)
  omega

theorem kE13_d239 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 239 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g340337 : 340337 ∈ P := S2 340337 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 340337 ∣ 2 ^ 239 + 1).trans hd)
  have g433 : 433 ∈ P := S1 433 (by norm_num) (by norm_num) (hnz (by norm_num)) 340337 g340337 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 433 g433 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d241 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 241 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g2411 : 2411 ∈ P := S2 2411 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2411 ∣ 2 ^ 241 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 2411 g2411 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 67 g67 (by norm_num) (by norm_num)
  omega

theorem kE13_d248 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 248 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g8929 : 8929 ∈ P := S2 8929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8929 ∣ 2 ^ 248 + 1).trans hd)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 8929 g8929 (by norm_num) (by norm_num)
  omega

theorem kE13_d263 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 263 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 63 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1579 : 1579 ∈ P := S2 1579 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1579 ∣ 2 ^ 200 * 2 ^ 63 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d271 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 271 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 71 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1627 ∣ 2 ^ 200 * 2 ^ 71 + 1).trans hd')
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1627 g1627 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 37 g37 (by norm_num) (by norm_num)
  omega

theorem kE13_d283 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 283 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 83 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1699 : 1699 ∈ P := S2 1699 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1699 ∣ 2 ^ 200 * 2 ^ 83 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1699 g1699 (by norm_num)

theorem kE13_d293 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 293 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 93 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g587 : 587 ∈ P := S2 587 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 587 ∣ 2 ^ 200 * 2 ^ 93 + 1).trans hd')
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 587 g587 (by norm_num)

theorem kE13_d296 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 296 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 96 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g80513 : 80513 ∈ P := S2 80513 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 80513 ∣ 2 ^ 200 * 2 ^ 96 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 80513 g80513 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d301 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 301 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 101 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  exact S5 43 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 43 * 43 ∣ 2 ^ 200 * 2 ^ 101 + 1).trans hd')

theorem kE13_d305 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 305 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 105 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g331841 : 331841 ∈ P := S2 331841 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 331841 ∣ 2 ^ 200 * 2 ^ 105 + 1).trans hd')
  have g7901 : 7901 ∈ P := S1 7901 (by norm_num) (by norm_num) (hnz (by norm_num)) 331841 g331841 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 7901 g7901 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 439 g439 (by norm_num) (by norm_num)
  omega

theorem kE13_d309 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 309 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 109 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g619 : 619 ∈ P := S2 619 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 619 ∣ 2 ^ 200 * 2 ^ 109 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 619 g619 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d311 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 311 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 111 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g64067 : 64067 ∈ P := S2 64067 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 64067 ∣ 2 ^ 200 * 2 ^ 111 + 1).trans hd')
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 64067 g64067 (by norm_num) (by norm_num)
  omega

theorem kE13_d327 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 327 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 127 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g666427 : 666427 ∈ P := S2 666427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 666427 ∣ 2 ^ 200 * 2 ^ 127 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 666427 g666427 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE13_d329 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 329 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 129 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 200 * 2 ^ 129 + 1).trans hd')
  have g659 : 659 ∈ P := S2 659 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 659 ∣ 2 ^ 200 * 2 ^ 129 + 1).trans hd')
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 659 g659 (by norm_num) (by norm_num)
  omega

theorem kE13_d331 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 331 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 131 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g5297 : 5297 ∈ P := S2 5297 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5297 ∣ 2 ^ 200 * 2 ^ 131 + 1).trans hd')
  have g883 : 883 ∈ P := S1 883 (by norm_num) (by norm_num) (hnz (by norm_num)) 5297 g5297 (by norm_num)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 883 g883 (by norm_num) (by norm_num)
  omega

theorem kE13_d337 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 337 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 137 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g21569 : 21569 ∈ P := S2 21569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 21569 ∣ 2 ^ 200 * 2 ^ 137 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d344 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 344 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 144 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g4129 : 4129 ∈ P := S2 4129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4129 ∣ 2 ^ 200 * 2 ^ 144 + 1).trans hd')
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4129 g4129 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE13_d367 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 367 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 167 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g2203 : 2203 ∈ P := S2 2203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2203 ∣ 2 ^ 200 * 2 ^ 167 + 1).trans hd')
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 2203 g2203 (by norm_num) (by norm_num)
  omega

theorem kE13_d373 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 373 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 173 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 60427 ∣ 2 ^ 200 * 2 ^ 173 + 1).trans hd')
  have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 1259 g1259 (by norm_num) (by norm_num)
  omega

theorem kE13_d381 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 381 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 181 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g3049 : 3049 ∈ P := S2 3049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3049 ∣ 2 ^ 200 * 2 ^ 181 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3049 g3049 (by norm_num)

theorem kE13_d395 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 395 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 195 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g5531 : 5531 ∈ P := S2 5531 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5531 ∣ 2 ^ 200 * 2 ^ 195 + 1).trans hd')
  have g461 : 461 ∈ P := S1 461 (by norm_num) (by norm_num) (hnz (by norm_num)) 5531 g5531 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 200 * 2 ^ 195 + 1).trans hd') 461 g461 (by norm_num)

theorem kE13_d397 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 397 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 197 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g13499 : 13499 ∈ P := S2 13499 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13499 ∣ 2 ^ 200 * 2 ^ 197 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13499 g13499 (by norm_num)

theorem new_e13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p) :
    ∀ d ∈ ({9, 11, 13, 15, 17, 19, 21, 41, 73, 88, 89, 107, 113, 136, 137, 159, 173, 181, 200, 213, 227, 232, 233, 237, 239, 241, 248, 263, 271, 283, 293, 296, 301, 305, 309, 311, 327, 329, 331, 337, 344, 367, 373, 381, 395, 397} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun h => kE13_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) h)
  · exact fun h => kE13_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) h)
  · exact fun h => kE13_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) h)
  · exact fun h => kE13_d15 hP E (two_pow_add_one_dvd_of_odd_mul (d := 15) h)
  · exact fun h => kE13_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) h)
  · exact fun h => kE13_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) h)
  · exact fun h => kE13_d21 hP E (two_pow_add_one_dvd_of_odd_mul (d := 21) h)
  · exact fun h => kE13_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) h)
  · exact fun h => kE13_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) h)
  · exact fun h => kE13_d88 hP E (two_pow_add_one_dvd_of_odd_mul (d := 88) h)
  · exact fun h => kE13_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) h)
  · exact fun h => kE13_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) h)
  · exact fun h => kE13_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) h)
  · exact fun h => kE13_d136 hP E (two_pow_add_one_dvd_of_odd_mul (d := 136) h)
  · exact fun h => kE13_d137 hP E (two_pow_add_one_dvd_of_odd_mul (d := 137) h)
  · exact fun h => kE13_d159 hP E (two_pow_add_one_dvd_of_odd_mul (d := 159) h)
  · exact fun h => kE13_d173 hP E (two_pow_add_one_dvd_of_odd_mul (d := 173) h)
  · exact fun h => kE13_d181 hP E (two_pow_add_one_dvd_of_odd_mul (d := 181) h)
  · exact fun h => kE13_d200 hP E (two_pow_add_one_dvd_of_odd_mul (d := 200) h)
  · exact fun h => kE13_d213 hP E (two_pow_add_one_dvd_of_odd_mul (d := 213) h)
  · exact fun h => kE13_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) h)
  · exact fun h => kE13_d232 hP E (two_pow_add_one_dvd_of_odd_mul (d := 232) h)
  · exact fun h => kE13_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) h)
  · exact fun h => kE13_d237 hP E (two_pow_add_one_dvd_of_odd_mul (d := 237) h)
  · exact fun h => kE13_d239 hP E (two_pow_add_one_dvd_of_odd_mul (d := 239) h)
  · exact fun h => kE13_d241 hP E (two_pow_add_one_dvd_of_odd_mul (d := 241) h)
  · exact fun h => kE13_d248 hP E (two_pow_add_one_dvd_of_odd_mul (d := 248) h)
  · exact fun h => kE13_d263 hP E (two_pow_add_one_dvd_of_odd_mul (d := 263) h)
  · exact fun h => kE13_d271 hP E (two_pow_add_one_dvd_of_odd_mul (d := 271) h)
  · exact fun h => kE13_d283 hP E (two_pow_add_one_dvd_of_odd_mul (d := 283) h)
  · exact fun h => kE13_d293 hP E (two_pow_add_one_dvd_of_odd_mul (d := 293) h)
  · exact fun h => kE13_d296 hP E (two_pow_add_one_dvd_of_odd_mul (d := 296) h)
  · exact fun h => kE13_d301 hP E (two_pow_add_one_dvd_of_odd_mul (d := 301) h)
  · exact fun h => kE13_d305 hP E (two_pow_add_one_dvd_of_odd_mul (d := 305) h)
  · exact fun h => kE13_d309 hP E (two_pow_add_one_dvd_of_odd_mul (d := 309) h)
  · exact fun h => kE13_d311 hP E (two_pow_add_one_dvd_of_odd_mul (d := 311) h)
  · exact fun h => kE13_d327 hP E (two_pow_add_one_dvd_of_odd_mul (d := 327) h)
  · exact fun h => kE13_d329 hP E (two_pow_add_one_dvd_of_odd_mul (d := 329) h)
  · exact fun h => kE13_d331 hP E (two_pow_add_one_dvd_of_odd_mul (d := 331) h)
  · exact fun h => kE13_d337 hP E (two_pow_add_one_dvd_of_odd_mul (d := 337) h)
  · exact fun h => kE13_d344 hP E (two_pow_add_one_dvd_of_odd_mul (d := 344) h)
  · exact fun h => kE13_d367 hP E (two_pow_add_one_dvd_of_odd_mul (d := 367) h)
  · exact fun h => kE13_d373 hP E (two_pow_add_one_dvd_of_odd_mul (d := 373) h)
  · exact fun h => kE13_d381 hP E (two_pow_add_one_dvd_of_odd_mul (d := 381) h)
  · exact fun h => kE13_d395 hP E (two_pow_add_one_dvd_of_odd_mul (d := 395) h)
  · exact fun h => kE13_d397 hP E (two_pow_add_one_dvd_of_odd_mul (d := 397) h)

theorem kE19_d5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 5 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 5 + 1).trans hd) 131 g131 (by norm_num)

theorem kE19_d7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 7 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 7 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 9 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19 : 19 ∈ P := S2 19 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19 ∣ 2 ^ 9 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 11 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 683 ∣ 2 ^ 11 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE19_d13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 13 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 2 ^ 13 + 1).trans hd)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE19_d17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 17 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 17 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43691 g43691 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 19 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 19 + 1).trans hd)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hnz (by norm_num)) 174763 g174763 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kE19_d41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 41 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g83 : 83 ∈ P := S2 83 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 83 ∣ 2 ^ 41 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE19_d44 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 44 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g353 : 353 ∈ P := S2 353 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 353 ∣ 2 ^ 44 + 1).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 353 g353 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 59 g59 (by norm_num) (by norm_num)
  omega

theorem kE19_d73 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 73 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 2 ^ 73 + 1).trans hd)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 439 g439 (by norm_num) (by norm_num)
  omega

theorem kE19_d89 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 89 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g179 : 179 ∈ P := S2 179 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 179 ∣ 2 ^ 89 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d107 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 107 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 2 ^ 107 + 1).trans hd)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 643 g643 (by norm_num) (by norm_num)
  omega

theorem kE19_d113 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 113 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g48817 : 48817 ∈ P := S2 48817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 48817 ∣ 2 ^ 113 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d129 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 129 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1033 : 1033 ∈ P := S2 1033 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1033 ∣ 2 ^ 129 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1033 g1033 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d137 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 137 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15619 : 15619 ∈ P := S2 15619 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15619 ∣ 2 ^ 137 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 15619 g15619 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d159 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 159 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6043 : 6043 ∈ P := S2 6043 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6043 ∣ 2 ^ 159 + 1).trans hd)
  have g1511 : 1511 ∈ P := S1 1511 (by norm_num) (by norm_num) (hnz (by norm_num)) 6043 g6043 (by norm_num)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1511 g1511 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE19_d173 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 173 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g4153 : 4153 ∈ P := S2 4153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4153 ∣ 2 ^ 173 + 1).trans hd)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 4153 g4153 (by norm_num) (by norm_num)
  omega

theorem kE19_d181 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 181 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g1811 : 1811 ∈ P := S2 1811 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1811 ∣ 2 ^ 181 + 1).trans hd)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 1811 g1811 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE19_d193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 193 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g6563 : 6563 ∈ P := S2 6563 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6563 ∣ 2 ^ 193 + 1).trans hd)
  have g547 : 547 ∈ P := S1 547 (by norm_num) (by norm_num) (hnz (by norm_num)) 6563 g6563 (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 137 g137 (by norm_num) (by norm_num)
  omega

theorem kE19_d211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 211 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g4643 : 4643 ∈ P := S2 4643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4643 ∣ 2 ^ 211 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 4643 g4643 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 43 g43 (by norm_num) (by norm_num)
  omega

theorem kE19_d213 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 213 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17467 : 17467 ∈ P := S2 17467 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17467 ∣ 2 ^ 213 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 17467 g17467 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d227 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 227 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g297371 : 297371 ∈ P := S2 297371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 297371 ∣ 2 ^ 227 + 1).trans hd)
  have g24781 : 24781 ∈ P := S1 24781 (by norm_num) (by norm_num) (hnz (by norm_num)) 297371 g297371 (by norm_num)
  have g12391 : 12391 ∈ P := S1 12391 (by norm_num) (by norm_num) (hnz (by norm_num)) 24781 g24781 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 12391 g12391 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

theorem kE19_d233 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 233 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g27961 : 27961 ∈ P := S2 27961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 27961 ∣ 2 ^ 233 + 1).trans hd)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 27961 g27961 (by norm_num) (by norm_num)
  omega

theorem kE19_d236 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 236 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1889 : 1889 ∈ P := S2 1889 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1889 ∣ 2 ^ 236 + 1).trans hd)
  have g11329 : 11329 ∈ P := S2 11329 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11329 ∣ 2 ^ 236 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1889 g1889 11329 g11329 (by norm_num) (by norm_num)
  omega

theorem kE19_d237 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 237 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g647011 : 647011 ∈ P := S2 647011 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 647011 ∣ 2 ^ 237 + 1).trans hd)
  have g161753 : 161753 ∈ P := S1 161753 (by norm_num) (by norm_num) (hnz (by norm_num)) 647011 g647011 (by norm_num)
  have g26959 : 26959 ∈ P := S1 26959 (by norm_num) (by norm_num) (hnz (by norm_num)) 161753 g161753 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 26959 g26959 (by norm_num) (by norm_num)
  omega

theorem kE19_d239 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 239 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g340337 : 340337 ∈ P := S2 340337 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 340337 ∣ 2 ^ 239 + 1).trans hd)
  have := S3 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 340337 g340337 (by norm_num) (by norm_num)
  omega

theorem kE19_d244 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 244 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 (by norm_num)
  have g977 : 977 ∈ P := S2 977 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 977 ∣ 2 ^ 244 + 1).trans hd)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 977 g977 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem kE19_d251 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 251 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g238451 : 238451 ∈ P := S2 238451 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 238451 ∣ 2 ^ 251 + 1).trans hd)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 238451 g238451 (by norm_num) (by norm_num)
  omega

theorem kE19_d263 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 263 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 63 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1579 : 1579 ∈ P := S2 1579 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1579 ∣ 2 ^ 200 * 2 ^ 63 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1579 g1579 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d268 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 268 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 68 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g75041 : 75041 ∈ P := S2 75041 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 75041 ∣ 2 ^ 200 * 2 ^ 68 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 75041 g75041 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d271 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 271 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 71 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1627 ∣ 2 ^ 200 * 2 ^ 71 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1627 g1627 131 g131 (by norm_num) (by norm_num)
  omega

theorem kE19_d283 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 283 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 83 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g1699 : 1699 ∈ P := S2 1699 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1699 ∣ 2 ^ 200 * 2 ^ 83 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1699 g1699 (by norm_num)

theorem kE19_d284 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 284 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 84 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g2273 : 2273 ∈ P := S2 2273 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2273 ∣ 2 ^ 200 * 2 ^ 84 + 1).trans hd')
  have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 2273 g2273 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 379 g379 (by norm_num) (by norm_num)
  omega

theorem kE19_d293 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 293 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 93 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g587 : 587 ∈ P := S2 587 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 587 ∣ 2 ^ 200 * 2 ^ 93 + 1).trans hd')
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 587 g587 (by norm_num)

theorem kE19_d309 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 309 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 109 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g619 : 619 ∈ P := S2 619 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 619 ∣ 2 ^ 200 * 2 ^ 109 + 1).trans hd')
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2851 g2851 619 g619 (by norm_num) (by norm_num)
  omega

theorem kE19_d311 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 311 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 111 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g64067 : 64067 ∈ P := S2 64067 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 64067 ∣ 2 ^ 200 * 2 ^ 111 + 1).trans hd')
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 64067 g64067 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 19 g19 (by norm_num) (by norm_num)
  omega

theorem kE19_d316 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 316 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 116 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g994769 : 994769 ∈ P := S2 994769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 994769 ∣ 2 ^ 200 * 2 ^ 116 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 994769 g994769 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d327 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 327 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 127 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g666427 : 666427 ∈ P := S2 666427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 666427 ∣ 2 ^ 200 * 2 ^ 127 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 666427 g666427 13 g13 (by norm_num) (by norm_num)
  omega

theorem kE19_d331 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 331 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 131 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g5297 : 5297 ∈ P := S2 5297 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5297 ∣ 2 ^ 200 * 2 ^ 131 + 1).trans hd')
  have g883 : 883 ∈ P := S1 883 (by norm_num) (by norm_num) (hnz (by norm_num)) 5297 g5297 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 883 g883 (by norm_num) (by norm_num)
  omega

theorem kE19_d332 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 332 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 132 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g11953 : 11953 ∈ P := S2 11953 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11953 ∣ 2 ^ 200 * 2 ^ 132 + 1).trans hd')
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 11953 g11953 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 43 g43 (by norm_num) (by norm_num)
  omega

theorem kE19_d337 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 337 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 137 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g21569 : 21569 ∈ P := S2 21569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 21569 ∣ 2 ^ 200 * 2 ^ 137 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21569 g21569 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d367 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 367 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 167 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g19819 : 19819 ∈ P := S2 19819 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19819 ∣ 2 ^ 200 * 2 ^ 167 + 1).trans hd')
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19819 g19819 389 g389 (by norm_num) (by norm_num)
  omega

theorem kE19_d373 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 373 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 173 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 60427 ∣ 2 ^ 200 * 2 ^ 173 + 1).trans hd')
  have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (hnz (by norm_num)) 60427 g60427 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 15107 g15107 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 1259 g1259 (by norm_num) (by norm_num)
  omega

theorem kE19_d381 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 381 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 181 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g3049 : 3049 ∈ P := S2 3049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3049 ∣ 2 ^ 200 * 2 ^ 181 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3049 g3049 (by norm_num)

theorem kE19_d397 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 397 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hd' : 2 ^ 200 * 2 ^ 197 + 1 ∣ 2 ^ m + 1 := by rw [← pow_add]; exact hd
  have g13499 : 13499 ∈ P := S2 13499 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13499 ∣ 2 ^ 200 * 2 ^ 197 + 1).trans hd')
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13499 g13499 (by norm_num)

theorem new_e19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({5, 7, 9, 11, 13, 17, 19, 41, 44, 73, 89, 107, 113, 129, 137, 159, 173, 181, 193, 211, 213, 227, 233, 236, 237, 239, 244, 251, 263, 268, 271, 283, 284, 293, 309, 311, 316, 327, 331, 332, 337, 367, 373, 381, 397} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun h => kE19_d5 hP E (two_pow_add_one_dvd_of_odd_mul (d := 5) h)
  · exact fun h => kE19_d7 hP E (two_pow_add_one_dvd_of_odd_mul (d := 7) h)
  · exact fun h => kE19_d9 hP E (two_pow_add_one_dvd_of_odd_mul (d := 9) h)
  · exact fun h => kE19_d11 hP E (two_pow_add_one_dvd_of_odd_mul (d := 11) h)
  · exact fun h => kE19_d13 hP E (two_pow_add_one_dvd_of_odd_mul (d := 13) h)
  · exact fun h => kE19_d17 hP E (two_pow_add_one_dvd_of_odd_mul (d := 17) h)
  · exact fun h => kE19_d19 hP E (two_pow_add_one_dvd_of_odd_mul (d := 19) h)
  · exact fun h => kE19_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) h)
  · exact fun h => kE19_d44 hP E (two_pow_add_one_dvd_of_odd_mul (d := 44) h)
  · exact fun h => kE19_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) h)
  · exact fun h => kE19_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) h)
  · exact fun h => kE19_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) h)
  · exact fun h => kE19_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) h)
  · exact fun h => kE19_d129 hP E (two_pow_add_one_dvd_of_odd_mul (d := 129) h)
  · exact fun h => kE19_d137 hP E (two_pow_add_one_dvd_of_odd_mul (d := 137) h)
  · exact fun h => kE19_d159 hP E (two_pow_add_one_dvd_of_odd_mul (d := 159) h)
  · exact fun h => kE19_d173 hP E (two_pow_add_one_dvd_of_odd_mul (d := 173) h)
  · exact fun h => kE19_d181 hP E (two_pow_add_one_dvd_of_odd_mul (d := 181) h)
  · exact fun h => kE19_d193 hP E (two_pow_add_one_dvd_of_odd_mul (d := 193) h)
  · exact fun h => kE19_d211 hP E (two_pow_add_one_dvd_of_odd_mul (d := 211) h)
  · exact fun h => kE19_d213 hP E (two_pow_add_one_dvd_of_odd_mul (d := 213) h)
  · exact fun h => kE19_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) h)
  · exact fun h => kE19_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) h)
  · exact fun h => kE19_d236 hP E (two_pow_add_one_dvd_of_odd_mul (d := 236) h)
  · exact fun h => kE19_d237 hP E (two_pow_add_one_dvd_of_odd_mul (d := 237) h)
  · exact fun h => kE19_d239 hP E (two_pow_add_one_dvd_of_odd_mul (d := 239) h)
  · exact fun h => kE19_d244 hP E (two_pow_add_one_dvd_of_odd_mul (d := 244) h)
  · exact fun h => kE19_d251 hP E (two_pow_add_one_dvd_of_odd_mul (d := 251) h)
  · exact fun h => kE19_d263 hP E (two_pow_add_one_dvd_of_odd_mul (d := 263) h)
  · exact fun h => kE19_d268 hP E (two_pow_add_one_dvd_of_odd_mul (d := 268) h)
  · exact fun h => kE19_d271 hP E (two_pow_add_one_dvd_of_odd_mul (d := 271) h)
  · exact fun h => kE19_d283 hP E (two_pow_add_one_dvd_of_odd_mul (d := 283) h)
  · exact fun h => kE19_d284 hP E (two_pow_add_one_dvd_of_odd_mul (d := 284) h)
  · exact fun h => kE19_d293 hP E (two_pow_add_one_dvd_of_odd_mul (d := 293) h)
  · exact fun h => kE19_d309 hP E (two_pow_add_one_dvd_of_odd_mul (d := 309) h)
  · exact fun h => kE19_d311 hP E (two_pow_add_one_dvd_of_odd_mul (d := 311) h)
  · exact fun h => kE19_d316 hP E (two_pow_add_one_dvd_of_odd_mul (d := 316) h)
  · exact fun h => kE19_d327 hP E (two_pow_add_one_dvd_of_odd_mul (d := 327) h)
  · exact fun h => kE19_d331 hP E (two_pow_add_one_dvd_of_odd_mul (d := 331) h)
  · exact fun h => kE19_d332 hP E (two_pow_add_one_dvd_of_odd_mul (d := 332) h)
  · exact fun h => kE19_d337 hP E (two_pow_add_one_dvd_of_odd_mul (d := 337) h)
  · exact fun h => kE19_d367 hP E (two_pow_add_one_dvd_of_odd_mul (d := 367) h)
  · exact fun h => kE19_d373 hP E (two_pow_add_one_dvd_of_odd_mul (d := 373) h)
  · exact fun h => kE19_d381 hP E (two_pow_add_one_dvd_of_odd_mul (d := 381) h)
  · exact fun h => kE19_d397 hP E (two_pow_add_one_dvd_of_odd_mul (d := 397) h)

-- Section 2. The step.

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he hDA h11 h13 h19 => ?_⟩
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
  rcases he with he | he | he
  · rw [he] at E
    have hn := new_e11 hP E
    rw [ha] at hn
    exact (h1 n h hiff he hDA (h11 he) hn).trans (le_max_left _ _)
  · rw [he] at E
    have hn := new_e13 hP E
    rw [ha] at hn
    exact (h2 n h hiff he hDA (h13 he) hn).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [he] at E
    have hn := new_e19 hP E
    rw [ha] at hn
    exact (h3 n h hiff he hDA (h19 he) hn).trans ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1
