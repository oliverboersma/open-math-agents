import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1 (3 the only repeated odd prime,
-- its exponent e above 500 and no odd multiple of the 190 values listed there) by pushing the
-- exponent sieve from 500 to 800.  Proving the two H proves the step.
--
-- Notation: n unitary perfect with 3 the only repeated odd prime, e = n.factorization 3,
-- a = padicValNat 2 n.  A number x is an ODD MULTIPLE of d when x mod 2d = d; then 3^d + 1
-- divides 3^e + 1 (for x = e).
--
-- PROVED BELOW (no hypothesis needed): for each of the 84 values d of the second set in H1
-- (500 < d <= 800), e is no odd multiple of d (kill3_e<d>, collected in core3_residues_800).
-- Method as in the parent: every odd prime of 3^d + 1 is a simple prime of n with source 3^e + 1,
-- and the odd primes of p + 1 for a simple prime p are again simple primes; the chains found give
-- an odd prime with two sources or a square, contradicting the balance equation
-- (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p.  Witness primes above 4.3 * 10^7 are
-- certified by the Lucas test.  Factorizations of 3^d + 1 were taken from factordb and checked
-- here: Lean re-checks every divisibility and primality.
-- Consequently 500 < e <= 800 forces e to be one of 577, 764 (exponent_sieve_800).
--
-- H1 (OPEN): e > 800, e no odd multiple of any of the 84 new values, a no odd multiple of DA.
-- H2 (OPEN): e is one of 577, 764, a no odd multiple of DA.
-- This narrows e; it does not bound a.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 above 800, e no odd multiple of any d in the first set (the 84
-- new values), and a no odd multiple of any d in DA (the second set).  The 190 classes of the parent
-- step are not restated, to keep H1 short: they hold for every such n anyway, by
-- three_exponent_residues_200 and core3_residues_new, both already proved and merged.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 577 or 764, and a no odd multiple of any d in DA.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 577 ∨ n.factorization 3 = 764) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

theorem prime_1017977689 : Nat.Prime 1017977689 := by
  refine lucas_primality 1017977689 (29 : ZMod 1017977689) ?_ (fun q hq hd => ?_)
  · rw [show 1017977689 - 1 = 1017977688 from by norm_num]
    reduce_mod_char
  · have e : 1017977689 - 1 = [2 ^ 3, 3 ^ 2, 7 ^ 1, 13 ^ 1, 251 ^ 1, 619 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 2 = 508988844 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 508988844 = ((1017977688 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 3 = 339325896 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 339325896 = ((279497006 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 7 = 145425384 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 145425384 = ((465289529 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 13 = 78305976 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 78305976 = ((623361230 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 251 = 4055688 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 4055688 = ((1267572 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1017977689 - 1) / 619 = 1644552 from by norm_num]
      have h2 : (29 : ZMod 1017977689) ^ 1644552 = ((871193982 : ℕ) : ZMod 1017977689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_44197979107 : Nat.Prime 44197979107 := by
  refine lucas_primality 44197979107 (2 : ZMod 44197979107) ?_ (fun q hq hd => ?_)
  · rw [show 44197979107 - 1 = 44197979106 from by norm_num]
    reduce_mod_char
  · have e : 44197979107 - 1 = [2 ^ 1, 3 ^ 1, 1231 ^ 1, 5984021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44197979107 - 1) / 2 = 22098989553 from by norm_num]
      have h2 : (2 : ZMod 44197979107) ^ 22098989553 = ((44197979106 : ℕ) : ZMod 44197979107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44197979107 - 1) / 3 = 14732659702 from by norm_num]
      have h2 : (2 : ZMod 44197979107) ^ 14732659702 = ((42197034448 : ℕ) : ZMod 44197979107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44197979107 - 1) / 1231 = 35904126 from by norm_num]
      have h2 : (2 : ZMod 44197979107) ^ 35904126 = ((6986177710 : ℕ) : ZMod 44197979107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (44197979107 - 1) / 5984021 = 7386 from by norm_num]
      have h2 : (2 : ZMod 44197979107) ^ 7386 = ((12590398146 : ℕ) : ZMod 44197979107) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_265187874643 : Nat.Prime 265187874643 := by
  refine lucas_primality 265187874643 (2 : ZMod 265187874643) ?_ (fun q hq hd => ?_)
  · rw [show 265187874643 - 1 = 265187874642 from by norm_num]
    reduce_mod_char
  · have e : 265187874643 - 1 = [2 ^ 1, 3 ^ 1, 44197979107 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (265187874643 - 1) / 2 = 132593937321 from by norm_num]
      have h2 : (2 : ZMod 265187874643) ^ 132593937321 = ((265187874642 : ℕ) : ZMod 265187874643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (265187874643 - 1) / 3 = 88395958214 from by norm_num]
      have h2 : (2 : ZMod 265187874643) ^ 88395958214 = ((41708320762 : ℕ) : ZMod 265187874643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_44197979107).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (265187874643 - 1) / 44197979107 = 6 from by norm_num]
      have h2 : (2 : ZMod 265187874643) ^ 6 = ((64 : ℕ) : ZMod 265187874643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4782859410470150595894697 : Nat.Prime 4782859410470150595894697 := by
  refine lucas_primality 4782859410470150595894697 (5 : ZMod 4782859410470150595894697) ?_ (fun q hq hd => ?_)
  · rw [show 4782859410470150595894697 - 1 = 4782859410470150595894696 from by norm_num]
    reduce_mod_char
  · have e : 4782859410470150595894697 - 1 = [2 ^ 3, 3 ^ 4, 313 ^ 1, 449 ^ 1, 198047 ^ 1, 265187874643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 2 = 2391429705235075297947348 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 2391429705235075297947348 = ((4782859410470150595894696 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 3 = 1594286470156716865298232 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 1594286470156716865298232 = ((3053270075429078203762181 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 313 = 15280700991917414044392 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 15280700991917414044392 = ((555010498255491005758348 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 449 = 10652248130223052552104 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 10652248130223052552104 = ((3564112385976030277733999 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 198047 = 24150123003479732568 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 24150123003479732568 = ((2496607240004597504642251 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_265187874643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4782859410470150595894697 - 1) / 265187874643 = 18035739442872 from by norm_num]
      have h2 : (5 : ZMod 4782859410470150595894697) ^ 18035739442872 = ((2350064132068956624832015 : ℕ) : ZMod 4782859410470150595894697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_132324814660676946180438449964086833 : Nat.Prime 132324814660676946180438449964086833 := by
  refine lucas_primality 132324814660676946180438449964086833 (5 : ZMod 132324814660676946180438449964086833) ?_ (fun q hq hd => ?_)
  · rw [show 132324814660676946180438449964086833 - 1 = 132324814660676946180438449964086832 from by norm_num]
    reduce_mod_char
  · have e : 132324814660676946180438449964086833 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 2, 109 ^ 1, 311 ^ 1, 347 ^ 1, 4782859410470150595894697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 2 = 66162407330338473090219224982043416 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 66162407330338473090219224982043416 = ((132324814660676946180438449964086832 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 3 = 44108271553558982060146149988028944 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 44108271553558982060146149988028944 = ((80665917625388823809726918113243443 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 7 = 18903544951525278025776921423440976 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 18903544951525278025776921423440976 = ((78595358100911707188808375753252579 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 109 = 1213989125327311432848059173982448 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 1213989125327311432848059173982448 = ((124431308001252677799817512805836211 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 311 = 425481719166163814085011093132112 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 425481719166163814085011093132112 = ((61909189951082731652546509122084725 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 347 = 381339523517800997638151152634256 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 381339523517800997638151152634256 = ((34576229958675863773997478821566912 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4782859410470150595894697).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132324814660676946180438449964086833 - 1) / 4782859410470150595894697 = 27666465456 from by norm_num]
      have h2 : (5 : ZMod 132324814660676946180438449964086833) ^ 27666465456 = ((87650302446744554275595376506862808 : ℕ) : ZMod 132324814660676946180438449964086833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_364069663 : Nat.Prime 364069663 := by
  refine lucas_primality 364069663 (3 : ZMod 364069663) ?_ (fun q hq hd => ?_)
  · rw [show 364069663 - 1 = 364069662 from by norm_num]
    reduce_mod_char
  · have e : 364069663 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 311 ^ 1, 17737 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (364069663 - 1) / 2 = 182034831 from by norm_num]
      have h2 : (3 : ZMod 364069663) ^ 182034831 = ((364069662 : ℕ) : ZMod 364069663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (364069663 - 1) / 3 = 121356554 from by norm_num]
      have h2 : (3 : ZMod 364069663) ^ 121356554 = ((234922420 : ℕ) : ZMod 364069663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (364069663 - 1) / 11 = 33097242 from by norm_num]
      have h2 : (3 : ZMod 364069663) ^ 33097242 = ((179112237 : ℕ) : ZMod 364069663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (364069663 - 1) / 311 = 1170642 from by norm_num]
      have h2 : (3 : ZMod 364069663) ^ 1170642 = ((172222824 : ℕ) : ZMod 364069663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (364069663 - 1) / 17737 = 20526 from by norm_num]
      have h2 : (3 : ZMod 364069663) ^ 20526 = ((15279019 : ℕ) : ZMod 364069663) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_54093886887062230599082516017052647105427126977713417 : Nat.Prime 54093886887062230599082516017052647105427126977713417 := by
  refine lucas_primality 54093886887062230599082516017052647105427126977713417 (5 : ZMod 54093886887062230599082516017052647105427126977713417) ?_ (fun q hq hd => ?_)
  · rw [show 54093886887062230599082516017052647105427126977713417 - 1 = 54093886887062230599082516017052647105427126977713416 from by norm_num]
    reduce_mod_char
  · have e : 54093886887062230599082516017052647105427126977713417 - 1 = [2 ^ 3, 13 ^ 1, 127 ^ 1, 151 ^ 1, 563 ^ 1, 364069663 ^ 1, 132324814660676946180438449964086833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 2 = 27046943443531115299541258008526323552713563488856708 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 27046943443531115299541258008526323552713563488856708 = ((54093886887062230599082516017052647105427126977713416 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 13 = 4161068222081710046083270462850203623494394382901032 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 4161068222081710046083270462850203623494394382901032 = ((7728233886786350798967157275793543489263228615803158 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 127 = 425936117220962445662067055252383048074229346281208 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 425936117220962445662067055252383048074229346281208 = ((2239647663056502595795100264494350133150410360702179 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 151 = 358237661503723381450877589516904947718060443561016 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 358237661503723381450877589516904947718060443561016 = ((22993871292410755564413453316476837776847888950054876 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 563 = 96081504239897390051656333955688538375536637615832 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 96081504239897390051656333955688538375536637615832 = ((26063547536050146663583758440736206112591694247774219 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_364069663).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 364069663 = 148581143623225290812221605009293639238013432 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 148581143623225290812221605009293639238013432 = ((42425435328856391227047781303961790755289454493842080 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_132324814660676946180438449964086833).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (54093886887062230599082516017052647105427126977713417 - 1) / 132324814660676946180438449964086833 = 408796241474255752 from by norm_num]
      have h2 : (5 : ZMod 54093886887062230599082516017052647105427126977713417) ^ 408796241474255752 = ((12848166215544593518638425850418360040221654200461523 : ℕ) : ZMod 54093886887062230599082516017052647105427126977713417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_134382593 : Nat.Prime 134382593 := by
  refine lucas_primality 134382593 (5 : ZMod 134382593) ?_ (fun q hq hd => ?_)
  · rw [show 134382593 - 1 = 134382592 from by norm_num]
    reduce_mod_char
  · have e : 134382593 - 1 = [2 ^ 10, 19 ^ 1, 6907 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (134382593 - 1) / 2 = 67191296 from by norm_num]
      have h2 : (5 : ZMod 134382593) ^ 67191296 = ((134382592 : ℕ) : ZMod 134382593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (134382593 - 1) / 19 = 7072768 from by norm_num]
      have h2 : (5 : ZMod 134382593) ^ 7072768 = ((98892022 : ℕ) : ZMod 134382593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (134382593 - 1) / 6907 = 19456 from by norm_num]
      have h2 : (5 : ZMod 134382593) ^ 19456 = ((56971207 : ℕ) : ZMod 134382593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_149789881 : Nat.Prime 149789881 := by
  refine lucas_primality 149789881 (11 : ZMod 149789881) ?_ (fun q hq hd => ?_)
  · rw [show 149789881 - 1 = 149789880 from by norm_num]
    reduce_mod_char
  · have e : 149789881 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 257 ^ 1, 1619 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149789881 - 1) / 2 = 74894940 from by norm_num]
      have h2 : (11 : ZMod 149789881) ^ 74894940 = ((149789880 : ℕ) : ZMod 149789881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149789881 - 1) / 3 = 49929960 from by norm_num]
      have h2 : (11 : ZMod 149789881) ^ 49929960 = ((82840593 : ℕ) : ZMod 149789881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149789881 - 1) / 5 = 29957976 from by norm_num]
      have h2 : (11 : ZMod 149789881) ^ 29957976 = ((69175518 : ℕ) : ZMod 149789881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149789881 - 1) / 257 = 582840 from by norm_num]
      have h2 : (11 : ZMod 149789881) ^ 582840 = ((140017438 : ℕ) : ZMod 149789881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (149789881 - 1) / 1619 = 92520 from by norm_num]
      have h2 : (11 : ZMod 149789881) ^ 92520 = ((135835749 : ℕ) : ZMod 149789881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_60427777 : Nat.Prime 60427777 := by
  refine lucas_primality 60427777 (5 : ZMod 60427777) ?_ (fun q hq hd => ?_)
  · rw [show 60427777 - 1 = 60427776 from by norm_num]
    reduce_mod_char
  · have e : 60427777 - 1 = [2 ^ 9, 3 ^ 1, 39341 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60427777 - 1) / 2 = 30213888 from by norm_num]
      have h2 : (5 : ZMod 60427777) ^ 30213888 = ((60427776 : ℕ) : ZMod 60427777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60427777 - 1) / 3 = 20142592 from by norm_num]
      have h2 : (5 : ZMod 60427777) ^ 20142592 = ((42018236 : ℕ) : ZMod 60427777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60427777 - 1) / 39341 = 1536 from by norm_num]
      have h2 : (5 : ZMod 60427777) ^ 1536 = ((46272095 : ℕ) : ZMod 60427777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8421451860752373577 : Nat.Prime 8421451860752373577 := by
  refine lucas_primality 8421451860752373577 (11 : ZMod 8421451860752373577) ?_ (fun q hq hd => ?_)
  · rw [show 8421451860752373577 - 1 = 8421451860752373576 from by norm_num]
    reduce_mod_char
  · have e : 8421451860752373577 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 23 ^ 1, 37 ^ 1, 521 ^ 1, 1871 ^ 1, 60427777 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 2 = 4210725930376186788 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 4210725930376186788 = ((8421451860752373576 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 3 = 2807150620250791192 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 2807150620250791192 = ((3696232665929706873 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 7 = 1203064551536053368 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 1203064551536053368 = ((3783663425175947773 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 23 = 366150080902277112 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 366150080902277112 = ((1167298615123202981 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 37 = 227606807047361448 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 227606807047361448 = ((4971036815740117121 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 521 = 16164015087816456 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 16164015087816456 = ((1479932634280672641 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 1871 = 4501043217932856 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 4501043217932856 = ((5926814778777969906 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_60427777).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8421451860752373577 - 1) / 60427777 = 139363919688 from by norm_num]
      have h2 : (11 : ZMod 8421451860752373577) ^ 139363919688 = ((2548300432752916939 : ℕ) : ZMod 8421451860752373577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1146386713 : Nat.Prime 1146386713 := by
  refine lucas_primality 1146386713 (5 : ZMod 1146386713) ?_ (fun q hq hd => ?_)
  · rw [show 1146386713 - 1 = 1146386712 from by norm_num]
    reduce_mod_char
  · have e : 1146386713 - 1 = [2 ^ 3, 3 ^ 1, 523 ^ 1, 91331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1146386713 - 1) / 2 = 573193356 from by norm_num]
      have h2 : (5 : ZMod 1146386713) ^ 573193356 = ((1146386712 : ℕ) : ZMod 1146386713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1146386713 - 1) / 3 = 382128904 from by norm_num]
      have h2 : (5 : ZMod 1146386713) ^ 382128904 = ((490355917 : ℕ) : ZMod 1146386713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1146386713 - 1) / 523 = 2191944 from by norm_num]
      have h2 : (5 : ZMod 1146386713) ^ 2191944 = ((913788553 : ℕ) : ZMod 1146386713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1146386713 - 1) / 91331 = 12552 from by norm_num]
      have h2 : (5 : ZMod 1146386713) ^ 12552 = ((1137323581 : ℕ) : ZMod 1146386713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_48345927359 : Nat.Prime 48345927359 := by
  refine lucas_primality 48345927359 (7 : ZMod 48345927359) ?_ (fun q hq hd => ?_)
  · rw [show 48345927359 - 1 = 48345927358 from by norm_num]
    reduce_mod_char
  · have e : 48345927359 - 1 = [2 ^ 1, 1129 ^ 1, 21410951 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48345927359 - 1) / 2 = 24172963679 from by norm_num]
      have h2 : (7 : ZMod 48345927359) ^ 24172963679 = ((48345927358 : ℕ) : ZMod 48345927359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48345927359 - 1) / 1129 = 42821902 from by norm_num]
      have h2 : (7 : ZMod 48345927359) ^ 42821902 = ((18650725792 : ℕ) : ZMod 48345927359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48345927359 - 1) / 21410951 = 2258 from by norm_num]
      have h2 : (7 : ZMod 48345927359) ^ 2258 = ((6790051914 : ℕ) : ZMod 48345927359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_887051075182933 : Nat.Prime 887051075182933 := by
  refine lucas_primality 887051075182933 (2 : ZMod 887051075182933) ?_ (fun q hq hd => ?_)
  · rw [show 887051075182933 - 1 = 887051075182932 from by norm_num]
    reduce_mod_char
  · have e : 887051075182933 - 1 = [2 ^ 2, 3 ^ 1, 11 ^ 1, 139 ^ 1, 48345927359 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887051075182933 - 1) / 2 = 443525537591466 from by norm_num]
      have h2 : (2 : ZMod 887051075182933) ^ 443525537591466 = ((887051075182932 : ℕ) : ZMod 887051075182933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887051075182933 - 1) / 3 = 295683691727644 from by norm_num]
      have h2 : (2 : ZMod 887051075182933) ^ 295683691727644 = ((658681031915361 : ℕ) : ZMod 887051075182933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887051075182933 - 1) / 11 = 80641006834812 from by norm_num]
      have h2 : (2 : ZMod 887051075182933) ^ 80641006834812 = ((553329914219201 : ℕ) : ZMod 887051075182933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887051075182933 - 1) / 139 = 6381662411388 from by norm_num]
      have h2 : (2 : ZMod 887051075182933) ^ 6381662411388 = ((674835219000827 : ℕ) : ZMod 887051075182933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_48345927359).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (887051075182933 - 1) / 48345927359 = 18348 from by norm_num]
      have h2 : (2 : ZMod 887051075182933) ^ 18348 = ((207181785238747 : ℕ) : ZMod 887051075182933) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2621920730595608239277 : Nat.Prime 2621920730595608239277 := by
  refine lucas_primality 2621920730595608239277 (2 : ZMod 2621920730595608239277) ?_ (fun q hq hd => ?_)
  · rw [show 2621920730595608239277 - 1 = 2621920730595608239276 from by norm_num]
    reduce_mod_char
  · have e : 2621920730595608239277 - 1 = [2 ^ 2, 41 ^ 1, 67 ^ 1, 269 ^ 1, 887051075182933 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2621920730595608239277 - 1) / 2 = 1310960365297804119638 from by norm_num]
      have h2 : (2 : ZMod 2621920730595608239277) ^ 1310960365297804119638 = ((2621920730595608239276 : ℕ) : ZMod 2621920730595608239277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2621920730595608239277 - 1) / 41 = 63949286112088005836 from by norm_num]
      have h2 : (2 : ZMod 2621920730595608239277) ^ 63949286112088005836 = ((817935744568010859460 : ℕ) : ZMod 2621920730595608239277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2621920730595608239277 - 1) / 67 = 39133145232770272228 from by norm_num]
      have h2 : (2 : ZMod 2621920730595608239277) ^ 39133145232770272228 = ((1432702299889352113721 : ℕ) : ZMod 2621920730595608239277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2621920730595608239277 - 1) / 269 = 9746917214110067804 from by norm_num]
      have h2 : (2 : ZMod 2621920730595608239277) ^ 9746917214110067804 = ((2463264719467958641087 : ℕ) : ZMod 2621920730595608239277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_887051075182933).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2621920730595608239277 - 1) / 887051075182933 = 2955772 from by norm_num]
      have h2 : (2 : ZMod 2621920730595608239277) ^ 2955772 = ((783382725240884808259 : ℕ) : ZMod 2621920730595608239277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_147842923003 : Nat.Prime 147842923003 := by
  refine lucas_primality 147842923003 (2 : ZMod 147842923003) ?_ (fun q hq hd => ?_)
  · rw [show 147842923003 - 1 = 147842923002 from by norm_num]
    reduce_mod_char
  · have e : 147842923003 - 1 = [2 ^ 1, 3 ^ 1, 23 ^ 1, 541 ^ 1, 1980269 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (147842923003 - 1) / 2 = 73921461501 from by norm_num]
      have h2 : (2 : ZMod 147842923003) ^ 73921461501 = ((147842923002 : ℕ) : ZMod 147842923003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (147842923003 - 1) / 3 = 49280974334 from by norm_num]
      have h2 : (2 : ZMod 147842923003) ^ 49280974334 = ((26327811107 : ℕ) : ZMod 147842923003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (147842923003 - 1) / 23 = 6427953174 from by norm_num]
      have h2 : (2 : ZMod 147842923003) ^ 6427953174 = ((2359696639 : ℕ) : ZMod 147842923003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (147842923003 - 1) / 541 = 273277122 from by norm_num]
      have h2 : (2 : ZMod 147842923003) ^ 273277122 = ((40392722600 : ℕ) : ZMod 147842923003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (147842923003 - 1) / 1980269 = 74658 from by norm_num]
      have h2 : (2 : ZMod 147842923003) ^ 74658 = ((57907163591 : ℕ) : ZMod 147842923003) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6217786649 : Nat.Prime 6217786649 := by
  refine lucas_primality 6217786649 (6 : ZMod 6217786649) ?_ (fun q hq hd => ?_)
  · rw [show 6217786649 - 1 = 6217786648 from by norm_num]
    reduce_mod_char
  · have e : 6217786649 - 1 = [2 ^ 3, 137 ^ 1, 5673163 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6217786649 - 1) / 2 = 3108893324 from by norm_num]
      have h2 : (6 : ZMod 6217786649) ^ 3108893324 = ((6217786648 : ℕ) : ZMod 6217786649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6217786649 - 1) / 137 = 45385304 from by norm_num]
      have h2 : (6 : ZMod 6217786649) ^ 45385304 = ((3792343444 : ℕ) : ZMod 6217786649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6217786649 - 1) / 5673163 = 1096 from by norm_num]
      have h2 : (6 : ZMod 6217786649) ^ 1096 = ((5768135421 : ℕ) : ZMod 6217786649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_495738992209 : Nat.Prime 495738992209 := by
  refine lucas_primality 495738992209 (11 : ZMod 495738992209) ?_ (fun q hq hd => ?_)
  · rw [show 495738992209 - 1 = 495738992208 from by norm_num]
    reduce_mod_char
  · have e : 495738992209 - 1 = [2 ^ 4, 3 ^ 1, 557 ^ 1, 569 ^ 1, 32587 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (495738992209 - 1) / 2 = 247869496104 from by norm_num]
      have h2 : (11 : ZMod 495738992209) ^ 247869496104 = ((495738992208 : ℕ) : ZMod 495738992209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (495738992209 - 1) / 3 = 165246330736 from by norm_num]
      have h2 : (11 : ZMod 495738992209) ^ 165246330736 = ((480216855162 : ℕ) : ZMod 495738992209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (495738992209 - 1) / 557 = 890016144 from by norm_num]
      have h2 : (11 : ZMod 495738992209) ^ 890016144 = ((356412587856 : ℕ) : ZMod 495738992209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (495738992209 - 1) / 569 = 871246032 from by norm_num]
      have h2 : (11 : ZMod 495738992209) ^ 871246032 = ((260500379776 : ℕ) : ZMod 495738992209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (495738992209 - 1) / 32587 = 15212784 from by norm_num]
      have h2 : (11 : ZMod 495738992209) ^ 15212784 = ((458593974021 : ℕ) : ZMod 495738992209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3751695056761 : Nat.Prime 3751695056761 := by
  refine lucas_primality 3751695056761 (13 : ZMod 3751695056761) ?_ (fun q hq hd => ?_)
  · rw [show 3751695056761 - 1 = 3751695056760 from by norm_num]
    reduce_mod_char
  · have e : 3751695056761 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 2, 47 ^ 1, 281 ^ 1, 48311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 2 = 1875847528380 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 1875847528380 = ((3751695056760 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 3 = 1250565018920 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 1250565018920 = ((1557504334700 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 5 = 750339011352 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 750339011352 = ((54552416911 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 7 = 535956436680 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 535956436680 = ((1409599487328 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 47 = 79823299080 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 79823299080 = ((394270279207 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 281 = 13351227960 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 13351227960 = ((317486565586 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3751695056761 - 1) / 48311 = 77657160 from by norm_num]
      have h2 : (13 : ZMod 3751695056761) ^ 77657160 = ((2247829419149 : ℕ) : ZMod 3751695056761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8594162701 : Nat.Prime 8594162701 := by
  refine lucas_primality 8594162701 (6 : ZMod 8594162701) ?_ (fun q hq hd => ?_)
  · rw [show 8594162701 - 1 = 8594162700 from by norm_num]
    reduce_mod_char
  · have e : 8594162701 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 28647209 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8594162701 - 1) / 2 = 4297081350 from by norm_num]
      have h2 : (6 : ZMod 8594162701) ^ 4297081350 = ((8594162700 : ℕ) : ZMod 8594162701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8594162701 - 1) / 3 = 2864720900 from by norm_num]
      have h2 : (6 : ZMod 8594162701) ^ 2864720900 = ((7249434168 : ℕ) : ZMod 8594162701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8594162701 - 1) / 5 = 1718832540 from by norm_num]
      have h2 : (6 : ZMod 8594162701) ^ 1718832540 = ((8454613123 : ℕ) : ZMod 8594162701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8594162701 - 1) / 28647209 = 300 from by norm_num]
      have h2 : (6 : ZMod 8594162701) ^ 300 = ((6418512164 : ℕ) : ZMod 8594162701) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1749994974153827 : Nat.Prime 1749994974153827 := by
  refine lucas_primality 1749994974153827 (2 : ZMod 1749994974153827) ?_ (fun q hq hd => ?_)
  · rw [show 1749994974153827 - 1 = 1749994974153826 from by norm_num]
    reduce_mod_char
  · have e : 1749994974153827 - 1 = [2 ^ 1, 17 ^ 1, 53 ^ 1, 113 ^ 1, 8594162701 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1749994974153827 - 1) / 2 = 874997487076913 from by norm_num]
      have h2 : (2 : ZMod 1749994974153827) ^ 874997487076913 = ((1749994974153826 : ℕ) : ZMod 1749994974153827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1749994974153827 - 1) / 17 = 102940880832578 from by norm_num]
      have h2 : (2 : ZMod 1749994974153827) ^ 102940880832578 = ((160915521181073 : ℕ) : ZMod 1749994974153827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1749994974153827 - 1) / 53 = 33018773097242 from by norm_num]
      have h2 : (2 : ZMod 1749994974153827) ^ 33018773097242 = ((1103666689735947 : ℕ) : ZMod 1749994974153827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1749994974153827 - 1) / 113 = 15486681187202 from by norm_num]
      have h2 : (2 : ZMod 1749994974153827) ^ 15486681187202 = ((273914818713870 : ℕ) : ZMod 1749994974153827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8594162701).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1749994974153827 - 1) / 8594162701 = 203626 from by norm_num]
      have h2 : (2 : ZMod 1749994974153827) ^ 203626 = ((218634107396851 : ℕ) : ZMod 1749994974153827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_46901369347503080003230459 : Nat.Prime 46901369347503080003230459 := by
  refine lucas_primality 46901369347503080003230459 (10 : ZMod 46901369347503080003230459) ?_ (fun q hq hd => ?_)
  · rw [show 46901369347503080003230459 - 1 = 46901369347503080003230458 from by norm_num]
    reduce_mod_char
  · have e : 46901369347503080003230459 - 1 = [2 ^ 1, 3 ^ 1, 107 ^ 1, 563 ^ 1, 74149 ^ 1, 1749994974153827 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 2 = 23450684673751540001615229 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 23450684673751540001615229 = ((46901369347503080003230458 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 3 = 15633789782501026667743486 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 15633789782501026667743486 = ((546288808594023984930825 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 107 = 438330554649561495357294 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 438330554649561495357294 = ((42311334515384283214271039 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 563 = 83306162251337619899166 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 83306162251337619899166 = ((33463718475382145593471056 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 74149 = 632528683428004153842 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 632528683428004153842 = ((3372101480150660562373797 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1749994974153827).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46901369347503080003230459 - 1) / 1749994974153827 = 26800859454 from by norm_num]
      have h2 : (10 : ZMod 46901369347503080003230459) ^ 26800859454 = ((20914284807206898960379268 : ℕ) : ZMod 46901369347503080003230459) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_292106875057 : Nat.Prime 292106875057 := by
  refine lucas_primality 292106875057 (10 : ZMod 292106875057) ?_ (fun q hq hd => ?_)
  · rw [show 292106875057 - 1 = 292106875056 from by norm_num]
    reduce_mod_char
  · have e : 292106875057 - 1 = [2 ^ 4, 3 ^ 1, 29 ^ 1, 59 ^ 1, 61 ^ 1, 199 ^ 1, 293 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 2 = 146053437528 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 146053437528 = ((292106875056 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 3 = 97368958352 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 97368958352 = ((206929154320 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 29 = 10072650864 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 10072650864 = ((223419780131 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 59 = 4950963984 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 4950963984 = ((24845774155 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 61 = 4788637296 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 4788637296 = ((282321613915 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 199 = 1467873744 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 1467873744 = ((186340857793 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (292106875057 - 1) / 293 = 996951792 from by norm_num]
      have h2 : (10 : ZMod 292106875057) ^ 996951792 = ((6260736273 : ℕ) : ZMod 292106875057) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_146053437529 : Nat.Prime 146053437529 := by
  refine lucas_primality 146053437529 (7 : ZMod 146053437529) ?_ (fun q hq hd => ?_)
  · rw [show 146053437529 - 1 = 146053437528 from by norm_num]
    reduce_mod_char
  · have e : 146053437529 - 1 = [2 ^ 3, 3 ^ 1, 29 ^ 1, 59 ^ 1, 61 ^ 1, 199 ^ 1, 293 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 2 = 73026718764 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 73026718764 = ((146053437528 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 3 = 48684479176 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 48684479176 = ((46996354854 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 29 = 5036325432 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 5036325432 = ((17918307078 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 59 = 2475481992 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 2475481992 = ((38662568738 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 61 = 2394318648 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 2394318648 = ((111468213185 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 199 = 733936872 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 733936872 = ((69925559826 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (146053437529 - 1) / 293 = 498475896 from by norm_num]
      have h2 : (7 : ZMod 146053437529) ^ 498475896 = ((135443352956 : ℕ) : ZMod 146053437529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_235085219994159229 : Nat.Prime 235085219994159229 := by
  refine lucas_primality 235085219994159229 (2 : ZMod 235085219994159229) ?_ (fun q hq hd => ?_)
  · rw [show 235085219994159229 - 1 = 235085219994159228 from by norm_num]
    reduce_mod_char
  · have e : 235085219994159229 - 1 = [2 ^ 2, 3 ^ 1, 59 ^ 1, 283 ^ 1, 587 ^ 1, 24251 ^ 1, 82421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 2 = 117542609997079614 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 117542609997079614 = ((235085219994159228 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 3 = 78361739998053076 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 78361739998053076 = ((200424725793878245 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 59 = 3984495254138292 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 3984495254138292 = ((52363076925506497 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 283 = 830689823300916 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 830689823300916 = ((223424539782814629 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 587 = 400485894368244 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 400485894368244 = ((6916858790744919 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 24251 = 9693836130228 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 9693836130228 = ((128474518849729407 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (235085219994159229 - 1) / 82421 = 2852249062668 from by norm_num]
      have h2 : (2 : ZMod 235085219994159229) ^ 2852249062668 = ((867719505807729 : ℕ) : ZMod 235085219994159229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_500181319136509 : Nat.Prime 500181319136509 := by
  refine lucas_primality 500181319136509 (2 : ZMod 500181319136509) ?_ (fun q hq hd => ?_)
  · rw [show 500181319136509 - 1 = 500181319136508 from by norm_num]
    reduce_mod_char
  · have e : 500181319136509 - 1 = [2 ^ 2, 3 ^ 1, 19 ^ 1, 31 ^ 1, 251 ^ 1, 3163 ^ 1, 89137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 2 = 250090659568254 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 250090659568254 = ((500181319136508 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 3 = 166727106378836 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 166727106378836 = ((334906645940545 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 19 = 26325332586132 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 26325332586132 = ((178485354222112 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 31 = 16134881262468 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 16134881262468 = ((56774302579300 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 251 = 1992754259508 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 1992754259508 = ((184684541529828 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 3163 = 158135099316 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 158135099316 = ((257692578905954 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (500181319136509 - 1) / 89137 = 5611377084 from by norm_num]
      have h2 : (2 : ZMod 500181319136509) ^ 5611377084 = ((420259667061494 : ℕ) : ZMod 500181319136509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_368243983 : Nat.Prime 368243983 := by
  refine lucas_primality 368243983 (3 : ZMod 368243983) ?_ (fun q hq hd => ?_)
  · rw [show 368243983 - 1 = 368243982 from by norm_num]
    reduce_mod_char
  · have e : 368243983 - 1 = [2 ^ 1, 3 ^ 4, 971 ^ 1, 2341 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368243983 - 1) / 2 = 184121991 from by norm_num]
      have h2 : (3 : ZMod 368243983) ^ 184121991 = ((368243982 : ℕ) : ZMod 368243983) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368243983 - 1) / 3 = 122747994 from by norm_num]
      have h2 : (3 : ZMod 368243983) ^ 122747994 = ((42363291 : ℕ) : ZMod 368243983) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368243983 - 1) / 971 = 379242 from by norm_num]
      have h2 : (3 : ZMod 368243983) ^ 379242 = ((131544136 : ℕ) : ZMod 368243983) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (368243983 - 1) / 2341 = 157302 from by norm_num]
      have h2 : (3 : ZMod 368243983) ^ 157302 = ((221335133 : ℕ) : ZMod 368243983) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52929917140489 : Nat.Prime 52929917140489 := by
  refine lucas_primality 52929917140489 (23 : ZMod 52929917140489) ?_ (fun q hq hd => ?_)
  · rw [show 52929917140489 - 1 = 52929917140488 from by norm_num]
    reduce_mod_char
  · have e : 52929917140489 - 1 = [2 ^ 3, 3 ^ 1, 53 ^ 1, 113 ^ 1, 368243983 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52929917140489 - 1) / 2 = 26464958570244 from by norm_num]
      have h2 : (23 : ZMod 52929917140489) ^ 26464958570244 = ((52929917140488 : ℕ) : ZMod 52929917140489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52929917140489 - 1) / 3 = 17643305713496 from by norm_num]
      have h2 : (23 : ZMod 52929917140489) ^ 17643305713496 = ((9635924399271 : ℕ) : ZMod 52929917140489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52929917140489 - 1) / 53 = 998677681896 from by norm_num]
      have h2 : (23 : ZMod 52929917140489) ^ 998677681896 = ((49255502806681 : ℕ) : ZMod 52929917140489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52929917140489 - 1) / 113 = 468406346376 from by norm_num]
      have h2 : (23 : ZMod 52929917140489) ^ 468406346376 = ((42873891790588 : ℕ) : ZMod 52929917140489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_368243983).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52929917140489 - 1) / 368243983 = 143736 from by norm_num]
      have h2 : (23 : ZMod 52929917140489) ^ 143736 = ((10203977377830 : ℕ) : ZMod 52929917140489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7044625728241 : Nat.Prime 7044625728241 := by
  refine lucas_primality 7044625728241 (11 : ZMod 7044625728241) ?_ (fun q hq hd => ?_)
  · rw [show 7044625728241 - 1 = 7044625728240 from by norm_num]
    reduce_mod_char
  · have e : 7044625728241 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17 ^ 1, 29 ^ 1, 443 ^ 1, 134399 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 2 = 3522312864120 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 3522312864120 = ((7044625728240 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 3 = 2348208576080 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 2348208576080 = ((5128139040002 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 5 = 1408925145648 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 1408925145648 = ((4121934551935 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 17 = 414389748720 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 414389748720 = ((5087959802391 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 29 = 242918128560 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 242918128560 = ((689600927018 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 443 = 15902089680 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 15902089680 = ((6673441872620 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7044625728241 - 1) / 134399 = 52415760 from by norm_num]
      have h2 : (11 : ZMod 7044625728241) ^ 52415760 = ((5319914562657 : ℕ) : ZMod 7044625728241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_211197634469030854488137501976187207 : Nat.Prime 211197634469030854488137501976187207 := by
  refine lucas_primality 211197634469030854488137501976187207 (5 : ZMod 211197634469030854488137501976187207) ?_ (fun q hq hd => ?_)
  · rw [show 211197634469030854488137501976187207 - 1 = 211197634469030854488137501976187206 from by norm_num]
    reduce_mod_char
  · have e : 211197634469030854488137501976187207 - 1 = [2 ^ 1, 3 ^ 1, 593 ^ 1, 159193 ^ 1, 7044625728241 ^ 1, 52929917140489 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 2 = 105598817234515427244068750988093603 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 105598817234515427244068750988093603 = ((211197634469030854488137501976187206 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 3 = 70399211489676951496045833992062402 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 70399211489676951496045833992062402 = ((184032251085232006930489111958422790 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 593 = 356151154247944105376285838071142 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 356151154247944105376285838071142 = ((43191292697893000288694796152972113 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 159193 = 1326676640738165965137521762742 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 1326676640738165965137521762742 = ((148669600048061117009938429983217503 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7044625728241).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 7044625728241 = 29979965241072589011366 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 29979965241072589011366 = ((40671429103064320219586887440391461 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_52929917140489).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211197634469030854488137501976187207 - 1) / 52929917140489 = 3990137258451783727254 from by norm_num]
      have h2 : (5 : ZMod 211197634469030854488137501976187207) ^ 3990137258451783727254 = ((148253244219700908109302406175226302 : ℕ) : ZMod 211197634469030854488137501976187207) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2919871751 : Nat.Prime 2919871751 := by
  refine lucas_primality 2919871751 (22 : ZMod 2919871751) ?_ (fun q hq hd => ?_)
  · rw [show 2919871751 - 1 = 2919871750 from by norm_num]
    reduce_mod_char
  · have e : 2919871751 - 1 = [2 ^ 1, 5 ^ 3, 61 ^ 1, 191467 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2919871751 - 1) / 2 = 1459935875 from by norm_num]
      have h2 : (22 : ZMod 2919871751) ^ 1459935875 = ((2919871750 : ℕ) : ZMod 2919871751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2919871751 - 1) / 5 = 583974350 from by norm_num]
      have h2 : (22 : ZMod 2919871751) ^ 583974350 = ((1395628279 : ℕ) : ZMod 2919871751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2919871751 - 1) / 61 = 47866750 from by norm_num]
      have h2 : (22 : ZMod 2919871751) ^ 47866750 = ((2226499331 : ℕ) : ZMod 2919871751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2919871751 - 1) / 191467 = 15250 from by norm_num]
      have h2 : (22 : ZMod 2919871751) ^ 15250 = ((1334018586 : ℕ) : ZMod 2919871751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_27263461551898213 : Nat.Prime 27263461551898213 := by
  refine lucas_primality 27263461551898213 (2 : ZMod 27263461551898213) ?_ (fun q hq hd => ?_)
  · rw [show 27263461551898213 - 1 = 27263461551898212 from by norm_num]
    reduce_mod_char
  · have e : 27263461551898213 - 1 = [2 ^ 2, 3 ^ 2, 433 ^ 1, 599 ^ 1, 2919871751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27263461551898213 - 1) / 2 = 13631730775949106 from by norm_num]
      have h2 : (2 : ZMod 27263461551898213) ^ 13631730775949106 = ((27263461551898212 : ℕ) : ZMod 27263461551898213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27263461551898213 - 1) / 3 = 9087820517299404 from by norm_num]
      have h2 : (2 : ZMod 27263461551898213) ^ 9087820517299404 = ((18746149645587212 : ℕ) : ZMod 27263461551898213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27263461551898213 - 1) / 433 = 62964114438564 from by norm_num]
      have h2 : (2 : ZMod 27263461551898213) ^ 62964114438564 = ((16620217956357172 : ℕ) : ZMod 27263461551898213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27263461551898213 - 1) / 599 = 45514960854588 from by norm_num]
      have h2 : (2 : ZMod 27263461551898213) ^ 45514960854588 = ((19138040711081950 : ℕ) : ZMod 27263461551898213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2919871751).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27263461551898213 - 1) / 2919871751 = 9337212 from by norm_num]
      have h2 : (2 : ZMod 27263461551898213) ^ 9337212 = ((3027501487697438 : ℕ) : ZMod 27263461551898213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_949008479 : Nat.Prime 949008479 := by
  refine lucas_primality 949008479 (11 : ZMod 949008479) ?_ (fun q hq hd => ?_)
  · rw [show 949008479 - 1 = 949008478 from by norm_num]
    reduce_mod_char
  · have e : 949008479 - 1 = [2 ^ 1, 11 ^ 1, 349 ^ 1, 123601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (949008479 - 1) / 2 = 474504239 from by norm_num]
      have h2 : (11 : ZMod 949008479) ^ 474504239 = ((949008478 : ℕ) : ZMod 949008479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (949008479 - 1) / 11 = 86273498 from by norm_num]
      have h2 : (11 : ZMod 949008479) ^ 86273498 = ((443681532 : ℕ) : ZMod 949008479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (949008479 - 1) / 349 = 2719222 from by norm_num]
      have h2 : (11 : ZMod 949008479) ^ 2719222 = ((60516550 : ℕ) : ZMod 949008479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (949008479 - 1) / 123601 = 7678 from by norm_num]
      have h2 : (11 : ZMod 949008479) ^ 7678 = ((550015357 : ℕ) : ZMod 949008479) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_855771161348957807 : Nat.Prime 855771161348957807 := by
  refine lucas_primality 855771161348957807 (5 : ZMod 855771161348957807) ?_ (fun q hq hd => ?_)
  · rw [show 855771161348957807 - 1 = 855771161348957806 from by norm_num]
    reduce_mod_char
  · have e : 855771161348957807 - 1 = [2 ^ 1, 43 ^ 1, 10485499 ^ 1, 949008479 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (855771161348957807 - 1) / 2 = 427885580674478903 from by norm_num]
      have h2 : (5 : ZMod 855771161348957807) ^ 427885580674478903 = ((855771161348957806 : ℕ) : ZMod 855771161348957807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (855771161348957807 - 1) / 43 = 19901654915092042 from by norm_num]
      have h2 : (5 : ZMod 855771161348957807) ^ 19901654915092042 = ((217207866095582860 : ℕ) : ZMod 855771161348957807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (855771161348957807 - 1) / 10485499 = 81614729194 from by norm_num]
      have h2 : (5 : ZMod 855771161348957807) ^ 81614729194 = ((244953871223433912 : ℕ) : ZMod 855771161348957807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_949008479).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (855771161348957807 - 1) / 949008479 = 901752914 from by norm_num]
      have h2 : (5 : ZMod 855771161348957807) ^ 901752914 = ((405993752234664194 : ℕ) : ZMod 855771161348957807) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18297294547071747808935421 : Nat.Prime 18297294547071747808935421 := by
  refine lucas_primality 18297294547071747808935421 (2 : ZMod 18297294547071747808935421) ?_ (fun q hq hd => ?_)
  · rw [show 18297294547071747808935421 - 1 = 18297294547071747808935420 from by norm_num]
    reduce_mod_char
  · have e : 18297294547071747808935421 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 356351 ^ 1, 855771161348957807 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18297294547071747808935421 - 1) / 2 = 9148647273535873904467710 from by norm_num]
      have h2 : (2 : ZMod 18297294547071747808935421) ^ 9148647273535873904467710 = ((18297294547071747808935420 : ℕ) : ZMod 18297294547071747808935421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18297294547071747808935421 - 1) / 3 = 6099098182357249269645140 from by norm_num]
      have h2 : (2 : ZMod 18297294547071747808935421) ^ 6099098182357249269645140 = ((8427925500049453351925571 : ℕ) : ZMod 18297294547071747808935421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18297294547071747808935421 - 1) / 5 = 3659458909414349561787084 from by norm_num]
      have h2 : (2 : ZMod 18297294547071747808935421) ^ 3659458909414349561787084 = ((14836011133059554275128346 : ℕ) : ZMod 18297294547071747808935421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18297294547071747808935421 - 1) / 356351 = 51346269680937468420 from by norm_num]
      have h2 : (2 : ZMod 18297294547071747808935421) ^ 51346269680937468420 = ((8047795129049076348924820 : ℕ) : ZMod 18297294547071747808935421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_855771161348957807).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18297294547071747808935421 - 1) / 855771161348957807 = 21381060 from by norm_num]
      have h2 : (2 : ZMod 18297294547071747808935421) ^ 21381060 = ((9659190795337113182290970 : ℕ) : ZMod 18297294547071747808935421) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2744594182060762171340313151 : Nat.Prime 2744594182060762171340313151 := by
  refine lucas_primality 2744594182060762171340313151 (11 : ZMod 2744594182060762171340313151) ?_ (fun q hq hd => ?_)
  · rw [show 2744594182060762171340313151 - 1 = 2744594182060762171340313150 from by norm_num]
    reduce_mod_char
  · have e : 2744594182060762171340313151 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 18297294547071747808935421 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2744594182060762171340313151 - 1) / 2 = 1372297091030381085670156575 from by norm_num]
      have h2 : (11 : ZMod 2744594182060762171340313151) ^ 1372297091030381085670156575 = ((2744594182060762171340313150 : ℕ) : ZMod 2744594182060762171340313151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2744594182060762171340313151 - 1) / 3 = 914864727353587390446771050 from by norm_num]
      have h2 : (11 : ZMod 2744594182060762171340313151) ^ 914864727353587390446771050 = ((2717928247792582584500949607 : ℕ) : ZMod 2744594182060762171340313151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2744594182060762171340313151 - 1) / 5 = 548918836412152434268062630 from by norm_num]
      have h2 : (11 : ZMod 2744594182060762171340313151) ^ 548918836412152434268062630 = ((1453606264487339643452434674 : ℕ) : ZMod 2744594182060762171340313151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_18297294547071747808935421).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2744594182060762171340313151 - 1) / 18297294547071747808935421 = 150 from by norm_num]
      have h2 : (11 : ZMod 2744594182060762171340313151) ^ 150 = ((892770804523145251585167005 : ℕ) : ZMod 2744594182060762171340313151) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_624158251060640521747881981606817836433 : Nat.Prime 624158251060640521747881981606817836433 := by
  refine lucas_primality 624158251060640521747881981606817836433 (5 : ZMod 624158251060640521747881981606817836433) ?_ (fun q hq hd => ?_)
  · rw [show 624158251060640521747881981606817836433 - 1 = 624158251060640521747881981606817836432 from by norm_num]
    reduce_mod_char
  · have e : 624158251060640521747881981606817836433 - 1 = [2 ^ 4, 3 ^ 1, 11 ^ 1, 13 ^ 1, 151 ^ 1, 313 ^ 1, 701 ^ 1, 2744594182060762171340313151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 2 = 312079125530320260873940990803408918216 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 312079125530320260873940990803408918216 = ((624158251060640521747881981606817836432 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 3 = 208052750353546840582627327202272612144 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 208052750353546840582627327202272612144 = ((444397868148107194432521102587807740864 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 11 = 56741659187330956522534725600619803312 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 56741659187330956522534725600619803312 = ((458524658588632152984537497693211143633 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 13 = 48012173158510809365221690892832141264 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 48012173158510809365221690892832141264 = ((521953380453764525886133611864965830984 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 151 = 4133498351394970342701205176204091632 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 4133498351394970342701205176204091632 = ((624158251060640521747881981603331052032 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 313 = 1994115818085113488012402497146382864 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 1994115818085113488012402497146382864 = ((600807584996995991567066384254653396024 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 701 = 890382669130728276387848761208014032 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 890382669130728276387848761208014032 = ((318738226327877737069633214418877398114 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2744594182060762171340313151).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (624158251060640521747881981606817836433 - 1) / 2744594182060762171340313151 = 227413675632 from by norm_num]
      have h2 : (5 : ZMod 624158251060640521747881981606817836433) ^ 227413675632 = ((32059952455226703204059340111117307599 : ℕ) : ZMod 624158251060640521747881981606817836433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_312079125530320260873940990803408918217 : Nat.Prime 312079125530320260873940990803408918217 := by
  refine lucas_primality 312079125530320260873940990803408918217 (5 : ZMod 312079125530320260873940990803408918217) ?_ (fun q hq hd => ?_)
  · rw [show 312079125530320260873940990803408918217 - 1 = 312079125530320260873940990803408918216 from by norm_num]
    reduce_mod_char
  · have e : 312079125530320260873940990803408918217 - 1 = [2 ^ 3, 3 ^ 1, 11 ^ 1, 13 ^ 1, 151 ^ 1, 313 ^ 1, 701 ^ 1, 2744594182060762171340313151 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 2 = 156039562765160130436970495401704459108 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 156039562765160130436970495401704459108 = ((312079125530320260873940990803408918216 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 3 = 104026375176773420291313663601136306072 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 104026375176773420291313663601136306072 = ((121455592797503079754487316233113777074 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 11 = 28370829593665478261267362800309901656 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 28370829593665478261267362800309901656 = ((306711956504309430269620207578819124145 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 13 = 24006086579255404682610845446416070632 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 24006086579255404682610845446416070632 = ((175285592526562112273449998725314140138 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 151 = 2066749175697485171350602588102045816 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 2066749175697485171350602588102045816 = ((33634087332372013937960667714422905700 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 313 = 997057909042556744006201248573191432 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 997057909042556744006201248573191432 = ((145477459534547806672775258337386658515 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 701 = 445191334565364138193924380604007016 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 445191334565364138193924380604007016 = ((184926552527173212790595007375075747320 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2744594182060762171340313151).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (312079125530320260873940990803408918217 - 1) / 2744594182060762171340313151 = 113706837816 from by norm_num]
      have h2 : (5 : ZMod 312079125530320260873940990803408918217) ^ 113706837816 = ((57211950124225020779908340370299194144 : ℕ) : ZMod 312079125530320260873940990803408918217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_554500987 : Nat.Prime 554500987 := by
  refine lucas_primality 554500987 (5 : ZMod 554500987) ?_ (fun q hq hd => ?_)
  · rw [show 554500987 - 1 = 554500986 from by norm_num]
    reduce_mod_char
  · have e : 554500987 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 757 ^ 1, 9391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (554500987 - 1) / 2 = 277250493 from by norm_num]
      have h2 : (5 : ZMod 554500987) ^ 277250493 = ((554500986 : ℕ) : ZMod 554500987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (554500987 - 1) / 3 = 184833662 from by norm_num]
      have h2 : (5 : ZMod 554500987) ^ 184833662 = ((94924025 : ℕ) : ZMod 554500987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (554500987 - 1) / 13 = 42653922 from by norm_num]
      have h2 : (5 : ZMod 554500987) ^ 42653922 = ((532917691 : ℕ) : ZMod 554500987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (554500987 - 1) / 757 = 732498 from by norm_num]
      have h2 : (5 : ZMod 554500987) ^ 732498 = ((292962243 : ℕ) : ZMod 554500987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (554500987 - 1) / 9391 = 59046 from by norm_num]
      have h2 : (5 : ZMod 554500987) ^ 59046 = ((47504039 : ℕ) : ZMod 554500987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10450644613925833 : Nat.Prime 10450644613925833 := by
  refine lucas_primality 10450644613925833 (10 : ZMod 10450644613925833) ?_ (fun q hq hd => ?_)
  · rw [show 10450644613925833 - 1 = 10450644613925832 from by norm_num]
    reduce_mod_char
  · have e : 10450644613925833 - 1 = [2 ^ 3, 3 ^ 2, 19 ^ 1, 23 ^ 1, 599 ^ 1, 554500987 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 2 = 5225322306962916 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 5225322306962916 = ((10450644613925832 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 3 = 3483548204641944 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 3483548204641944 = ((4637371616209050 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 19 = 550033927048728 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 550033927048728 = ((2389749975175313 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 23 = 454375852779384 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 454375852779384 = ((3148000042820761 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 599 = 17446819054968 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 17446819054968 = ((2186000770709295 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_554500987).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10450644613925833 - 1) / 554500987 = 18846936 from by norm_num]
      have h2 : (10 : ZMod 10450644613925833) ^ 18846936 = ((9448266653372204 : ℕ) : ZMod 10450644613925833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_207699789684066106935217 : Nat.Prime 207699789684066106935217 := by
  refine lucas_primality 207699789684066106935217 (5 : ZMod 207699789684066106935217) ?_ (fun q hq hd => ?_)
  · rw [show 207699789684066106935217 - 1 = 207699789684066106935216 from by norm_num]
    reduce_mod_char
  · have e : 207699789684066106935217 - 1 = [2 ^ 4, 3 ^ 1, 414049 ^ 1, 10450644613925833 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207699789684066106935217 - 1) / 2 = 103849894842033053467608 from by norm_num]
      have h2 : (5 : ZMod 207699789684066106935217) ^ 103849894842033053467608 = ((207699789684066106935216 : ℕ) : ZMod 207699789684066106935217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207699789684066106935217 - 1) / 3 = 69233263228022035645072 from by norm_num]
      have h2 : (5 : ZMod 207699789684066106935217) ^ 69233263228022035645072 = ((65865260009233305677609 : ℕ) : ZMod 207699789684066106935217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207699789684066106935217 - 1) / 414049 = 501630941468439984 from by norm_num]
      have h2 : (5 : ZMod 207699789684066106935217) ^ 501630941468439984 = ((93849605791108386039241 : ℕ) : ZMod 207699789684066106935217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_10450644613925833).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (207699789684066106935217 - 1) / 10450644613925833 = 19874352 from by norm_num]
      have h2 : (5 : ZMod 207699789684066106935217) ^ 19874352 = ((33960090639620122571618 : ℕ) : ZMod 207699789684066106935217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_32082958650930942362102683442981 : Nat.Prime 32082958650930942362102683442981 := by
  refine lucas_primality 32082958650930942362102683442981 (2 : ZMod 32082958650930942362102683442981) ?_ (fun q hq hd => ?_)
  · rw [show 32082958650930942362102683442981 - 1 = 32082958650930942362102683442980 from by norm_num]
    reduce_mod_char
  · have e : 32082958650930942362102683442981 - 1 = [2 ^ 2, 5 ^ 1, 11 ^ 1, 702127 ^ 1, 207699789684066106935217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32082958650930942362102683442981 - 1) / 2 = 16041479325465471181051341721490 from by norm_num]
      have h2 : (2 : ZMod 32082958650930942362102683442981) ^ 16041479325465471181051341721490 = ((32082958650930942362102683442980 : ℕ) : ZMod 32082958650930942362102683442981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32082958650930942362102683442981 - 1) / 5 = 6416591730186188472420536688596 from by norm_num]
      have h2 : (2 : ZMod 32082958650930942362102683442981) ^ 6416591730186188472420536688596 = ((11395105666079853250891885532151 : ℕ) : ZMod 32082958650930942362102683442981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32082958650930942362102683442981 - 1) / 11 = 2916632604630085669282062131180 from by norm_num]
      have h2 : (2 : ZMod 32082958650930942362102683442981) ^ 2916632604630085669282062131180 = ((15001077350318782763762326291674 : ℕ) : ZMod 32082958650930942362102683442981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32082958650930942362102683442981 - 1) / 702127 = 45693953730494543525747740 from by norm_num]
      have h2 : (2 : ZMod 32082958650930942362102683442981) ^ 45693953730494543525747740 = ((12619824410519764459607204754156 : ℕ) : ZMod 32082958650930942362102683442981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_207699789684066106935217).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32082958650930942362102683442981 - 1) / 207699789684066106935217 = 154467940 from by norm_num]
      have h2 : (2 : ZMod 32082958650930942362102683442981) ^ 154467940 = ((1500367490091282680386245420268 : ℕ) : ZMod 32082958650930942362102683442981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_582664694022060378487303494994260032536305143468203 : Nat.Prime 582664694022060378487303494994260032536305143468203 := by
  refine lucas_primality 582664694022060378487303494994260032536305143468203 (2 : ZMod 582664694022060378487303494994260032536305143468203) ?_ (fun q hq hd => ?_)
  · rw [show 582664694022060378487303494994260032536305143468203 - 1 = 582664694022060378487303494994260032536305143468202 from by norm_num]
    reduce_mod_char
  · have e : 582664694022060378487303494994260032536305143468203 - 1 = [2 ^ 1, 3 ^ 2, 613 ^ 1, 14683 ^ 1, 20549 ^ 1, 5455139 ^ 1, 32082958650930942362102683442981 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 2 = 291332347011030189243651747497130016268152571734101 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 291332347011030189243651747497130016268152571734101 = ((582664694022060378487303494994260032536305143468202 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 3 = 194221564674020126162434498331420010845435047822734 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 194221564674020126162434498331420010845435047822734 = ((9957682943378502327143533893196549507617115557095 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 613 = 950513367083295886602452683514290428281085062754 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 950513367083295886602452683514290428281085062754 = ((582664694022060378487303494994260032536294683115000 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 14683 = 39682945857253992950167097663574203673384536094 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 39682945857253992950167097663574203673384536094 = ((165562773869328367551669994262796627467499748229830 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 20549 = 28354892891238521508944644264648402965414625698 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 28354892891238521508944644264648402965414625698 = ((260631483144280460859291661229016080533355522127386 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 5455139 = 106810237836663809755774049936080461476106318 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 106810237836663809755774049936080461476106318 = ((444596037036326356417406746780701917728990982927023 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_32082958650930942362102683442981).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582664694022060378487303494994260032536305143468203 - 1) / 32082958650930942362102683442981 = 18161189569876323042 from by norm_num]
      have h2 : (2 : ZMod 582664694022060378487303494994260032536305143468203) ^ 18161189569876323042 = ((231024438076346398323568175333431699634225658239303 : ℕ) : ZMod 582664694022060378487303494994260032536305143468203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1662430939291 : Nat.Prime 1662430939291 := by
  refine lucas_primality 1662430939291 (10 : ZMod 1662430939291) ?_ (fun q hq hd => ?_)
  · rw [show 1662430939291 - 1 = 1662430939290 from by norm_num]
    reduce_mod_char
  · have e : 1662430939291 - 1 = [2 ^ 1, 3 ^ 3, 5 ^ 1, 11 ^ 1, 241 ^ 1, 2322577 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 2 = 831215469645 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 831215469645 = ((1662430939290 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 3 = 554143646430 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 554143646430 = ((557298366252 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 5 = 332486187858 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 332486187858 = ((196254467702 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 11 = 151130085390 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 151130085390 = ((1373209087681 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 241 = 6898053690 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 6898053690 = ((329111770491 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1662430939291 - 1) / 2322577 = 715770 from by norm_num]
      have h2 : (10 : ZMod 1662430939291) ^ 715770 = ((1082267716768 : ℕ) : ZMod 1662430939291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12520624214056907824237 : Nat.Prime 12520624214056907824237 := by
  refine lucas_primality 12520624214056907824237 (2 : ZMod 12520624214056907824237) ?_ (fun q hq hd => ?_)
  · rw [show 12520624214056907824237 - 1 = 12520624214056907824236 from by norm_num]
    reduce_mod_char
  · have e : 12520624214056907824237 - 1 = [2 ^ 2, 3 ^ 2, 139 ^ 1, 1505099 ^ 1, 1662430939291 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12520624214056907824237 - 1) / 2 = 6260312107028453912118 from by norm_num]
      have h2 : (2 : ZMod 12520624214056907824237) ^ 6260312107028453912118 = ((12520624214056907824236 : ℕ) : ZMod 12520624214056907824237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12520624214056907824237 - 1) / 3 = 4173541404685635941412 from by norm_num]
      have h2 : (2 : ZMod 12520624214056907824237) ^ 4173541404685635941412 = ((5846459264412271762053 : ℕ) : ZMod 12520624214056907824237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12520624214056907824237 - 1) / 139 = 90076433194654013124 from by norm_num]
      have h2 : (2 : ZMod 12520624214056907824237) ^ 90076433194654013124 = ((5718384044619230721620 : ℕ) : ZMod 12520624214056907824237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12520624214056907824237 - 1) / 1505099 = 8318804420212164 from by norm_num]
      have h2 : (2 : ZMod 12520624214056907824237) ^ 8318804420212164 = ((11015126771290467160391 : ℕ) : ZMod 12520624214056907824237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1662430939291).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12520624214056907824237 - 1) / 1662430939291 = 7531515396 from by norm_num]
      have h2 : (2 : ZMod 12520624214056907824237) ^ 7531515396 = ((6802103882235865282657 : ℕ) : ZMod 12520624214056907824237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15099872802152630836029823 : Nat.Prime 15099872802152630836029823 := by
  refine lucas_primality 15099872802152630836029823 (3 : ZMod 15099872802152630836029823) ?_ (fun q hq hd => ?_)
  · rw [show 15099872802152630836029823 - 1 = 15099872802152630836029822 from by norm_num]
    reduce_mod_char
  · have e : 15099872802152630836029823 - 1 = [2 ^ 1, 3 ^ 2, 67 ^ 1, 12520624214056907824237 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15099872802152630836029823 - 1) / 2 = 7549936401076315418014911 from by norm_num]
      have h2 : (3 : ZMod 15099872802152630836029823) ^ 7549936401076315418014911 = ((15099872802152630836029822 : ℕ) : ZMod 15099872802152630836029823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15099872802152630836029823 - 1) / 3 = 5033290934050876945343274 from by norm_num]
      have h2 : (3 : ZMod 15099872802152630836029823) ^ 5033290934050876945343274 = ((13303685374551029335964403 : ℕ) : ZMod 15099872802152630836029823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15099872802152630836029823 - 1) / 67 = 225371235853024340836266 from by norm_num]
      have h2 : (3 : ZMod 15099872802152630836029823) ^ 225371235853024340836266 = ((408816901533651184253357 : ℕ) : ZMod 15099872802152630836029823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_12520624214056907824237).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15099872802152630836029823 - 1) / 12520624214056907824237 = 1206 from by norm_num]
      have h2 : (3 : ZMod 15099872802152630836029823) ^ 1206 = ((14948231206858103010893508 : ℕ) : ZMod 15099872802152630836029823) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_112796049832080152345142777811 : Nat.Prime 112796049832080152345142777811 := by
  refine lucas_primality 112796049832080152345142777811 (3 : ZMod 112796049832080152345142777811) ?_ (fun q hq hd => ?_)
  · rw [show 112796049832080152345142777811 - 1 = 112796049832080152345142777810 from by norm_num]
    reduce_mod_char
  · have e : 112796049832080152345142777811 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 83 ^ 1, 15099872802152630836029823 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112796049832080152345142777811 - 1) / 2 = 56398024916040076172571388905 from by norm_num]
      have h2 : (3 : ZMod 112796049832080152345142777811) ^ 56398024916040076172571388905 = ((112796049832080152345142777810 : ℕ) : ZMod 112796049832080152345142777811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112796049832080152345142777811 - 1) / 3 = 37598683277360050781714259270 from by norm_num]
      have h2 : (3 : ZMod 112796049832080152345142777811) ^ 37598683277360050781714259270 = ((66620890519678016062559406549 : ℕ) : ZMod 112796049832080152345142777811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112796049832080152345142777811 - 1) / 5 = 22559209966416030469028555562 from by norm_num]
      have h2 : (3 : ZMod 112796049832080152345142777811) ^ 22559209966416030469028555562 = ((39325111194496270915609153021 : ℕ) : ZMod 112796049832080152345142777811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112796049832080152345142777811 - 1) / 83 = 1358988552193736775242684070 from by norm_num]
      have h2 : (3 : ZMod 112796049832080152345142777811) ^ 1358988552193736775242684070 = ((83508208536539769471850360952 : ℕ) : ZMod 112796049832080152345142777811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15099872802152630836029823).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (112796049832080152345142777811 - 1) / 15099872802152630836029823 = 7470 from by norm_num]
      have h2 : (3 : ZMod 112796049832080152345142777811) ^ 7470 = ((96222366440292718035440620934 : ℕ) : ZMod 112796049832080152345142777811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14421832221010171286484327228247713601 : Nat.Prime 14421832221010171286484327228247713601 := by
  refine lucas_primality 14421832221010171286484327228247713601 (11 : ZMod 14421832221010171286484327228247713601) ?_ (fun q hq hd => ?_)
  · rw [show 14421832221010171286484327228247713601 - 1 = 14421832221010171286484327228247713600 from by norm_num]
    reduce_mod_char
  · have e : 14421832221010171286484327228247713601 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 2, 13 ^ 1, 683 ^ 1, 112796049832080152345142777811 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 2 = 7210916110505085643242163614123856800 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 7210916110505085643242163614123856800 = ((14421832221010171286484327228247713600 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 3 = 4807277407003390428828109076082571200 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 4807277407003390428828109076082571200 = ((8704375380219563583030108267915854491 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 5 = 2884366444202034257296865445649542720 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 2884366444202034257296865445649542720 = ((6800052877340009495884634105770716844 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 13 = 1109371709308474714344948248326747200 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 1109371709308474714344948248326747200 = ((12795388060334223181098166906777181269 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 683 = 21115420528565404519010728006219200 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 21115420528565404519010728006219200 = ((7079274196925942380605978987376641035 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_112796049832080152345142777811).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14421832221010171286484327228247713601 - 1) / 112796049832080152345142777811 = 127857600 from by norm_num]
      have h2 : (11 : ZMod 14421832221010171286484327228247713601) ^ 127857600 = ((12509157121324050530303096795981499215 : ℕ) : ZMod 14421832221010171286484327228247713601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17236983499017921972849595101062911347678496967884099 : Nat.Prime 17236983499017921972849595101062911347678496967884099 := by
  refine lucas_primality 17236983499017921972849595101062911347678496967884099 (2 : ZMod 17236983499017921972849595101062911347678496967884099) ?_ (fun q hq hd => ?_)
  · rw [show 17236983499017921972849595101062911347678496967884099 - 1 = 17236983499017921972849595101062911347678496967884098 from by norm_num]
    reduce_mod_char
  · have e : 17236983499017921972849595101062911347678496967884099 - 1 = [2 ^ 1, 3 ^ 1, 139 ^ 1, 617 ^ 1, 1223 ^ 1, 1899167 ^ 1, 14421832221010171286484327228247713601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 2 = 8618491749508960986424797550531455673839248483942049 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 8618491749508960986424797550531455673839248483942049 = ((17236983499017921972849595101062911347678496967884098 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 3 = 5745661166339307324283198367020970449226165655961366 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 5745661166339307324283198367020970449226165655961366 = ((5202589229185447125382240105625634607656244715315712 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 139 = 124007075532503035775896367633546124803442424229382 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 124007075532503035775896367633546124803442424229382 = ((2401692237475648340875224049127613918348125770881073 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 617 = 27936764179931802225039862400426112394940837873394 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 27936764179931802225039862400426112394940837873394 = ((8227574549135616531516739139949033810305666844839213 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 1223 = 14094017578918987712877837367999109850922728510126 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 14094017578918987712877837367999109850922728510126 = ((13236649452097038774093866817503865545069759580287078 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 1899167 = 9076075721101894658473738802887219158546087294 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 9076075721101894658473738802887219158546087294 = ((13524438004226712231412135820142748324639168908866821 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14421832221010171286484327228247713601).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17236983499017921972849595101062911347678496967884099 - 1) / 14421832221010171286484327228247713601 = 1195200667631298 from by norm_num]
      have h2 : (2 : ZMod 17236983499017921972849595101062911347678496967884099) ^ 1195200667631298 = ((6527876499484159475148389664783322913980184699024841 : ℕ) : ZMod 17236983499017921972849595101062911347678496967884099) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11383690387 : Nat.Prime 11383690387 := by
  refine lucas_primality 11383690387 (3 : ZMod 11383690387) ?_ (fun q hq hd => ?_)
  · rw [show 11383690387 - 1 = 11383690386 from by norm_num]
    reduce_mod_char
  · have e : 11383690387 - 1 = [2 ^ 1, 3 ^ 1, 829 ^ 1, 1063 ^ 1, 2153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11383690387 - 1) / 2 = 5691845193 from by norm_num]
      have h2 : (3 : ZMod 11383690387) ^ 5691845193 = ((11383690386 : ℕ) : ZMod 11383690387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11383690387 - 1) / 3 = 3794563462 from by norm_num]
      have h2 : (3 : ZMod 11383690387) ^ 3794563462 = ((5569954617 : ℕ) : ZMod 11383690387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11383690387 - 1) / 829 = 13731834 from by norm_num]
      have h2 : (3 : ZMod 11383690387) ^ 13731834 = ((913943129 : ℕ) : ZMod 11383690387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11383690387 - 1) / 1063 = 10709022 from by norm_num]
      have h2 : (3 : ZMod 11383690387) ^ 10709022 = ((3555094008 : ℕ) : ZMod 11383690387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11383690387 - 1) / 2153 = 5287362 from by norm_num]
      have h2 : (3 : ZMod 11383690387) ^ 5287362 = ((6070887221 : ℕ) : ZMod 11383690387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28462659967079735788297 : Nat.Prime 28462659967079735788297 := by
  refine lucas_primality 28462659967079735788297 (5 : ZMod 28462659967079735788297) ?_ (fun q hq hd => ?_)
  · rw [show 28462659967079735788297 - 1 = 28462659967079735788296 from by norm_num]
    reduce_mod_char
  · have e : 28462659967079735788297 - 1 = [2 ^ 3, 3 ^ 2, 313 ^ 1, 1801 ^ 1, 61603 ^ 1, 11383690387 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 2 = 14231329983539867894148 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 14231329983539867894148 = ((28462659967079735788296 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 3 = 9487553322359911929432 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 9487553322359911929432 = ((22791689659694373916061 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 313 = 90935015869264331592 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 90935015869264331592 = ((15870758644590338948281 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 1801 = 15803808976723895496 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 15803808976723895496 = ((6230740896479163152589 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 61603 = 462033666657139032 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 462033666657139032 = ((8731170718815860470817 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11383690387).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28462659967079735788297 - 1) / 11383690387 = 2500301659608 from by norm_num]
      have h2 : (5 : ZMod 28462659967079735788297) ^ 2500301659608 = ((13740756498410037239982 : ℕ) : ZMod 28462659967079735788297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138336073 : Nat.Prime 138336073 := by
  refine lucas_primality 138336073 (15 : ZMod 138336073) ?_ (fun q hq hd => ?_)
  · rw [show 138336073 - 1 = 138336072 from by norm_num]
    reduce_mod_char
  · have e : 138336073 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 17 ^ 1, 48437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138336073 - 1) / 2 = 69168036 from by norm_num]
      have h2 : (15 : ZMod 138336073) ^ 69168036 = ((138336072 : ℕ) : ZMod 138336073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138336073 - 1) / 3 = 46112024 from by norm_num]
      have h2 : (15 : ZMod 138336073) ^ 46112024 = ((15537414 : ℕ) : ZMod 138336073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138336073 - 1) / 7 = 19762296 from by norm_num]
      have h2 : (15 : ZMod 138336073) ^ 19762296 = ((55128469 : ℕ) : ZMod 138336073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138336073 - 1) / 17 = 8137416 from by norm_num]
      have h2 : (15 : ZMod 138336073) ^ 8137416 = ((43632474 : ℕ) : ZMod 138336073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138336073 - 1) / 48437 = 2856 from by norm_num]
      have h2 : (15 : ZMod 138336073) ^ 2856 = ((79855981 : ℕ) : ZMod 138336073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3794406154453232489 : Nat.Prime 3794406154453232489 := by
  refine lucas_primality 3794406154453232489 (3 : ZMod 3794406154453232489) ?_ (fun q hq hd => ?_)
  · rw [show 3794406154453232489 - 1 = 3794406154453232488 from by norm_num]
    reduce_mod_char
  · have e : 3794406154453232489 - 1 = [2 ^ 3, 101 ^ 1, 461 ^ 1, 73637 ^ 1, 138336073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3794406154453232489 - 1) / 2 = 1897203077226616244 from by norm_num]
      have h2 : (3 : ZMod 3794406154453232489) ^ 1897203077226616244 = ((3794406154453232488 : ℕ) : ZMod 3794406154453232489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3794406154453232489 - 1) / 101 = 37568377766863688 from by norm_num]
      have h2 : (3 : ZMod 3794406154453232489) ^ 37568377766863688 = ((1506015977815234817 : ℕ) : ZMod 3794406154453232489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3794406154453232489 - 1) / 461 = 8230815953260808 from by norm_num]
      have h2 : (3 : ZMod 3794406154453232489) ^ 8230815953260808 = ((67215046763863548 : ℕ) : ZMod 3794406154453232489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3794406154453232489 - 1) / 73637 = 51528527159624 from by norm_num]
      have h2 : (3 : ZMod 3794406154453232489) ^ 51528527159624 = ((2715026872785719952 : ℕ) : ZMod 3794406154453232489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_138336073).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3794406154453232489 - 1) / 138336073 = 27428898856 from by norm_num]
      have h2 : (3 : ZMod 3794406154453232489) ^ 27428898856 = ((3459100271357480033 : ℕ) : ZMod 3794406154453232489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_64675734285078548487935424073 : Nat.Prime 64675734285078548487935424073 := by
  refine lucas_primality 64675734285078548487935424073 (15 : ZMod 64675734285078548487935424073) ?_ (fun q hq hd => ?_)
  · rw [show 64675734285078548487935424073 - 1 = 64675734285078548487935424072 from by norm_num]
    reduce_mod_char
  · have e : 64675734285078548487935424073 - 1 = [2 ^ 3, 3 ^ 2, 7 ^ 1, 13 ^ 1, 19 ^ 1, 269 ^ 1, 509 ^ 1, 3794406154453232489 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 2 = 32337867142539274243967712036 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 32337867142539274243967712036 = ((64675734285078548487935424072 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 3 = 21558578095026182829311808024 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 21558578095026182829311808024 = ((20439555140958230494409018154 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 7 = 9239390612154078355419346296 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 9239390612154078355419346296 = ((50495513861350660968770151774 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 13 = 4975056483467580652918109544 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 4975056483467580652918109544 = ((24427945155940624796566747656 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 19 = 3403986015004134130943969688 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 3403986015004134130943969688 = ((53584919121563360609019800225 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 269 = 240430238977987169100131688 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 240430238977987169100131688 = ((59989488616422279429783278908 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 509 = 127064310972649407638380008 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 127064310972649407638380008 = ((18646176207007940289310620886 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3794406154453232489).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64675734285078548487935424073 - 1) / 3794406154453232489 = 17045021448 from by norm_num]
      have h2 : (15 : ZMod 64675734285078548487935424073) ^ 17045021448 = ((57221292831899440655748929137 : ℕ) : ZMod 64675734285078548487935424073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1541167907 : Nat.Prime 1541167907 := by
  refine lucas_primality 1541167907 (2 : ZMod 1541167907) ?_ (fun q hq hd => ?_)
  · rw [show 1541167907 - 1 = 1541167906 from by norm_num]
    reduce_mod_char
  · have e : 1541167907 - 1 = [2 ^ 1, 823 ^ 1, 936311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1541167907 - 1) / 2 = 770583953 from by norm_num]
      have h2 : (2 : ZMod 1541167907) ^ 770583953 = ((1541167906 : ℕ) : ZMod 1541167907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1541167907 - 1) / 823 = 1872622 from by norm_num]
      have h2 : (2 : ZMod 1541167907) ^ 1872622 = ((388905032 : ℕ) : ZMod 1541167907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1541167907 - 1) / 936311 = 1646 from by norm_num]
      have h2 : (2 : ZMod 1541167907) ^ 1646 = ((995150345 : ℕ) : ZMod 1541167907) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_261998544191 : Nat.Prime 261998544191 := by
  refine lucas_primality 261998544191 (13 : ZMod 261998544191) ?_ (fun q hq hd => ?_)
  · rw [show 261998544191 - 1 = 261998544190 from by norm_num]
    reduce_mod_char
  · have e : 261998544191 - 1 = [2 ^ 1, 5 ^ 1, 17 ^ 1, 1541167907 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261998544191 - 1) / 2 = 130999272095 from by norm_num]
      have h2 : (13 : ZMod 261998544191) ^ 130999272095 = ((261998544190 : ℕ) : ZMod 261998544191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261998544191 - 1) / 5 = 52399708838 from by norm_num]
      have h2 : (13 : ZMod 261998544191) ^ 52399708838 = ((238136498770 : ℕ) : ZMod 261998544191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261998544191 - 1) / 17 = 15411679070 from by norm_num]
      have h2 : (13 : ZMod 261998544191) ^ 15411679070 = ((114904598209 : ℕ) : ZMod 261998544191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1541167907).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (261998544191 - 1) / 1541167907 = 170 from by norm_num]
      have h2 : (13 : ZMod 261998544191) ^ 170 = ((205355009487 : ℕ) : ZMod 261998544191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11306568509 : Nat.Prime 11306568509 := by
  refine lucas_primality 11306568509 (2 : ZMod 11306568509) ?_ (fun q hq hd => ?_)
  · rw [show 11306568509 - 1 = 11306568508 from by norm_num]
    reduce_mod_char
  · have e : 11306568509 - 1 = [2 ^ 2, 10457 ^ 1, 270311 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11306568509 - 1) / 2 = 5653284254 from by norm_num]
      have h2 : (2 : ZMod 11306568509) ^ 5653284254 = ((11306568508 : ℕ) : ZMod 11306568509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11306568509 - 1) / 10457 = 1081244 from by norm_num]
      have h2 : (2 : ZMod 11306568509) ^ 1081244 = ((3909430493 : ℕ) : ZMod 11306568509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11306568509 - 1) / 270311 = 41828 from by norm_num]
      have h2 : (2 : ZMod 11306568509) ^ 41828 = ((3362775243 : ℕ) : ZMod 11306568509) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_126170538473855459870995755264812959134139669176057183246713 : Nat.Prime 126170538473855459870995755264812959134139669176057183246713 := by
  refine lucas_primality 126170538473855459870995755264812959134139669176057183246713 (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ?_ (fun q hq hd => ?_)
  · rw [show 126170538473855459870995755264812959134139669176057183246713 - 1 = 126170538473855459870995755264812959134139669176057183246712 from by norm_num]
    reduce_mod_char
  · have e : 126170538473855459870995755264812959134139669176057183246713 - 1 = [2 ^ 3, 7 ^ 1, 157 ^ 1, 74903 ^ 1, 11306568509 ^ 1, 261998544191 ^ 1, 64675734285078548487935424073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 2 = 63085269236927729935497877632406479567069834588028591623356 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 63085269236927729935497877632406479567069834588028591623356 = ((126170538473855459870995755264812959134139669176057183246712 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 7 = 18024362639122208552999393609258994162019952739436740463816 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 18024362639122208552999393609258994162019952739436740463816 = ((17663698592547260755082005064704526015197594086772681040308 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 157 = 803634003018187642490418823342757701491335472458962950616 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 803634003018187642490418823342757701491335472458962950616 = ((69647861954679418692708541792439972313093440952039089658798 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 74903 = 1684452404761564421598544187346474228457333740652005704 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 1684452404761564421598544187346474228457333740652005704 = ((76783505479069898748813600723992399173897164023973138049308 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11306568509).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 11306568509 = 11159047802471990476044773529688516667717797770968 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 11159047802471990476044773529688516667717797770968 = ((64196931476583814796973872990247632097082374368718743844185 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_261998544191).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 261998544191 = 481569616592509243493454260408268510821038698632 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 481569616592509243493454260408268510821038698632 = ((25611179768561639060927873520504445068120139448366240680012 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_64675734285078548487935424073).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126170538473855459870995755264812959134139669176057183246713 - 1) / 64675734285078548487935424073 = 1950817255784361229310093487544 from by norm_num]
      have h2 : (5 : ZMod 126170538473855459870995755264812959134139669176057183246713) ^ 1950817255784361229310093487544 = ((103315186751796765425976885761738363532988748250215835426774 : ℕ) : ZMod 126170538473855459870995755264812959134139669176057183246713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14515440586279 : Nat.Prime 14515440586279 := by
  refine lucas_primality 14515440586279 (6 : ZMod 14515440586279) ?_ (fun q hq hd => ?_)
  · rw [show 14515440586279 - 1 = 14515440586278 from by norm_num]
    reduce_mod_char
  · have e : 14515440586279 - 1 = [2 ^ 1, 3 ^ 1, 61 ^ 1, 2579 ^ 1, 15377927 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14515440586279 - 1) / 2 = 7257720293139 from by norm_num]
      have h2 : (6 : ZMod 14515440586279) ^ 7257720293139 = ((14515440586278 : ℕ) : ZMod 14515440586279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14515440586279 - 1) / 3 = 4838480195426 from by norm_num]
      have h2 : (6 : ZMod 14515440586279) ^ 4838480195426 = ((3537289448227 : ℕ) : ZMod 14515440586279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14515440586279 - 1) / 61 = 237958042398 from by norm_num]
      have h2 : (6 : ZMod 14515440586279) ^ 237958042398 = ((9472246220224 : ℕ) : ZMod 14515440586279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14515440586279 - 1) / 2579 = 5628321282 from by norm_num]
      have h2 : (6 : ZMod 14515440586279) ^ 5628321282 = ((8524096034327 : ℕ) : ZMod 14515440586279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14515440586279 - 1) / 15377927 = 943914 from by norm_num]
      have h2 : (6 : ZMod 14515440586279) ^ 943914 = ((7082525231253 : ℕ) : ZMod 14515440586279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9036732691393854241 : Nat.Prime 9036732691393854241 := by
  refine lucas_primality 9036732691393854241 (13 : ZMod 9036732691393854241) ?_ (fun q hq hd => ?_)
  · rw [show 9036732691393854241 - 1 = 9036732691393854240 from by norm_num]
    reduce_mod_char
  · have e : 9036732691393854241 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 1297 ^ 1, 14515440586279 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9036732691393854241 - 1) / 2 = 4518366345696927120 from by norm_num]
      have h2 : (13 : ZMod 9036732691393854241) ^ 4518366345696927120 = ((9036732691393854240 : ℕ) : ZMod 9036732691393854241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9036732691393854241 - 1) / 3 = 3012244230464618080 from by norm_num]
      have h2 : (13 : ZMod 9036732691393854241) ^ 3012244230464618080 = ((1730478202458495672 : ℕ) : ZMod 9036732691393854241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9036732691393854241 - 1) / 5 = 1807346538278770848 from by norm_num]
      have h2 : (13 : ZMod 9036732691393854241) ^ 1807346538278770848 = ((3614330555296836379 : ℕ) : ZMod 9036732691393854241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9036732691393854241 - 1) / 1297 = 6967411481413920 from by norm_num]
      have h2 : (13 : ZMod 9036732691393854241) ^ 6967411481413920 = ((5128992719526523490 : ℕ) : ZMod 9036732691393854241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14515440586279).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9036732691393854241 - 1) / 14515440586279 = 622560 from by norm_num]
      have h2 : (13 : ZMod 9036732691393854241) ^ 622560 = ((4837042693015995202 : ℕ) : ZMod 9036732691393854241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_40538269301 : Nat.Prime 40538269301 := by
  refine lucas_primality 40538269301 (2 : ZMod 40538269301) ?_ (fun q hq hd => ?_)
  · rw [show 40538269301 - 1 = 40538269300 from by norm_num]
    reduce_mod_char
  · have e : 40538269301 - 1 = [2 ^ 2, 5 ^ 2, 37 ^ 1, 10956289 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40538269301 - 1) / 2 = 20269134650 from by norm_num]
      have h2 : (2 : ZMod 40538269301) ^ 20269134650 = ((40538269300 : ℕ) : ZMod 40538269301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40538269301 - 1) / 5 = 8107653860 from by norm_num]
      have h2 : (2 : ZMod 40538269301) ^ 8107653860 = ((8446364478 : ℕ) : ZMod 40538269301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40538269301 - 1) / 37 = 1095628900 from by norm_num]
      have h2 : (2 : ZMod 40538269301) ^ 1095628900 = ((20248351055 : ℕ) : ZMod 40538269301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (40538269301 - 1) / 10956289 = 3700 from by norm_num]
      have h2 : (2 : ZMod 40538269301) ^ 3700 = ((5287937795 : ℕ) : ZMod 40538269301) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1053995001827 : Nat.Prime 1053995001827 := by
  refine lucas_primality 1053995001827 (2 : ZMod 1053995001827) ?_ (fun q hq hd => ?_)
  · rw [show 1053995001827 - 1 = 1053995001826 from by norm_num]
    reduce_mod_char
  · have e : 1053995001827 - 1 = [2 ^ 1, 13 ^ 1, 40538269301 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1053995001827 - 1) / 2 = 526997500913 from by norm_num]
      have h2 : (2 : ZMod 1053995001827) ^ 526997500913 = ((1053995001826 : ℕ) : ZMod 1053995001827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1053995001827 - 1) / 13 = 81076538602 from by norm_num]
      have h2 : (2 : ZMod 1053995001827) ^ 81076538602 = ((985258163506 : ℕ) : ZMod 1053995001827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_40538269301).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1053995001827 - 1) / 40538269301 = 26 from by norm_num]
      have h2 : (2 : ZMod 1053995001827) ^ 26 = ((67108864 : ℕ) : ZMod 1053995001827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17012053131775651866570892537312925929 : Nat.Prime 17012053131775651866570892537312925929 := by
  refine lucas_primality 17012053131775651866570892537312925929 (11 : ZMod 17012053131775651866570892537312925929) ?_ (fun q hq hd => ?_)
  · rw [show 17012053131775651866570892537312925929 - 1 = 17012053131775651866570892537312925928 from by norm_num]
    reduce_mod_char
  · have e : 17012053131775651866570892537312925929 - 1 = [2 ^ 3, 3 ^ 3, 8269 ^ 1, 1053995001827 ^ 1, 9036732691393854241 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17012053131775651866570892537312925929 - 1) / 2 = 8506026565887825933285446268656462964 from by norm_num]
      have h2 : (11 : ZMod 17012053131775651866570892537312925929) ^ 8506026565887825933285446268656462964 = ((17012053131775651866570892537312925928 : ℕ) : ZMod 17012053131775651866570892537312925929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17012053131775651866570892537312925929 - 1) / 3 = 5670684377258550622190297512437641976 from by norm_num]
      have h2 : (11 : ZMod 17012053131775651866570892537312925929) ^ 5670684377258550622190297512437641976 = ((15804868662890101303480448648116629254 : ℕ) : ZMod 17012053131775651866570892537312925929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17012053131775651866570892537312925929 - 1) / 8269 = 2057328955348367622030583206834312 from by norm_num]
      have h2 : (11 : ZMod 17012053131775651866570892537312925929) ^ 2057328955348367622030583206834312 = ((12126147670590553560031380791100657004 : ℕ) : ZMod 17012053131775651866570892537312925929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1053995001827).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17012053131775651866570892537312925929 - 1) / 1053995001827 = 16140544407029328635267064 from by norm_num]
      have h2 : (11 : ZMod 17012053131775651866570892537312925929) ^ 16140544407029328635267064 = ((9130980288531488388013690025962546424 : ℕ) : ZMod 17012053131775651866570892537312925929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9036732691393854241).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17012053131775651866570892537312925929 - 1) / 9036732691393854241 = 1882544688743212008 from by norm_num]
      have h2 : (11 : ZMod 17012053131775651866570892537312925929) ^ 1882544688743212008 = ((3368704521162159710554137700621364066 : ℕ) : ZMod 17012053131775651866570892537312925929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7009474359658636659499764181378497729674426065336510180373 : Nat.Prime 7009474359658636659499764181378497729674426065336510180373 := by
  refine lucas_primality 7009474359658636659499764181378497729674426065336510180373 (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ?_ (fun q hq hd => ?_)
  · rw [show 7009474359658636659499764181378497729674426065336510180373 - 1 = 7009474359658636659499764181378497729674426065336510180372 from by norm_num]
    reduce_mod_char
  · have e : 7009474359658636659499764181378497729674426065336510180373 - 1 = [2 ^ 2, 1889 ^ 1, 90911 ^ 1, 411809 ^ 1, 1456547 ^ 1, 17012053131775651866570892537312925929 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 2 = 3504737179829318329749882090689248864837213032668255090186 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 3504737179829318329749882090689248864837213032668255090186 = ((7009474359658636659499764181378497729674426065336510180372 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 1889 = 3710679915118388914504904278125197315867880394566707348 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 3710679915118388914504904278125197315867880394566707348 = ((4670673473586457234302561852658563832569928350196212714557 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 90911 = 77102598801670168180965605717443408714835675169523052 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 77102598801670168180965605717443408714835675169523052 = ((1561527835952090087281813138334243574132256819000284339360 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 411809 = 17021178166719611906247226703103860599633388452745108 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 17021178166719611906247226703103860599633388452745108 = ((4300817497376293943245009324043814805493138537976304856272 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 1456547 = 4812391470826987841449513253865819454967416818912476 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 4812391470826987841449513253865819454967416818912476 = ((4350186301844473233391130771999829374901895057198643412647 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17012053131775651866570892537312925929).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7009474359658636659499764181378497729674426065336510180373 - 1) / 17012053131775651866570892537312925929 = 412029888771398106868 from by norm_num]
      have h2 : (2 : ZMod 7009474359658636659499764181378497729674426065336510180373) ^ 412029888771398106868 = ((2667030761690619000581264866656064608271197521433964865469 : ℕ) : ZMod 7009474359658636659499764181378497729674426065336510180373) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_676611086009071 : Nat.Prime 676611086009071 := by
  refine lucas_primality 676611086009071 (3 : ZMod 676611086009071) ?_ (fun q hq hd => ?_)
  · rw [show 676611086009071 - 1 = 676611086009070 from by norm_num]
    reduce_mod_char
  · have e : 676611086009071 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 83 ^ 1, 8039 ^ 1, 33801637 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 2 = 338305543004535 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 338305543004535 = ((676611086009070 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 3 = 225537028669690 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 225537028669690 = ((657165468955867 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 5 = 135322217201814 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 135322217201814 = ((166773436756352 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 83 = 8151940795290 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 8151940795290 = ((423176493182378 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 8039 = 84166076130 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 84166076130 = ((609772792304453 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (676611086009071 - 1) / 33801637 = 20017110 from by norm_num]
      have h2 : (3 : ZMod 676611086009071) ^ 20017110 = ((574956411531142 : ℕ) : ZMod 676611086009071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_511613989 : Nat.Prime 511613989 := by
  refine lucas_primality 511613989 (2 : ZMod 511613989) ?_ (fun q hq hd => ?_)
  · rw [show 511613989 - 1 = 511613988 from by norm_num]
    reduce_mod_char
  · have e : 511613989 - 1 = [2 ^ 2, 3 ^ 1, 19 ^ 1, 47 ^ 1, 47743 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (511613989 - 1) / 2 = 255806994 from by norm_num]
      have h2 : (2 : ZMod 511613989) ^ 255806994 = ((511613988 : ℕ) : ZMod 511613989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (511613989 - 1) / 3 = 170537996 from by norm_num]
      have h2 : (2 : ZMod 511613989) ^ 170537996 = ((366745263 : ℕ) : ZMod 511613989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (511613989 - 1) / 19 = 26927052 from by norm_num]
      have h2 : (2 : ZMod 511613989) ^ 26927052 = ((210641901 : ℕ) : ZMod 511613989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (511613989 - 1) / 47 = 10885404 from by norm_num]
      have h2 : (2 : ZMod 511613989) ^ 10885404 = ((431902483 : ℕ) : ZMod 511613989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (511613989 - 1) / 47743 = 10716 from by norm_num]
      have h2 : (2 : ZMod 511613989) ^ 10716 = ((311011903 : ℕ) : ZMod 511613989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_252699498601747720280779871 : Nat.Prime 252699498601747720280779871 := by
  refine lucas_primality 252699498601747720280779871 (11 : ZMod 252699498601747720280779871) ?_ (fun q hq hd => ?_)
  · rw [show 252699498601747720280779871 - 1 = 252699498601747720280779870 from by norm_num]
    reduce_mod_char
  · have e : 252699498601747720280779871 - 1 = [2 ^ 1, 5 ^ 1, 73 ^ 1, 511613989 ^ 1, 676611086009071 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252699498601747720280779871 - 1) / 2 = 126349749300873860140389935 from by norm_num]
      have h2 : (11 : ZMod 252699498601747720280779871) ^ 126349749300873860140389935 = ((252699498601747720280779870 : ℕ) : ZMod 252699498601747720280779871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252699498601747720280779871 - 1) / 5 = 50539899720349544056155974 from by norm_num]
      have h2 : (11 : ZMod 252699498601747720280779871) ^ 50539899720349544056155974 = ((185412689062617312189162171 : ℕ) : ZMod 252699498601747720280779871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252699498601747720280779871 - 1) / 73 = 3461636967147229044942190 from by norm_num]
      have h2 : (11 : ZMod 252699498601747720280779871) ^ 3461636967147229044942190 = ((43563334338174306833351184 : ℕ) : ZMod 252699498601747720280779871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_511613989).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252699498601747720280779871 - 1) / 511613989 = 493926092786621830 from by norm_num]
      have h2 : (11 : ZMod 252699498601747720280779871) ^ 493926092786621830 = ((157728992618544694794899291 : ℕ) : ZMod 252699498601747720280779871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_676611086009071).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (252699498601747720280779871 - 1) / 676611086009071 = 373478211970 from by norm_num]
      have h2 : (11 : ZMod 252699498601747720280779871) ^ 373478211970 = ((19807597934892516385506135 : ℕ) : ZMod 252699498601747720280779871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_123523834588549530800560938945677540327 : Nat.Prime 123523834588549530800560938945677540327 := by
  refine lucas_primality 123523834588549530800560938945677540327 (5 : ZMod 123523834588549530800560938945677540327) ?_ (fun q hq hd => ?_)
  · rw [show 123523834588549530800560938945677540327 - 1 = 123523834588549530800560938945677540326 from by norm_num]
    reduce_mod_char
  · have e : 123523834588549530800560938945677540327 - 1 = [2 ^ 1, 11 ^ 1, 12391 ^ 1, 1793153 ^ 1, 252699498601747720280779871 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123523834588549530800560938945677540327 - 1) / 2 = 61761917294274765400280469472838770163 from by norm_num]
      have h2 : (5 : ZMod 123523834588549530800560938945677540327) ^ 61761917294274765400280469472838770163 = ((123523834588549530800560938945677540326 : ℕ) : ZMod 123523834588549530800560938945677540327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123523834588549530800560938945677540327 - 1) / 11 = 11229439508049957345505539904152503666 from by norm_num]
      have h2 : (5 : ZMod 123523834588549530800560938945677540327) ^ 11229439508049957345505539904152503666 = ((82909786987139581651526428221221182401 : ℕ) : ZMod 123523834588549530800560938945677540327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123523834588549530800560938945677540327 - 1) / 12391 = 9968835008356834057022107896511786 from by norm_num]
      have h2 : (5 : ZMod 123523834588549530800560938945677540327) ^ 9968835008356834057022107896511786 = ((35538121952933553066754344476673590333 : ℕ) : ZMod 123523834588549530800560938945677540327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123523834588549530800560938945677540327 - 1) / 1793153 = 68886388717833632043981154394342 from by norm_num]
      have h2 : (5 : ZMod 123523834588549530800560938945677540327) ^ 68886388717833632043981154394342 = ((89863039447236658850685651227662509561 : ℕ) : ZMod 123523834588549530800560938945677540327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_252699498601747720280779871).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (123523834588549530800560938945677540327 - 1) / 252699498601747720280779871 = 488817094106 from by norm_num]
      have h2 : (5 : ZMod 123523834588549530800560938945677540327) ^ 488817094106 = ((54147735724501662750736565909779383370 : ℕ) : ZMod 123523834588549530800560938945677540327) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_828943693 : Nat.Prime 828943693 := by
  refine lucas_primality 828943693 (6 : ZMod 828943693) ?_ (fun q hq hd => ?_)
  · rw [show 828943693 - 1 = 828943692 from by norm_num]
    reduce_mod_char
  · have e : 828943693 - 1 = [2 ^ 2, 3 ^ 1, 109 ^ 1, 197 ^ 1, 3217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (828943693 - 1) / 2 = 414471846 from by norm_num]
      have h2 : (6 : ZMod 828943693) ^ 414471846 = ((828943692 : ℕ) : ZMod 828943693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (828943693 - 1) / 3 = 276314564 from by norm_num]
      have h2 : (6 : ZMod 828943693) ^ 276314564 = ((292616948 : ℕ) : ZMod 828943693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (828943693 - 1) / 109 = 7604988 from by norm_num]
      have h2 : (6 : ZMod 828943693) ^ 7604988 = ((393257579 : ℕ) : ZMod 828943693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (828943693 - 1) / 197 = 4207836 from by norm_num]
      have h2 : (6 : ZMod 828943693) ^ 4207836 = ((189200915 : ℕ) : ZMod 828943693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (828943693 - 1) / 3217 = 257676 from by norm_num]
      have h2 : (6 : ZMod 828943693) ^ 257676 = ((589629110 : ℕ) : ZMod 828943693) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24343016953382358704409035657305528570198669421823919 : Nat.Prime 24343016953382358704409035657305528570198669421823919 := by
  refine lucas_primality 24343016953382358704409035657305528570198669421823919 (6 : ZMod 24343016953382358704409035657305528570198669421823919) ?_ (fun q hq hd => ?_)
  · rw [show 24343016953382358704409035657305528570198669421823919 - 1 = 24343016953382358704409035657305528570198669421823918 from by norm_num]
    reduce_mod_char
  · have e : 24343016953382358704409035657305528570198669421823919 - 1 = [2 ^ 1, 3 ^ 1, 39623 ^ 1, 828943693 ^ 1, 123523834588549530800560938945677540327 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24343016953382358704409035657305528570198669421823919 - 1) / 2 = 12171508476691179352204517828652764285099334710911959 from by norm_num]
      have h2 : (6 : ZMod 24343016953382358704409035657305528570198669421823919) ^ 12171508476691179352204517828652764285099334710911959 = ((24343016953382358704409035657305528570198669421823918 : ℕ) : ZMod 24343016953382358704409035657305528570198669421823919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24343016953382358704409035657305528570198669421823919 - 1) / 3 = 8114338984460786234803011885768509523399556473941306 from by norm_num]
      have h2 : (6 : ZMod 24343016953382358704409035657305528570198669421823919) ^ 8114338984460786234803011885768509523399556473941306 = ((14336742468585756184624430529614703684139633988098583 : ℕ) : ZMod 24343016953382358704409035657305528570198669421823919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24343016953382358704409035657305528570198669421823919 - 1) / 39623 = 614365821704120301451405387207064799994918845666 from by norm_num]
      have h2 : (6 : ZMod 24343016953382358704409035657305528570198669421823919) ^ 614365821704120301451405387207064799994918845666 = ((2177991835968860381956644452060832770698311481905091 : ℕ) : ZMod 24343016953382358704409035657305528570198669421823919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_828943693).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24343016953382358704409035657305528570198669421823919 - 1) / 828943693 = 29366309387412588353463756503067487082260326 from by norm_num]
      have h2 : (6 : ZMod 24343016953382358704409035657305528570198669421823919) ^ 29366309387412588353463756503067487082260326 = ((11688526289816377986947792947426048518361646968335998 : ℕ) : ZMod 24343016953382358704409035657305528570198669421823919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_123523834588549530800560938945677540327).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24343016953382358704409035657305528570198669421823919 - 1) / 123523834588549530800560938945677540327 = 197071415686434 from by norm_num]
      have h2 : (6 : ZMod 24343016953382358704409035657305528570198669421823919) ^ 197071415686434 = ((22199002924411105941454796354411733795373248067460199 : ℕ) : ZMod 24343016953382358704409035657305528570198669421823919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_977290392691 : Nat.Prime 977290392691 := by
  refine lucas_primality 977290392691 (2 : ZMod 977290392691) ?_ (fun q hq hd => ?_)
  · rw [show 977290392691 - 1 = 977290392690 from by norm_num]
    reduce_mod_char
  · have e : 977290392691 - 1 = [2 ^ 1, 3 ^ 4, 5 ^ 1, 16033 ^ 1, 75253 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (977290392691 - 1) / 2 = 488645196345 from by norm_num]
      have h2 : (2 : ZMod 977290392691) ^ 488645196345 = ((977290392690 : ℕ) : ZMod 977290392691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (977290392691 - 1) / 3 = 325763464230 from by norm_num]
      have h2 : (2 : ZMod 977290392691) ^ 325763464230 = ((675062505510 : ℕ) : ZMod 977290392691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (977290392691 - 1) / 5 = 195458078538 from by norm_num]
      have h2 : (2 : ZMod 977290392691) ^ 195458078538 = ((727530820075 : ℕ) : ZMod 977290392691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (977290392691 - 1) / 16033 = 60954930 from by norm_num]
      have h2 : (2 : ZMod 977290392691) ^ 60954930 = ((338628711723 : ℕ) : ZMod 977290392691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (977290392691 - 1) / 75253 = 12986730 from by norm_num]
      have h2 : (2 : ZMod 977290392691) ^ 12986730 = ((156325660822 : ℕ) : ZMod 977290392691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_317668238273 : Nat.Prime 317668238273 := by
  refine lucas_primality 317668238273 (19 : ZMod 317668238273) ?_ (fun q hq hd => ?_)
  · rw [show 317668238273 - 1 = 317668238272 from by norm_num]
    reduce_mod_char
  · have e : 317668238273 - 1 = [2 ^ 6, 7 ^ 1, 11 ^ 1, 89 ^ 1, 724291 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317668238273 - 1) / 2 = 158834119136 from by norm_num]
      have h2 : (19 : ZMod 317668238273) ^ 158834119136 = ((317668238272 : ℕ) : ZMod 317668238273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317668238273 - 1) / 7 = 45381176896 from by norm_num]
      have h2 : (19 : ZMod 317668238273) ^ 45381176896 = ((89919601623 : ℕ) : ZMod 317668238273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317668238273 - 1) / 11 = 28878930752 from by norm_num]
      have h2 : (19 : ZMod 317668238273) ^ 28878930752 = ((13195720562 : ℕ) : ZMod 317668238273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317668238273 - 1) / 89 = 3569306048 from by norm_num]
      have h2 : (19 : ZMod 317668238273) ^ 3569306048 = ((282299369052 : ℕ) : ZMod 317668238273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (317668238273 - 1) / 724291 = 438592 from by norm_num]
      have h2 : (19 : ZMod 317668238273) ^ 438592 = ((269908169224 : ℕ) : ZMod 317668238273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_132854592497883722299833006893761 : Nat.Prime 132854592497883722299833006893761 := by
  refine lucas_primality 132854592497883722299833006893761 (11 : ZMod 132854592497883722299833006893761) ?_ (fun q hq hd => ?_)
  · rw [show 132854592497883722299833006893761 - 1 = 132854592497883722299833006893760 from by norm_num]
    reduce_mod_char
  · have e : 132854592497883722299833006893761 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 7 ^ 1, 21227 ^ 1, 317668238273 ^ 1, 977290392691 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 2 = 66427296248941861149916503446880 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 66427296248941861149916503446880 = ((132854592497883722299833006893760 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 3 = 44284864165961240766611002297920 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 44284864165961240766611002297920 = ((20285526660570147699080431444607 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 5 = 26570918499576744459966601378752 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 26570918499576744459966601378752 = ((42079933587622343155846065287028 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 7 = 18979227499697674614261858127680 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 18979227499697674614261858127680 = ((106403231883821475323409998728121 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 21227 = 6258755005317931045358882880 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 6258755005317931045358882880 = ((95644940734297067959488974132589 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_317668238273).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 317668238273 = 418218054219541437120 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 418218054219541437120 = ((108627642896623158211313888973539 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_977290392691).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (132854592497883722299833006893761 - 1) / 977290392691 = 135941776867430775360 from by norm_num]
      have h2 : (11 : ZMod 132854592497883722299833006893761) ^ 135941776867430775360 = ((108877515809890984019632789200901 : ℕ) : ZMod 132854592497883722299833006893761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_472401162592505264461751488855196441634426625661 : Nat.Prime 472401162592505264461751488855196441634426625661 := by
  refine lucas_primality 472401162592505264461751488855196441634426625661 (10 : ZMod 472401162592505264461751488855196441634426625661) ?_ (fun q hq hd => ?_)
  · rw [show 472401162592505264461751488855196441634426625661 - 1 = 472401162592505264461751488855196441634426625660 from by norm_num]
    reduce_mod_char
  · have e : 472401162592505264461751488855196441634426625661 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 1, 317 ^ 1, 1021 ^ 1, 7133927 ^ 1, 132854592497883722299833006893761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 2 = 236200581296252632230875744427598220817213312830 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 236200581296252632230875744427598220817213312830 = ((472401162592505264461751488855196441634426625660 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 5 = 94480232518501052892350297771039288326885325132 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 94480232518501052892350297771039288326885325132 = ((440087714145137246465667035754303359576772647742 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 7 = 67485880370357894923107355550742348804918089380 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 67485880370357894923107355550742348804918089380 = ((307023056731907911479603392574126346736946755545 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 11 = 42945560235682296769250135350472403784947875060 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 42945560235682296769250135350472403784947875060 = ((96106064264684061479356358677613479088425928616 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 317 = 1490224487673518184421928986924909910518695980 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 1490224487673518184421928986924909910518695980 = ((363461992665443061811234710324190655827732847039 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 1021 = 462684782166998300158424572825853517761436460 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 462684782166998300158424572825853517761436460 = ((140478002362088771014525384515572613216132404619 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 7133927 = 66218951019894829938931459328809566124580 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 66218951019894829938931459328809566124580 = ((326380296327191361885604741036129479981693976415 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_132854592497883722299833006893761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (472401162592505264461751488855196441634426625661 - 1) / 132854592497883722299833006893761 = 3555775933000060 from by norm_num]
      have h2 : (10 : ZMod 472401162592505264461751488855196441634426625661) ^ 3555775933000060 = ((344794492017551387095424231992105211061871166030 : ℕ) : ZMod 472401162592505264461751488855196441634426625661) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10383775510679 : Nat.Prime 10383775510679 := by
  refine lucas_primality 10383775510679 (7 : ZMod 10383775510679) ?_ (fun q hq hd => ?_)
  · rw [show 10383775510679 - 1 = 10383775510678 from by norm_num]
    reduce_mod_char
  · have e : 10383775510679 - 1 = [2 ^ 1, 19 ^ 1, 1657 ^ 1, 4133 ^ 1, 39901 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10383775510679 - 1) / 2 = 5191887755339 from by norm_num]
      have h2 : (7 : ZMod 10383775510679) ^ 5191887755339 = ((10383775510678 : ℕ) : ZMod 10383775510679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10383775510679 - 1) / 19 = 546514500562 from by norm_num]
      have h2 : (7 : ZMod 10383775510679) ^ 546514500562 = ((9608351891225 : ℕ) : ZMod 10383775510679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10383775510679 - 1) / 1657 = 6266611654 from by norm_num]
      have h2 : (7 : ZMod 10383775510679) ^ 6266611654 = ((3677864663580 : ℕ) : ZMod 10383775510679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10383775510679 - 1) / 4133 = 2512406366 from by norm_num]
      have h2 : (7 : ZMod 10383775510679) ^ 2512406366 = ((8898486107924 : ℕ) : ZMod 10383775510679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10383775510679 - 1) / 39901 = 260238478 from by norm_num]
      have h2 : (7 : ZMod 10383775510679) ^ 260238478 = ((5711537431519 : ℕ) : ZMod 10383775510679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_129773067231637597 : Nat.Prime 129773067231637597 := by
  refine lucas_primality 129773067231637597 (7 : ZMod 129773067231637597) ?_ (fun q hq hd => ?_)
  · rw [show 129773067231637597 - 1 = 129773067231637596 from by norm_num]
    reduce_mod_char
  · have e : 129773067231637597 - 1 = [2 ^ 2, 3 ^ 1, 13 ^ 1, 19 ^ 1, 31 ^ 1, 557 ^ 1, 4259 ^ 1, 595363 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 2 = 64886533615818798 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 64886533615818798 = ((129773067231637596 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 3 = 43257689077212532 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 43257689077212532 = ((120889914990996333 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 13 = 9982543633202892 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 9982543633202892 = ((70203238261625746 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 19 = 6830161433244084 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 6830161433244084 = ((75208361396964138 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 31 = 4186227975214116 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 4186227975214116 = ((102790927608463486 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 557 = 232985758046028 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 232985758046028 = ((114153108307116689 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 4259 = 30470313977844 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 30470313977844 = ((58738494508147058 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (129773067231637597 - 1) / 595363 = 217973013492 from by norm_num]
      have h2 : (7 : ZMod 129773067231637597) ^ 217973013492 = ((56800870296273497 : ℕ) : ZMod 129773067231637597) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_182720478662145736577 : Nat.Prime 182720478662145736577 := by
  refine lucas_primality 182720478662145736577 (3 : ZMod 182720478662145736577) ?_ (fun q hq hd => ?_)
  · rw [show 182720478662145736577 - 1 = 182720478662145736576 from by norm_num]
    reduce_mod_char
  · have e : 182720478662145736577 - 1 = [2 ^ 7, 11 ^ 1, 129773067231637597 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182720478662145736577 - 1) / 2 = 91360239331072868288 from by norm_num]
      have h2 : (3 : ZMod 182720478662145736577) ^ 91360239331072868288 = ((182720478662145736576 : ℕ) : ZMod 182720478662145736577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182720478662145736577 - 1) / 11 = 16610952605649612416 from by norm_num]
      have h2 : (3 : ZMod 182720478662145736577) ^ 16610952605649612416 = ((35678889416109699704 : ℕ) : ZMod 182720478662145736577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_129773067231637597).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (182720478662145736577 - 1) / 129773067231637597 = 1408 from by norm_num]
      have h2 : (3 : ZMod 182720478662145736577) ^ 1408 = ((112561063902864985787 : ℕ) : ZMod 182720478662145736577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_254977717481 : Nat.Prime 254977717481 := by
  refine lucas_primality 254977717481 (3 : ZMod 254977717481) ?_ (fun q hq hd => ?_)
  · rw [show 254977717481 - 1 = 254977717480 from by norm_num]
    reduce_mod_char
  · have e : 254977717481 - 1 = [2 ^ 3, 5 ^ 1, 43 ^ 1, 251 ^ 1, 590609 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (254977717481 - 1) / 2 = 127488858740 from by norm_num]
      have h2 : (3 : ZMod 254977717481) ^ 127488858740 = ((254977717480 : ℕ) : ZMod 254977717481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (254977717481 - 1) / 5 = 50995543496 from by norm_num]
      have h2 : (3 : ZMod 254977717481) ^ 50995543496 = ((36879824663 : ℕ) : ZMod 254977717481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (254977717481 - 1) / 43 = 5929714360 from by norm_num]
      have h2 : (3 : ZMod 254977717481) ^ 5929714360 = ((180585719834 : ℕ) : ZMod 254977717481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (254977717481 - 1) / 251 = 1015847480 from by norm_num]
      have h2 : (3 : ZMod 254977717481) ^ 1015847480 = ((230911312641 : ℕ) : ZMod 254977717481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (254977717481 - 1) / 590609 = 431720 from by norm_num]
      have h2 : (3 : ZMod 254977717481) ^ 431720 = ((128448708177 : ℕ) : ZMod 254977717481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3297828698676263965255996064314097775904874359 : Nat.Prime 3297828698676263965255996064314097775904874359 := by
  refine lucas_primality 3297828698676263965255996064314097775904874359 (6 : ZMod 3297828698676263965255996064314097775904874359) ?_ (fun q hq hd => ?_)
  · rw [show 3297828698676263965255996064314097775904874359 - 1 = 3297828698676263965255996064314097775904874358 from by norm_num]
    reduce_mod_char
  · have e : 3297828698676263965255996064314097775904874359 - 1 = [2 ^ 1, 3 ^ 1, 47 ^ 1, 139 ^ 1, 643 ^ 1, 983 ^ 1, 2857 ^ 1, 254977717481 ^ 1, 182720478662145736577 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 2 = 1648914349338131982627998032157048887952437179 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 1648914349338131982627998032157048887952437179 = ((3297828698676263965255996064314097775904874358 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 3 = 1099276232892087988418665354771365925301624786 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 1099276232892087988418665354771365925301624786 = ((1447735237941434836203807749778710746130307914 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 47 = 70166568056941786494808426900299952678827114 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 70166568056941786494808426900299952678827114 = ((290177998652510204264773475001348959993037518 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 139 = 23725386321411970973064719887151782560466722 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 23725386321411970973064719887151782560466722 = ((1554065769171676996320218286099980388427765324 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 643 = 5128816016603831983290818140457383788343506 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 5128816016603831983290818140457383788343506 = ((2064433058186377879221203854623839756055163396 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 983 = 3354861341481448591308236077633873627573626 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 3354861341481448591308236077633873627573626 = ((3031429247421443412720145651742900148958144845 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 2857 = 1154297759424663621020649654992683855759494 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 1154297759424663621020649654992683855759494 = ((1129166051723905439726044238890611141168634150 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_254977717481).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 254977717481 = 12933791749555550902198155928883718 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 12933791749555550902198155928883718 = ((2548838081419731808003084361466874611046666929 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_182720478662145736577).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3297828698676263965255996064314097775904874359 - 1) / 182720478662145736577 = 18048489818013355791489654 from by norm_num]
      have h2 : (6 : ZMod 3297828698676263965255996064314097775904874359) ^ 18048489818013355791489654 = ((563605548388830908172438739135022121380984297 : ℕ) : ZMod 3297828698676263965255996064314097775904874359) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_91072483 : Nat.Prime 91072483 := by
  refine lucas_primality 91072483 (2 : ZMod 91072483) ?_ (fun q hq hd => ?_)
  · rw [show 91072483 - 1 = 91072482 from by norm_num]
    reduce_mod_char
  · have e : 91072483 - 1 = [2 ^ 1, 3 ^ 1, 31 ^ 1, 659 ^ 1, 743 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91072483 - 1) / 2 = 45536241 from by norm_num]
      have h2 : (2 : ZMod 91072483) ^ 45536241 = ((91072482 : ℕ) : ZMod 91072483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91072483 - 1) / 3 = 30357494 from by norm_num]
      have h2 : (2 : ZMod 91072483) ^ 30357494 = ((22590751 : ℕ) : ZMod 91072483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91072483 - 1) / 31 = 2937822 from by norm_num]
      have h2 : (2 : ZMod 91072483) ^ 2937822 = ((70183403 : ℕ) : ZMod 91072483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91072483 - 1) / 659 = 138198 from by norm_num]
      have h2 : (2 : ZMod 91072483) ^ 138198 = ((82537710 : ℕ) : ZMod 91072483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (91072483 - 1) / 743 = 122574 from by norm_num]
      have h2 : (2 : ZMod 91072483) ^ 122574 = ((22397329 : ℕ) : ZMod 91072483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1051615000043032744519 : Nat.Prime 1051615000043032744519 := by
  refine lucas_primality 1051615000043032744519 (7 : ZMod 1051615000043032744519) ?_ (fun q hq hd => ?_)
  · rw [show 1051615000043032744519 - 1 = 1051615000043032744518 from by norm_num]
    reduce_mod_char
  · have e : 1051615000043032744519 - 1 = [2 ^ 1, 3 ^ 1, 73 ^ 1, 661 ^ 1, 37811 ^ 1, 70181 ^ 1, 1368811 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 2 = 525807500021516372259 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 525807500021516372259 = ((1051615000043032744518 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 3 = 350538333347677581506 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 350538333347677581506 = ((441228662953630692770 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 73 = 14405684932096338966 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 14405684932096338966 = ((359669805493523882662 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 661 = 1590945537130155438 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 1590945537130155438 = ((841709716417575905676 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 37811 = 27812409088440738 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 27812409088440738 = ((268177475086360622483 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 70181 = 14984326242758478 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 14984326242758478 = ((174308893660586731545 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1051615000043032744519 - 1) / 1368811 = 768268957542738 from by norm_num]
      have h2 : (7 : ZMod 1051615000043032744519) ^ 768268957542738 = ((854831783720213807806 : ℕ) : ZMod 1051615000043032744519) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_192173221 : Nat.Prime 192173221 := by
  refine lucas_primality 192173221 (2 : ZMod 192173221) ?_ (fun q hq hd => ?_)
  · rw [show 192173221 - 1 = 192173220 from by norm_num]
    reduce_mod_char
  · have e : 192173221 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 19 ^ 1, 83 ^ 1, 677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 2 = 96086610 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 96086610 = ((192173220 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 3 = 64057740 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 64057740 = ((173621004 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 5 = 38434644 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 38434644 = ((65471012 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 19 = 10114380 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 10114380 = ((26167034 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 83 = 2315340 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 2315340 = ((59443020 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (192173221 - 1) / 677 = 283860 from by norm_num]
      have h2 : (2 : ZMod 192173221) ^ 283860 = ((173001896 : ℕ) : ZMod 192173221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_96086611 : Nat.Prime 96086611 := by
  refine lucas_primality 96086611 (11 : ZMod 96086611) ?_ (fun q hq hd => ?_)
  · rw [show 96086611 - 1 = 96086610 from by norm_num]
    reduce_mod_char
  · have e : 96086611 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 19 ^ 1, 83 ^ 1, 677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 2 = 48043305 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 48043305 = ((96086610 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 3 = 32028870 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 32028870 = ((69691002 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 5 = 19217322 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 19217322 = ((793257 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 19 = 5057190 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 5057190 = ((74993958 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 83 = 1157670 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 1157670 = ((50891410 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (96086611 - 1) / 677 = 141930 from by norm_num]
      have h2 : (11 : ZMod 96086611) ^ 141930 = ((62882995 : ℕ) : ZMod 96086611) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9114428881 : Nat.Prime 9114428881 := by
  refine lucas_primality 9114428881 (7 : ZMod 9114428881) ?_ (fun q hq hd => ?_)
  · rw [show 9114428881 - 1 = 9114428880 from by norm_num]
    reduce_mod_char
  · have e : 9114428881 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 173 ^ 1, 24391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9114428881 - 1) / 2 = 4557214440 from by norm_num]
      have h2 : (7 : ZMod 9114428881) ^ 4557214440 = ((9114428880 : ℕ) : ZMod 9114428881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9114428881 - 1) / 3 = 3038142960 from by norm_num]
      have h2 : (7 : ZMod 9114428881) ^ 3038142960 = ((7427206265 : ℕ) : ZMod 9114428881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9114428881 - 1) / 5 = 1822885776 from by norm_num]
      have h2 : (7 : ZMod 9114428881) ^ 1822885776 = ((1495537955 : ℕ) : ZMod 9114428881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9114428881 - 1) / 173 = 52684560 from by norm_num]
      have h2 : (7 : ZMod 9114428881) ^ 52684560 = ((371444345 : ℕ) : ZMod 9114428881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9114428881 - 1) / 24391 = 373680 from by norm_num]
      have h2 : (7 : ZMod 9114428881) ^ 373680 = ((7503663652 : ℕ) : ZMod 9114428881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_606813158110633 : Nat.Prime 606813158110633 := by
  refine lucas_primality 606813158110633 (5 : ZMod 606813158110633) ?_ (fun q hq hd => ?_)
  · rw [show 606813158110633 - 1 = 606813158110632 from by norm_num]
    reduce_mod_char
  · have e : 606813158110633 - 1 = [2 ^ 3, 3 ^ 1, 11 ^ 1, 277 ^ 1, 347 ^ 1, 23913427 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 2 = 303406579055316 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 303406579055316 = ((606813158110632 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 3 = 202271052703544 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 202271052703544 = ((600627710099900 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 11 = 55164832555512 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 55164832555512 = ((490690022261911 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 277 = 2190661220616 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 2190661220616 = ((282921418147377 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 347 = 1748741089656 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 1748741089656 = ((576269795570338 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (606813158110633 - 1) / 23913427 = 25375416 from by norm_num]
      have h2 : (5 : ZMod 606813158110633) ^ 25375416 = ((381032044214345 : ℕ) : ZMod 606813158110633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1072108053199 : Nat.Prime 1072108053199 := by
  refine lucas_primality 1072108053199 (6 : ZMod 1072108053199) ?_ (fun q hq hd => ?_)
  · rw [show 1072108053199 - 1 = 1072108053198 from by norm_num]
    reduce_mod_char
  · have e : 1072108053199 - 1 = [2 ^ 1, 3 ^ 3, 7 ^ 1, 13 ^ 1, 19 ^ 1, 11482853 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 2 = 536054026599 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 536054026599 = ((1072108053198 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 3 = 357369351066 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 357369351066 = ((127611193571 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 7 = 153158293314 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 153158293314 = ((1061121739724 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 13 = 82469850246 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 82469850246 = ((362332020977 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 19 = 56426739642 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 56426739642 = ((976624170929 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1072108053199 - 1) / 11482853 = 93366 from by norm_num]
      have h2 : (6 : ZMod 1072108053199) ^ 93366 = ((937033270462 : ℕ) : ZMod 1072108053199) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_790198478614393 : Nat.Prime 790198478614393 := by
  refine lucas_primality 790198478614393 (31 : ZMod 790198478614393) ?_ (fun q hq hd => ?_)
  · rw [show 790198478614393 - 1 = 790198478614392 from by norm_num]
    reduce_mod_char
  · have e : 790198478614393 - 1 = [2 ^ 3, 3 ^ 1, 701 ^ 1, 20717 ^ 1, 2267149 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (790198478614393 - 1) / 2 = 395099239307196 from by norm_num]
      have h2 : (31 : ZMod 790198478614393) ^ 395099239307196 = ((790198478614392 : ℕ) : ZMod 790198478614393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (790198478614393 - 1) / 3 = 263399492871464 from by norm_num]
      have h2 : (31 : ZMod 790198478614393) ^ 263399492871464 = ((193255393157089 : ℕ) : ZMod 790198478614393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (790198478614393 - 1) / 701 = 1127244619992 from by norm_num]
      have h2 : (31 : ZMod 790198478614393) ^ 1127244619992 = ((318297248274081 : ℕ) : ZMod 790198478614393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (790198478614393 - 1) / 20717 = 38142514776 from by norm_num]
      have h2 : (31 : ZMod 790198478614393) ^ 38142514776 = ((662517215065414 : ℕ) : ZMod 790198478614393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (790198478614393 - 1) / 2267149 = 348542808 from by norm_num]
      have h2 : (31 : ZMod 790198478614393) ^ 348542808 = ((127513015033085 : ℕ) : ZMod 790198478614393) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_92897029 : Nat.Prime 92897029 := by
  refine lucas_primality 92897029 (2 : ZMod 92897029) ?_ (fun q hq hd => ?_)
  · rw [show 92897029 - 1 = 92897028 from by norm_num]
    reduce_mod_char
  · have e : 92897029 - 1 = [2 ^ 2, 3 ^ 2, 7 ^ 1, 43 ^ 1, 8573 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92897029 - 1) / 2 = 46448514 from by norm_num]
      have h2 : (2 : ZMod 92897029) ^ 46448514 = ((92897028 : ℕ) : ZMod 92897029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92897029 - 1) / 3 = 30965676 from by norm_num]
      have h2 : (2 : ZMod 92897029) ^ 30965676 = ((23627521 : ℕ) : ZMod 92897029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92897029 - 1) / 7 = 13271004 from by norm_num]
      have h2 : (2 : ZMod 92897029) ^ 13271004 = ((73527540 : ℕ) : ZMod 92897029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92897029 - 1) / 43 = 2160396 from by norm_num]
      have h2 : (2 : ZMod 92897029) ^ 2160396 = ((80624791 : ℕ) : ZMod 92897029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (92897029 - 1) / 8573 = 10836 from by norm_num]
      have h2 : (2 : ZMod 92897029) ^ 10836 = ((43243531 : ℕ) : ZMod 92897029) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15606700873 : Nat.Prime 15606700873 := by
  refine lucas_primality 15606700873 (15 : ZMod 15606700873) ?_ (fun q hq hd => ?_)
  · rw [show 15606700873 - 1 = 15606700872 from by norm_num]
    reduce_mod_char
  · have e : 15606700873 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 92897029 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15606700873 - 1) / 2 = 7803350436 from by norm_num]
      have h2 : (15 : ZMod 15606700873) ^ 7803350436 = ((15606700872 : ℕ) : ZMod 15606700873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15606700873 - 1) / 3 = 5202233624 from by norm_num]
      have h2 : (15 : ZMod 15606700873) ^ 5202233624 = ((7239478549 : ℕ) : ZMod 15606700873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15606700873 - 1) / 7 = 2229528696 from by norm_num]
      have h2 : (15 : ZMod 15606700873) ^ 2229528696 = ((4801358759 : ℕ) : ZMod 15606700873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_92897029).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15606700873 - 1) / 92897029 = 168 from by norm_num]
      have h2 : (15 : ZMod 15606700873) ^ 168 = ((15744961 : ℕ) : ZMod 15606700873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62426803493 : Nat.Prime 62426803493 := by
  refine lucas_primality 62426803493 (2 : ZMod 62426803493) ?_ (fun q hq hd => ?_)
  · rw [show 62426803493 - 1 = 62426803492 from by norm_num]
    reduce_mod_char
  · have e : 62426803493 - 1 = [2 ^ 2, 15606700873 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62426803493 - 1) / 2 = 31213401746 from by norm_num]
      have h2 : (2 : ZMod 62426803493) ^ 31213401746 = ((62426803492 : ℕ) : ZMod 62426803493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15606700873).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62426803493 - 1) / 15606700873 = 4 from by norm_num]
      have h2 : (2 : ZMod 62426803493) ^ 4 = ((16 : ℕ) : ZMod 62426803493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_211902173811073 : Nat.Prime 211902173811073 := by
  refine lucas_primality 211902173811073 (13 : ZMod 211902173811073) ?_ (fun q hq hd => ?_)
  · rw [show 211902173811073 - 1 = 211902173811072 from by norm_num]
    reduce_mod_char
  · have e : 211902173811073 - 1 = [2 ^ 7, 3 ^ 2, 89 ^ 1, 353 ^ 1, 5854883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211902173811073 - 1) / 2 = 105951086905536 from by norm_num]
      have h2 : (13 : ZMod 211902173811073) ^ 105951086905536 = ((211902173811072 : ℕ) : ZMod 211902173811073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211902173811073 - 1) / 3 = 70634057937024 from by norm_num]
      have h2 : (13 : ZMod 211902173811073) ^ 70634057937024 = ((199407900952516 : ℕ) : ZMod 211902173811073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211902173811073 - 1) / 89 = 2380923301248 from by norm_num]
      have h2 : (13 : ZMod 211902173811073) ^ 2380923301248 = ((97643173498633 : ℕ) : ZMod 211902173811073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211902173811073 - 1) / 353 = 600289444224 from by norm_num]
      have h2 : (13 : ZMod 211902173811073) ^ 600289444224 = ((7581694470363 : ℕ) : ZMod 211902173811073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (211902173811073 - 1) / 5854883 = 36192384 from by norm_num]
      have h2 : (13 : ZMod 211902173811073) ^ 36192384 = ((132302251666551 : ℕ) : ZMod 211902173811073) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_159280471573 : Nat.Prime 159280471573 := by
  refine lucas_primality 159280471573 (2 : ZMod 159280471573) ?_ (fun q hq hd => ?_)
  · rw [show 159280471573 - 1 = 159280471572 from by norm_num]
    reduce_mod_char
  · have e : 159280471573 - 1 = [2 ^ 2, 3 ^ 1, 101 ^ 1, 709 ^ 1, 185359 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159280471573 - 1) / 2 = 79640235786 from by norm_num]
      have h2 : (2 : ZMod 159280471573) ^ 79640235786 = ((159280471572 : ℕ) : ZMod 159280471573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159280471573 - 1) / 3 = 53093490524 from by norm_num]
      have h2 : (2 : ZMod 159280471573) ^ 53093490524 = ((54161701106 : ℕ) : ZMod 159280471573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159280471573 - 1) / 101 = 1577034372 from by norm_num]
      have h2 : (2 : ZMod 159280471573) ^ 1577034372 = ((38555321034 : ℕ) : ZMod 159280471573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159280471573 - 1) / 709 = 224655108 from by norm_num]
      have h2 : (2 : ZMod 159280471573) ^ 224655108 = ((67484605192 : ℕ) : ZMod 159280471573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159280471573 - 1) / 185359 = 859308 from by norm_num]
      have h2 : (2 : ZMod 159280471573) ^ 859308 = ((37368483705 : ℕ) : ZMod 159280471573) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_50196146839 : Nat.Prime 50196146839 := by
  refine lucas_primality 50196146839 (11 : ZMod 50196146839) ?_ (fun q hq hd => ?_)
  · rw [show 50196146839 - 1 = 50196146838 from by norm_num]
    reduce_mod_char
  · have e : 50196146839 - 1 = [2 ^ 1, 3 ^ 1, 727 ^ 1, 1103 ^ 1, 10433 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50196146839 - 1) / 2 = 25098073419 from by norm_num]
      have h2 : (11 : ZMod 50196146839) ^ 25098073419 = ((50196146838 : ℕ) : ZMod 50196146839) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50196146839 - 1) / 3 = 16732048946 from by norm_num]
      have h2 : (11 : ZMod 50196146839) ^ 16732048946 = ((1485637203 : ℕ) : ZMod 50196146839) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50196146839 - 1) / 727 = 69045594 from by norm_num]
      have h2 : (11 : ZMod 50196146839) ^ 69045594 = ((11218841772 : ℕ) : ZMod 50196146839) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50196146839 - 1) / 1103 = 45508746 from by norm_num]
      have h2 : (11 : ZMod 50196146839) ^ 45508746 = ((9048772317 : ℕ) : ZMod 50196146839) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (50196146839 - 1) / 10433 = 4811286 from by norm_num]
      have h2 : (11 : ZMod 50196146839) ^ 4811286 = ((25710194615 : ℕ) : ZMod 50196146839) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1258271653 : Nat.Prime 1258271653 := by
  refine lucas_primality 1258271653 (2 : ZMod 1258271653) ?_ (fun q hq hd => ?_)
  · rw [show 1258271653 - 1 = 1258271652 from by norm_num]
    reduce_mod_char
  · have e : 1258271653 - 1 = [2 ^ 2, 3 ^ 1, 11 ^ 1, 739 ^ 1, 12899 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1258271653 - 1) / 2 = 629135826 from by norm_num]
      have h2 : (2 : ZMod 1258271653) ^ 629135826 = ((1258271652 : ℕ) : ZMod 1258271653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1258271653 - 1) / 3 = 419423884 from by norm_num]
      have h2 : (2 : ZMod 1258271653) ^ 419423884 = ((249342342 : ℕ) : ZMod 1258271653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1258271653 - 1) / 11 = 114388332 from by norm_num]
      have h2 : (2 : ZMod 1258271653) ^ 114388332 = ((1084232270 : ℕ) : ZMod 1258271653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1258271653 - 1) / 739 = 1702668 from by norm_num]
      have h2 : (2 : ZMod 1258271653) ^ 1702668 = ((1252147773 : ℕ) : ZMod 1258271653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1258271653 - 1) / 12899 = 97548 from by norm_num]
      have h2 : (2 : ZMod 1258271653) ^ 97548 = ((1099222746 : ℕ) : ZMod 1258271653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1073531989 : Nat.Prime 1073531989 := by
  refine lucas_primality 1073531989 (2 : ZMod 1073531989) ?_ (fun q hq hd => ?_)
  · rw [show 1073531989 - 1 = 1073531988 from by norm_num]
    reduce_mod_char
  · have e : 1073531989 - 1 = [2 ^ 2, 3 ^ 3, 9940111 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073531989 - 1) / 2 = 536765994 from by norm_num]
      have h2 : (2 : ZMod 1073531989) ^ 536765994 = ((1073531988 : ℕ) : ZMod 1073531989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073531989 - 1) / 3 = 357843996 from by norm_num]
      have h2 : (2 : ZMod 1073531989) ^ 357843996 = ((560729289 : ℕ) : ZMod 1073531989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1073531989 - 1) / 9940111 = 108 from by norm_num]
      have h2 : (2 : ZMod 1073531989) ^ 108 = ((462924553 : ℕ) : ZMod 1073531989) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23929028034811 : Nat.Prime 23929028034811 := by
  refine lucas_primality 23929028034811 (10 : ZMod 23929028034811) ?_ (fun q hq hd => ?_)
  · rw [show 23929028034811 - 1 = 23929028034810 from by norm_num]
    reduce_mod_char
  · have e : 23929028034811 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 743 ^ 1, 1073531989 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23929028034811 - 1) / 2 = 11964514017405 from by norm_num]
      have h2 : (10 : ZMod 23929028034811) ^ 11964514017405 = ((23929028034810 : ℕ) : ZMod 23929028034811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23929028034811 - 1) / 3 = 7976342678270 from by norm_num]
      have h2 : (10 : ZMod 23929028034811) ^ 7976342678270 = ((21532418549768 : ℕ) : ZMod 23929028034811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23929028034811 - 1) / 5 = 4785805606962 from by norm_num]
      have h2 : (10 : ZMod 23929028034811) ^ 4785805606962 = ((10295572863925 : ℕ) : ZMod 23929028034811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23929028034811 - 1) / 743 = 32205959670 from by norm_num]
      have h2 : (10 : ZMod 23929028034811) ^ 32205959670 = ((13807465457850 : ℕ) : ZMod 23929028034811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1073531989).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23929028034811 - 1) / 1073531989 = 22290 from by norm_num]
      have h2 : (10 : ZMod 23929028034811) ^ 22290 = ((23206562044379 : ℕ) : ZMod 23929028034811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47389469 : Nat.Prime 47389469 := by
  refine lucas_primality 47389469 (2 : ZMod 47389469) ?_ (fun q hq hd => ?_)
  · rw [show 47389469 - 1 = 47389468 from by norm_num]
    reduce_mod_char
  · have e : 47389469 - 1 = [2 ^ 2, 7 ^ 2, 241783 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47389469 - 1) / 2 = 23694734 from by norm_num]
      have h2 : (2 : ZMod 47389469) ^ 23694734 = ((47389468 : ℕ) : ZMod 47389469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47389469 - 1) / 7 = 6769924 from by norm_num]
      have h2 : (2 : ZMod 47389469) ^ 6769924 = ((17350895 : ℕ) : ZMod 47389469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47389469 - 1) / 241783 = 196 from by norm_num]
      have h2 : (2 : ZMod 47389469) ^ 196 = ((27715180 : ℕ) : ZMod 47389469) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_314855632037 : Nat.Prime 314855632037 := by
  refine lucas_primality 314855632037 (2 : ZMod 314855632037) ?_ (fun q hq hd => ?_)
  · rw [show 314855632037 - 1 = 314855632036 from by norm_num]
    reduce_mod_char
  · have e : 314855632037 - 1 = [2 ^ 2, 11 ^ 1, 151 ^ 1, 47389469 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (314855632037 - 1) / 2 = 157427816018 from by norm_num]
      have h2 : (2 : ZMod 314855632037) ^ 157427816018 = ((314855632036 : ℕ) : ZMod 314855632037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (314855632037 - 1) / 11 = 28623239276 from by norm_num]
      have h2 : (2 : ZMod 314855632037) ^ 28623239276 = ((102183081445 : ℕ) : ZMod 314855632037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (314855632037 - 1) / 151 = 2085136636 from by norm_num]
      have h2 : (2 : ZMod 314855632037) ^ 2085136636 = ((114332693420 : ℕ) : ZMod 314855632037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47389469).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (314855632037 - 1) / 47389469 = 6644 from by norm_num]
      have h2 : (2 : ZMod 314855632037) ^ 6644 = ((158541294239 : ℕ) : ZMod 314855632037) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1219676228250269 : Nat.Prime 1219676228250269 := by
  refine lucas_primality 1219676228250269 (2 : ZMod 1219676228250269) ?_ (fun q hq hd => ?_)
  · rw [show 1219676228250269 - 1 = 1219676228250268 from by norm_num]
    reduce_mod_char
  · have e : 1219676228250269 - 1 = [2 ^ 2, 373 ^ 1, 150649 ^ 1, 5426371 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1219676228250269 - 1) / 2 = 609838114125134 from by norm_num]
      have h2 : (2 : ZMod 1219676228250269) ^ 609838114125134 = ((1219676228250268 : ℕ) : ZMod 1219676228250269) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1219676228250269 - 1) / 373 = 3269909459116 from by norm_num]
      have h2 : (2 : ZMod 1219676228250269) ^ 3269909459116 = ((486056055016538 : ℕ) : ZMod 1219676228250269) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1219676228250269 - 1) / 150649 = 8096145532 from by norm_num]
      have h2 : (2 : ZMod 1219676228250269) ^ 8096145532 = ((645410537670051 : ℕ) : ZMod 1219676228250269) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1219676228250269 - 1) / 5426371 = 224768308 from by norm_num]
      have h2 : (2 : ZMod 1219676228250269) ^ 224768308 = ((229569598747768 : ℕ) : ZMod 1219676228250269) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_630262089757493 : Nat.Prime 630262089757493 := by
  refine lucas_primality 630262089757493 (2 : ZMod 630262089757493) ?_ (fun q hq hd => ?_)
  · rw [show 630262089757493 - 1 = 630262089757492 from by norm_num]
    reduce_mod_char
  · have e : 630262089757493 - 1 = [2 ^ 2, 2099 ^ 1, 3119 ^ 1, 24067633 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (630262089757493 - 1) / 2 = 315131044878746 from by norm_num]
      have h2 : (2 : ZMod 630262089757493) ^ 315131044878746 = ((630262089757492 : ℕ) : ZMod 630262089757493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (630262089757493 - 1) / 2099 = 300267789308 from by norm_num]
      have h2 : (2 : ZMod 630262089757493) ^ 300267789308 = ((131671982213206 : ℕ) : ZMod 630262089757493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (630262089757493 - 1) / 3119 = 202071846668 from by norm_num]
      have h2 : (2 : ZMod 630262089757493) ^ 202071846668 = ((489122843812104 : ℕ) : ZMod 630262089757493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (630262089757493 - 1) / 24067633 = 26187124 from by norm_num]
      have h2 : (2 : ZMod 630262089757493) ^ 26187124 = ((595090712700962 : ℕ) : ZMod 630262089757493) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22394472573263241277 : Nat.Prime 22394472573263241277 := by
  refine lucas_primality 22394472573263241277 (6 : ZMod 22394472573263241277) ?_ (fun q hq hd => ?_)
  · rw [show 22394472573263241277 - 1 = 22394472573263241276 from by norm_num]
    reduce_mod_char
  · have e : 22394472573263241277 - 1 = [2 ^ 2, 3 ^ 3, 7 ^ 1, 47 ^ 1, 630262089757493 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22394472573263241277 - 1) / 2 = 11197236286631620638 from by norm_num]
      have h2 : (6 : ZMod 22394472573263241277) ^ 11197236286631620638 = ((22394472573263241276 : ℕ) : ZMod 22394472573263241277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22394472573263241277 - 1) / 3 = 7464824191087747092 from by norm_num]
      have h2 : (6 : ZMod 22394472573263241277) ^ 7464824191087747092 = ((14511234774618524241 : ℕ) : ZMod 22394472573263241277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22394472573263241277 - 1) / 7 = 3199210367609034468 from by norm_num]
      have h2 : (6 : ZMod 22394472573263241277) ^ 3199210367609034468 = ((12773148193121058100 : ℕ) : ZMod 22394472573263241277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22394472573263241277 - 1) / 47 = 476478139856664708 from by norm_num]
      have h2 : (6 : ZMod 22394472573263241277) ^ 476478139856664708 = ((772633350656337745 : ℕ) : ZMod 22394472573263241277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_630262089757493).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22394472573263241277 - 1) / 630262089757493 = 35532 from by norm_num]
      have h2 : (6 : ZMod 22394472573263241277) ^ 35532 = ((21473036537743376503 : ℕ) : ZMod 22394472573263241277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1820450411621866648422581981583631 : Nat.Prime 1820450411621866648422581981583631 := by
  refine lucas_primality 1820450411621866648422581981583631 (7 : ZMod 1820450411621866648422581981583631) ?_ (fun q hq hd => ?_)
  · rw [show 1820450411621866648422581981583631 - 1 = 1820450411621866648422581981583630 from by norm_num]
    reduce_mod_char
  · have e : 1820450411621866648422581981583631 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 61 ^ 1, 751 ^ 1, 2143 ^ 1, 3943 ^ 1, 22394472573263241277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 2 = 910225205810933324211290990791815 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 910225205810933324211290990791815 = ((1820450411621866648422581981583630 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 3 = 606816803873955549474193993861210 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 606816803873955549474193993861210 = ((230670680751515884604556775312220 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 5 = 364090082324373329684516396316726 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 364090082324373329684516396316726 = ((1028582185420670690606787947193011 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 7 = 260064344517409521203225997369090 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 260064344517409521203225997369090 = ((642929592449132451894904269650286 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 61 = 29843449370850272924960360353830 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 29843449370850272924960360353830 = ((816515393244474184206541210755054 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 751 = 2424035168604349731587991986130 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 2424035168604349731587991986130 = ((886645250391823100802203819946434 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 2143 = 849486892964006835474839935410 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 849486892964006835474839935410 = ((814062818951464382109582344255444 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 3943 = 461691709769684668633675369410 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 461691709769684668633675369410 = ((205378825209625222995449724255030 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_22394472573263241277).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1820450411621866648422581981583631 - 1) / 22394472573263241277 = 81290166833190 from by norm_num]
      have h2 : (7 : ZMod 1820450411621866648422581981583631) ^ 81290166833190 = ((1195231987733382571101165129299624 : ℕ) : ZMod 1820450411621866648422581981583631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17498980673 : Nat.Prime 17498980673 := by
  refine lucas_primality 17498980673 (3 : ZMod 17498980673) ?_ (fun q hq hd => ?_)
  · rw [show 17498980673 - 1 = 17498980672 from by norm_num]
    reduce_mod_char
  · have e : 17498980673 - 1 = [2 ^ 6, 67 ^ 1, 73 ^ 1, 55903 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17498980673 - 1) / 2 = 8749490336 from by norm_num]
      have h2 : (3 : ZMod 17498980673) ^ 8749490336 = ((17498980672 : ℕ) : ZMod 17498980673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17498980673 - 1) / 67 = 261178816 from by norm_num]
      have h2 : (3 : ZMod 17498980673) ^ 261178816 = ((2426007536 : ℕ) : ZMod 17498980673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17498980673 - 1) / 73 = 239712064 from by norm_num]
      have h2 : (3 : ZMod 17498980673) ^ 239712064 = ((3948300848 : ℕ) : ZMod 17498980673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17498980673 - 1) / 55903 = 313024 from by norm_num]
      have h2 : (3 : ZMod 17498980673) ^ 313024 = ((9238646516 : ℕ) : ZMod 17498980673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_294564335740951689559 : Nat.Prime 294564335740951689559 := by
  refine lucas_primality 294564335740951689559 (3 : ZMod 294564335740951689559) ?_ (fun q hq hd => ?_)
  · rw [show 294564335740951689559 - 1 = 294564335740951689558 from by norm_num]
    reduce_mod_char
  · have e : 294564335740951689559 - 1 = [2 ^ 1, 3 ^ 3, 4513 ^ 1, 69073 ^ 1, 17498980673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294564335740951689559 - 1) / 2 = 147282167870475844779 from by norm_num]
      have h2 : (3 : ZMod 294564335740951689559) ^ 147282167870475844779 = ((294564335740951689558 : ℕ) : ZMod 294564335740951689559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294564335740951689559 - 1) / 3 = 98188111913650563186 from by norm_num]
      have h2 : (3 : ZMod 294564335740951689559) ^ 98188111913650563186 = ((28936704425557098074 : ℕ) : ZMod 294564335740951689559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294564335740951689559 - 1) / 4513 = 65270182969410966 from by norm_num]
      have h2 : (3 : ZMod 294564335740951689559) ^ 65270182969410966 = ((78219167916509725109 : ℕ) : ZMod 294564335740951689559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294564335740951689559 - 1) / 69073 = 4264536587971446 from by norm_num]
      have h2 : (3 : ZMod 294564335740951689559) ^ 4264536587971446 = ((209346178259688588746 : ℕ) : ZMod 294564335740951689559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17498980673).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (294564335740951689559 - 1) / 17498980673 = 16833228246 from by norm_num]
      have h2 : (3 : ZMod 294564335740951689559) ^ 16833228246 = ((76178703732697170538 : ℕ) : ZMod 294564335740951689559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2099182693095646638569878483 : Nat.Prime 2099182693095646638569878483 := by
  refine lucas_primality 2099182693095646638569878483 (2 : ZMod 2099182693095646638569878483) ?_ (fun q hq hd => ?_)
  · rw [show 2099182693095646638569878483 - 1 = 2099182693095646638569878482 from by norm_num]
    reduce_mod_char
  · have e : 2099182693095646638569878483 - 1 = [2 ^ 1, 3 ^ 2, 523 ^ 1, 757 ^ 1, 294564335740951689559 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099182693095646638569878483 - 1) / 2 = 1049591346547823319284939241 from by norm_num]
      have h2 : (2 : ZMod 2099182693095646638569878483) ^ 1049591346547823319284939241 = ((2099182693095646638569878482 : ℕ) : ZMod 2099182693095646638569878483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099182693095646638569878483 - 1) / 3 = 699727564365215546189959494 from by norm_num]
      have h2 : (2 : ZMod 2099182693095646638569878483) ^ 699727564365215546189959494 = ((317281036149188116127737286 : ℕ) : ZMod 2099182693095646638569878483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099182693095646638569878483 - 1) / 523 = 4013733638806207721930934 from by norm_num]
      have h2 : (2 : ZMod 2099182693095646638569878483) ^ 4013733638806207721930934 = ((1727510872040948404784447457 : ℕ) : ZMod 2099182693095646638569878483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099182693095646638569878483 - 1) / 757 = 2773028656665319205508426 from by norm_num]
      have h2 : (2 : ZMod 2099182693095646638569878483) ^ 2773028656665319205508426 = ((1072637473853613540154335584 : ℕ) : ZMod 2099182693095646638569878483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_294564335740951689559).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2099182693095646638569878483 - 1) / 294564335740951689559 = 7126398 from by norm_num]
      have h2 : (2 : ZMod 2099182693095646638569878483) ^ 7126398 = ((682645407994313988301759176 : ℕ) : ZMod 2099182693095646638569878483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_63716651 : Nat.Prime 63716651 := by
  refine lucas_primality 63716651 (2 : ZMod 63716651) ?_ (fun q hq hd => ?_)
  · rw [show 63716651 - 1 = 63716650 from by norm_num]
    reduce_mod_char
  · have e : 63716651 - 1 = [2 ^ 1, 5 ^ 2, 1274333 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63716651 - 1) / 2 = 31858325 from by norm_num]
      have h2 : (2 : ZMod 63716651) ^ 31858325 = ((63716650 : ℕ) : ZMod 63716651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63716651 - 1) / 5 = 12743330 from by norm_num]
      have h2 : (2 : ZMod 63716651) ^ 12743330 = ((27821166 : ℕ) : ZMod 63716651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63716651 - 1) / 1274333 = 50 from by norm_num]
      have h2 : (2 : ZMod 63716651) ^ 50 = ((50112506 : ℕ) : ZMod 63716651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_250455841 : Nat.Prime 250455841 := by
  refine lucas_primality 250455841 (14 : ZMod 250455841) ?_ (fun q hq hd => ?_)
  · rw [show 250455841 - 1 = 250455840 from by norm_num]
    reduce_mod_char
  · have e : 250455841 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 109 ^ 1, 4787 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250455841 - 1) / 2 = 125227920 from by norm_num]
      have h2 : (14 : ZMod 250455841) ^ 125227920 = ((250455840 : ℕ) : ZMod 250455841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250455841 - 1) / 3 = 83485280 from by norm_num]
      have h2 : (14 : ZMod 250455841) ^ 83485280 = ((98342948 : ℕ) : ZMod 250455841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250455841 - 1) / 5 = 50091168 from by norm_num]
      have h2 : (14 : ZMod 250455841) ^ 50091168 = ((86521280 : ℕ) : ZMod 250455841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250455841 - 1) / 109 = 2297760 from by norm_num]
      have h2 : (14 : ZMod 250455841) ^ 2297760 = ((119111769 : ℕ) : ZMod 250455841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (250455841 - 1) / 4787 = 52320 from by norm_num]
      have h2 : (14 : ZMod 250455841) ^ 52320 = ((44762019 : ℕ) : ZMod 250455841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24698220820062044069 : Nat.Prime 24698220820062044069 := by
  refine lucas_primality 24698220820062044069 (2 : ZMod 24698220820062044069) ?_ (fun q hq hd => ?_)
  · rw [show 24698220820062044069 - 1 = 24698220820062044068 from by norm_num]
    reduce_mod_char
  · have e : 24698220820062044069 - 1 = [2 ^ 2, 11 ^ 1, 379 ^ 1, 5913473 ^ 1, 250455841 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24698220820062044069 - 1) / 2 = 12349110410031022034 from by norm_num]
      have h2 : (2 : ZMod 24698220820062044069) ^ 12349110410031022034 = ((24698220820062044068 : ℕ) : ZMod 24698220820062044069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24698220820062044069 - 1) / 11 = 2245292801823822188 from by norm_num]
      have h2 : (2 : ZMod 24698220820062044069) ^ 2245292801823822188 = ((15036648535446515400 : ℕ) : ZMod 24698220820062044069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24698220820062044069 - 1) / 379 = 65166809551614892 from by norm_num]
      have h2 : (2 : ZMod 24698220820062044069) ^ 65166809551614892 = ((9207454606634486951 : ℕ) : ZMod 24698220820062044069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24698220820062044069 - 1) / 5913473 = 4176601604516 from by norm_num]
      have h2 : (2 : ZMod 24698220820062044069) ^ 4176601604516 = ((12682439997382693328 : ℕ) : ZMod 24698220820062044069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_250455841).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24698220820062044069 - 1) / 250455841 = 98613075748 from by norm_num]
      have h2 : (2 : ZMod 24698220820062044069) ^ 98613075748 = ((22634312862133238197 : ℕ) : ZMod 24698220820062044069) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_656822133606644237 : Nat.Prime 656822133606644237 := by
  refine lucas_primality 656822133606644237 (2 : ZMod 656822133606644237) ?_ (fun q hq hd => ?_)
  · rw [show 656822133606644237 - 1 = 656822133606644236 from by norm_num]
    reduce_mod_char
  · have e : 656822133606644237 - 1 = [2 ^ 2, 7 ^ 1, 11 ^ 1, 29 ^ 1, 383 ^ 1, 89897 ^ 1, 2135773 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 2 = 328411066803322118 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 328411066803322118 = ((656822133606644236 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 7 = 93831733372377748 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 93831733372377748 = ((279799484346023169 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 11 = 59711103055149476 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 59711103055149476 = ((292425300603183638 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 29 = 22649039089884284 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 22649039089884284 = ((614379045100308951 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 383 = 1714940296623092 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 1714940296623092 = ((247060618511650619 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 89897 = 7306385458988 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 7306385458988 = ((171526490391697525 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (656822133606644237 - 1) / 2135773 = 307533681532 from by norm_num]
      have h2 : (2 : ZMod 656822133606644237) ^ 307533681532 = ((206364447235256974 : ℕ) : ZMod 656822133606644237) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_49354941703447993616761 : Nat.Prime 49354941703447993616761 := by
  refine lucas_primality 49354941703447993616761 (11 : ZMod 49354941703447993616761) ?_ (fun q hq hd => ?_)
  · rw [show 49354941703447993616761 - 1 = 49354941703447993616760 from by norm_num]
    reduce_mod_char
  · have e : 49354941703447993616761 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 29 ^ 2, 769 ^ 1, 11197 ^ 1, 16139 ^ 1, 3519239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 2 = 24677470851723996808380 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 24677470851723996808380 = ((49354941703447993616760 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 3 = 16451647234482664538920 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 16451647234482664538920 = ((24591441029858691985303 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 5 = 9870988340689598723352 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 9870988340689598723352 = ((5124110263382817535977 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 29 = 1701894541498206676440 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 1701894541498206676440 = ((11355360976151669438445 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 769 = 64180678418007794040 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 64180678418007794040 = ((21595936312258362388829 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 11197 = 4407871903496293080 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 4407871903496293080 = ((33755635472376347128029 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 16139 = 3058116469635540840 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 3058116469635540840 = ((38221621428897957905779 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (49354941703447993616761 - 1) / 3519239 = 14024322219504840 from by norm_num]
      have h2 : (11 : ZMod 49354941703447993616761) ^ 14024322219504840 = ((21472157260022291988479 : ℕ) : ZMod 49354941703447993616761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_63543853 : Nat.Prime 63543853 := by
  refine lucas_primality 63543853 (2 : ZMod 63543853) ?_ (fun q hq hd => ?_)
  · rw [show 63543853 - 1 = 63543852 from by norm_num]
    reduce_mod_char
  · have e : 63543853 - 1 = [2 ^ 2, 3 ^ 4, 43 ^ 1, 4561 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63543853 - 1) / 2 = 31771926 from by norm_num]
      have h2 : (2 : ZMod 63543853) ^ 31771926 = ((63543852 : ℕ) : ZMod 63543853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63543853 - 1) / 3 = 21181284 from by norm_num]
      have h2 : (2 : ZMod 63543853) ^ 21181284 = ((46039941 : ℕ) : ZMod 63543853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63543853 - 1) / 43 = 1477764 from by norm_num]
      have h2 : (2 : ZMod 63543853) ^ 1477764 = ((47800747 : ℕ) : ZMod 63543853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63543853 - 1) / 4561 = 13932 from by norm_num]
      have h2 : (2 : ZMod 63543853) ^ 13932 = ((15936247 : ℕ) : ZMod 63543853) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2063851371725683433 : Nat.Prime 2063851371725683433 := by
  refine lucas_primality 2063851371725683433 (3 : ZMod 2063851371725683433) ?_ (fun q hq hd => ?_)
  · rw [show 2063851371725683433 - 1 = 2063851371725683432 from by norm_num]
    reduce_mod_char
  · have e : 2063851371725683433 - 1 = [2 ^ 3, 1721 ^ 1, 2359033 ^ 1, 63543853 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2063851371725683433 - 1) / 2 = 1031925685862841716 from by norm_num]
      have h2 : (3 : ZMod 2063851371725683433) ^ 1031925685862841716 = ((2063851371725683432 : ℕ) : ZMod 2063851371725683433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2063851371725683433 - 1) / 1721 = 1199216369393192 from by norm_num]
      have h2 : (3 : ZMod 2063851371725683433) ^ 1199216369393192 = ((1376094060675950426 : ℕ) : ZMod 2063851371725683433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2063851371725683433 - 1) / 2359033 = 874871768104 from by norm_num]
      have h2 : (3 : ZMod 2063851371725683433) ^ 874871768104 = ((758718135417561906 : ℕ) : ZMod 2063851371725683433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_63543853).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2063851371725683433 - 1) / 63543853 = 32479166344 from by norm_num]
      have h2 : (3 : ZMod 2063851371725683433) ^ 32479166344 = ((499983016713364087 : ℕ) : ZMod 2063851371725683433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_454333843 : Nat.Prime 454333843 := by
  refine lucas_primality 454333843 (2 : ZMod 454333843) ?_ (fun q hq hd => ?_)
  · rw [show 454333843 - 1 = 454333842 from by norm_num]
    reduce_mod_char
  · have e : 454333843 - 1 = [2 ^ 1, 3 ^ 2, 773 ^ 1, 32653 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (454333843 - 1) / 2 = 227166921 from by norm_num]
      have h2 : (2 : ZMod 454333843) ^ 227166921 = ((454333842 : ℕ) : ZMod 454333843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (454333843 - 1) / 3 = 151444614 from by norm_num]
      have h2 : (2 : ZMod 454333843) ^ 151444614 = ((104855400 : ℕ) : ZMod 454333843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (454333843 - 1) / 773 = 587754 from by norm_num]
      have h2 : (2 : ZMod 454333843) ^ 587754 = ((229553215 : ℕ) : ZMod 454333843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (454333843 - 1) / 32653 = 13914 from by norm_num]
      have h2 : (2 : ZMod 454333843) ^ 13914 = ((69878239 : ℕ) : ZMod 454333843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_63038579 : Nat.Prime 63038579 := by
  refine lucas_primality 63038579 (2 : ZMod 63038579) ?_ (fun q hq hd => ?_)
  · rw [show 63038579 - 1 = 63038578 from by norm_num]
    reduce_mod_char
  · have e : 63038579 - 1 = [2 ^ 1, 31519289 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63038579 - 1) / 2 = 31519289 from by norm_num]
      have h2 : (2 : ZMod 63038579) ^ 31519289 = ((63038578 : ℕ) : ZMod 63038579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (63038579 - 1) / 31519289 = 2 from by norm_num]
      have h2 : (2 : ZMod 63038579) ^ 2 = ((4 : ℕ) : ZMod 63038579) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2672085006016195513 : Nat.Prime 2672085006016195513 := by
  refine lucas_primality 2672085006016195513 (5 : ZMod 2672085006016195513) ?_ (fun q hq hd => ?_)
  · rw [show 2672085006016195513 - 1 = 2672085006016195512 from by norm_num]
    reduce_mod_char
  · have e : 2672085006016195513 - 1 = [2 ^ 3, 3 ^ 1, 509 ^ 1, 787 ^ 1, 4409 ^ 1, 63038579 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 2 = 1336042503008097756 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 1336042503008097756 = ((2672085006016195512 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 3 = 890695002005398504 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 890695002005398504 = ((1840718448836237937 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 509 = 5249675846790168 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 5249675846790168 = ((2390140690573751684 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 787 = 3395279550211176 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 3395279550211176 = ((1851633377145828943 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 4409 = 606052394197368 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 606052394197368 = ((2231748037745606080 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_63038579).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2672085006016195513 - 1) / 63038579 = 42388090728 from by norm_num]
      have h2 : (5 : ZMod 2672085006016195513) ^ 42388090728 = ((355613540908381469 : ℕ) : ZMod 2672085006016195513) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_807542599 : Nat.Prime 807542599 := by
  refine lucas_primality 807542599 (3 : ZMod 807542599) ?_ (fun q hq hd => ?_)
  · rw [show 807542599 - 1 = 807542598 from by norm_num]
    reduce_mod_char
  · have e : 807542599 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 7083707 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (807542599 - 1) / 2 = 403771299 from by norm_num]
      have h2 : (3 : ZMod 807542599) ^ 403771299 = ((807542598 : ℕ) : ZMod 807542599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (807542599 - 1) / 3 = 269180866 from by norm_num]
      have h2 : (3 : ZMod 807542599) ^ 269180866 = ((284133461 : ℕ) : ZMod 807542599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (807542599 - 1) / 19 = 42502242 from by norm_num]
      have h2 : (3 : ZMod 807542599) ^ 42502242 = ((696053570 : ℕ) : ZMod 807542599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (807542599 - 1) / 7083707 = 114 from by norm_num]
      have h2 : (3 : ZMod 807542599) ^ 114 = ((525130087 : ℕ) : ZMod 807542599) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4823258133603241 : Nat.Prime 4823258133603241 := by
  refine lucas_primality 4823258133603241 (7 : ZMod 4823258133603241) ?_ (fun q hq hd => ?_)
  · rw [show 4823258133603241 - 1 = 4823258133603240 from by norm_num]
    reduce_mod_char
  · have e : 4823258133603241 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 47 ^ 1, 353 ^ 1, 807542599 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 2 = 2411629066801620 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 2411629066801620 = ((4823258133603240 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 3 = 1607752711201080 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 1607752711201080 = ((3608769312308111 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 5 = 964651626720648 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 964651626720648 = ((748298120971190 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 47 = 102622513480920 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 102622513480920 = ((3805375892051976 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 353 = 13663620775080 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 13663620775080 = ((2220043615540595 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_807542599).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4823258133603241 - 1) / 807542599 = 5972760 from by norm_num]
      have h2 : (7 : ZMod 4823258133603241) ^ 5972760 = ((2808212602965789 : ℕ) : ZMod 4823258133603241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_439991139649 : Nat.Prime 439991139649 := by
  refine lucas_primality 439991139649 (7 : ZMod 439991139649) ?_ (fun q hq hd => ?_)
  · rw [show 439991139649 - 1 = 439991139648 from by norm_num]
    reduce_mod_char
  · have e : 439991139649 - 1 = [2 ^ 6, 3 ^ 1, 17 ^ 1, 53 ^ 1, 199 ^ 1, 12781 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 2 = 219995569824 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 219995569824 = ((439991139648 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 3 = 146663713216 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 146663713216 = ((296836284253 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 17 = 25881831744 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 25881831744 = ((83996500704 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 53 = 8301719616 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 8301719616 = ((231682046693 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 199 = 2211010752 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 2211010752 = ((390751062688 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (439991139649 - 1) / 12781 = 34425408 from by norm_num]
      have h2 : (7 : ZMod 439991139649) ^ 34425408 = ((188461803637 : ℕ) : ZMod 439991139649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- 3^502 + 1: 5 divides 3^502 + 1 and 1017977689 + 1 (chain 1017977689).
theorem kill3_e502 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 502 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1017977689 : 1017977689 ∈ P := S7 1017977689 prime_1017977689 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 502 = 3 ^ 200 * (3 ^ 200 * 3 ^ 102) by rw [← pow_add, ← pow_add]]; norm_num : 1017977689 ∣ 1 + 3 ^ 502).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 502 = 3 ^ 200 * (3 ^ 200 * 3 ^ 102) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 502).trans hd) 1017977689 g1017977689 (by norm_num)

-- 3^503 + 1: 5 divides 3019 + 1 and 19 + 1 (chains 3019; 3019 -> 151 -> 19).
theorem kill3_e503 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 503 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3019 : 3019 ∈ P := S7 3019 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 503 = 3 ^ 200 * (3 ^ 200 * 3 ^ 103) by rw [← pow_add, ← pow_add]]; norm_num : 3019 ∣ 1 + 3 ^ 503).trans hd)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^508 + 1: 7 divides 41 + 1 and 54093886887062230599082516017052647105427126977713417 + 1 (chains 41; 54093886887062230599082516017052647105427126977713417).
theorem kill3_e508 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 508 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 508 = 3 ^ 200 * (3 ^ 200 * 3 ^ 108) by rw [← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 508).trans hd)
  have g54093886887062230599082516017052647105427126977713417 : 54093886887062230599082516017052647105427126977713417 ∈ P := S7 54093886887062230599082516017052647105427126977713417 prime_54093886887062230599082516017052647105427126977713417 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 508 = 3 ^ 200 * (3 ^ 200 * 3 ^ 108) by rw [← pow_add, ← pow_add]]; norm_num : 54093886887062230599082516017052647105427126977713417 ∣ 1 + 3 ^ 508).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 54093886887062230599082516017052647105427126977713417 g54093886887062230599082516017052647105427126977713417 (by norm_num) (by norm_num)
  omega

-- 3^509 + 1: 7 divides 19557817 + 1 and 251 + 1 (chains 39115633 -> 19557817; 39115633 -> 19557817 -> 1396987 -> 12043 -> 3011 -> 251).
theorem kill3_e509 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 509 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g39115633 : 39115633 ∈ P := S7 39115633 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 509 = 3 ^ 200 * (3 ^ 200 * 3 ^ 109) by rw [← pow_add, ← pow_add]]; norm_num : 39115633 ∣ 1 + 3 ^ 509).trans hd)
  have g19557817 : 19557817 ∈ P := S1 19557817 (by norm_num) (by norm_num) (hnz (by norm_num)) 39115633 g39115633 (by norm_num)
  have g1396987 : 1396987 ∈ P := S1 1396987 (by norm_num) (by norm_num) (hnz (by norm_num)) 19557817 g19557817 (by norm_num)
  have g12043 : 12043 ∈ P := S1 12043 (by norm_num) (by norm_num) (hnz (by norm_num)) 1396987 g1396987 (by norm_num)
  have g3011 : 3011 ∈ P := S1 3011 (by norm_num) (by norm_num) (hnz (by norm_num)) 12043 g12043 (by norm_num)
  have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 3011 g3011 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 19557817 g19557817 251 g251 (by norm_num) (by norm_num)
  omega

-- 3^512 + 1: 5^2 divides 3499 + 1 (chain 134382593 -> 3499).
theorem kill3_e512 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 512 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g134382593 : 134382593 ∈ P := S7 134382593 prime_134382593 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 512 = 3 ^ 200 * (3 ^ 200 * 3 ^ 112) by rw [← pow_add, ← pow_add]]; norm_num : 134382593 ∣ 1 + 3 ^ 512).trans hd)
  have g3499 : 3499 ∈ P := S1 3499 (by norm_num) (by norm_num) (hnz (by norm_num)) 134382593 g134382593 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3499 g3499 (by norm_num)

-- 3^514 + 1: 5 divides 3^514 + 1 and 19 + 1 (chain 149789881 -> 19).
theorem kill3_e514 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 514 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g149789881 : 149789881 ∈ P := S7 149789881 prime_149789881 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 514 = 3 ^ 200 * (3 ^ 200 * 3 ^ 114) by rw [← pow_add, ← pow_add]]; norm_num : 149789881 ∣ 1 + 3 ^ 514).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 149789881 g149789881 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 514 = 3 ^ 200 * (3 ^ 200 * 3 ^ 114) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 514).trans hd) 19 g19 (by norm_num)

-- 3^521 + 1: 7 divides 162553 + 1 and 251 + 1 (chains 162553; 8421451860752373577 -> 251).
theorem kill3_e521 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 521 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g162553 : 162553 ∈ P := S7 162553 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 521 = 3 ^ 200 * (3 ^ 200 * 3 ^ 121) by rw [← pow_add, ← pow_add]]; norm_num : 162553 ∣ 1 + 3 ^ 521).trans hd)
  have g8421451860752373577 : 8421451860752373577 ∈ P := S7 8421451860752373577 prime_8421451860752373577 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 521 = 3 ^ 200 * (3 ^ 200 * 3 ^ 121) by rw [← pow_add, ← pow_add]]; norm_num : 8421451860752373577 ∣ 1 + 3 ^ 521).trans hd)
  have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 8421451860752373577 g8421451860752373577 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 162553 g162553 251 g251 (by norm_num) (by norm_num)
  omega

-- 3^523 + 1: 11 divides 1146386713 + 1 and 983179 + 1 (chains 1146386713; 1146386713 -> 983179).
theorem kill3_e523 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 523 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1146386713 : 1146386713 ∈ P := S7 1146386713 prime_1146386713 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 523 = 3 ^ 200 * (3 ^ 200 * 3 ^ 123) by rw [← pow_add, ← pow_add]]; norm_num : 1146386713 ∣ 1 + 3 ^ 523).trans hd)
  have g983179 : 983179 ∈ P := S1 983179 (by norm_num) (by norm_num) (hnz (by norm_num)) 1146386713 g1146386713 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1146386713 g1146386713 983179 g983179 (by norm_num) (by norm_num)
  omega

-- 3^524 + 1: 5^2 divides 1049 + 1 (chain 1049).
theorem kill3_e524 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 524 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1049 : 1049 ∈ P := S7 1049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 524 = 3 ^ 200 * (3 ^ 200 * 3 ^ 124) by rw [← pow_add, ← pow_add]]; norm_num : 1049 ∣ 1 + 3 ^ 524).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1049 g1049 (by norm_num)

-- 3^526 + 1: 19^2 divides 36821 + 1 (chain 36821).
theorem kill3_e526 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 526 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g36821 : 36821 ∈ P := S7 36821 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 526 = 3 ^ 200 * (3 ^ 200 * 3 ^ 126) by rw [← pow_add, ← pow_add]]; norm_num : 36821 ∣ 1 + 3 ^ 526).trans hd)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 36821 g36821 (by norm_num)

-- 3^538 + 1: 13^2 divides 2621920730595608239277 + 1 (chain 2621920730595608239277).
theorem kill3_e538 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 538 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2621920730595608239277 : 2621920730595608239277 ∈ P := S7 2621920730595608239277 prime_2621920730595608239277 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 538 = 3 ^ 200 * (3 ^ 200 * 3 ^ 138) by rw [← pow_add, ← pow_add]]; norm_num : 2621920730595608239277 ∣ 1 + 3 ^ 538).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2621920730595608239277 g2621920730595608239277 (by norm_num)

-- 3^541 + 1: 7 divides 71413 + 1 and 147842923003 + 1 (chains 71413; 147842923003).
theorem kill3_e541 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 541 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g71413 : 71413 ∈ P := S7 71413 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 541 = 3 ^ 200 * (3 ^ 200 * 3 ^ 141) by rw [← pow_add, ← pow_add]]; norm_num : 71413 ∣ 1 + 3 ^ 541).trans hd)
  have g147842923003 : 147842923003 ∈ P := S7 147842923003 prime_147842923003 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 541 = 3 ^ 200 * (3 ^ 200 * 3 ^ 141) by rw [← pow_add, ← pow_add]]; norm_num : 147842923003 ∣ 1 + 3 ^ 541).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 71413 g71413 147842923003 g147842923003 (by norm_num) (by norm_num)
  omega

-- 3^542 + 1: 5 divides 3^542 + 1 and 7589 + 1 (chain 7589).
theorem kill3_e542 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 542 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7589 : 7589 ∈ P := S7 7589 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 542 = 3 ^ 200 * (3 ^ 200 * 3 ^ 142) by rw [← pow_add, ← pow_add]]; norm_num : 7589 ∣ 1 + 3 ^ 542).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 542 = 3 ^ 200 * (3 ^ 200 * 3 ^ 142) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 542).trans hd) 7589 g7589 (by norm_num)

-- 3^547 + 1: 17^2 divides 577 + 1 (chain 357739 -> 577).
theorem kill3_e547 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 547 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g357739 : 357739 ∈ P := S7 357739 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 547 = 3 ^ 200 * (3 ^ 200 * 3 ^ 147) by rw [← pow_add, ← pow_add]]; norm_num : 357739 ∣ 1 + 3 ^ 547).trans hd)
  have g577 : 577 ∈ P := S1 577 (by norm_num) (by norm_num) (hnz (by norm_num)) 357739 g357739 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)

-- 3^548 + 1: 5^2 divides 6217786649 + 1 (chain 6217786649).
theorem kill3_e548 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 548 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6217786649 : 6217786649 ∈ P := S7 6217786649 prime_6217786649 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 548 = 3 ^ 200 * (3 ^ 200 * 3 ^ 148) by rw [← pow_add, ← pow_add]]; norm_num : 6217786649 ∣ 1 + 3 ^ 548).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6217786649 g6217786649 (by norm_num)

-- 3^554 + 1: 5 divides 3^554 + 1 and 1109 + 1 (chain 1109).
theorem kill3_e554 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 554 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1109 : 1109 ∈ P := S7 1109 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 554 = 3 ^ 200 * (3 ^ 200 * 3 ^ 154) by rw [← pow_add, ← pow_add]]; norm_num : 1109 ∣ 1 + 3 ^ 554).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 554 = 3 ^ 200 * (3 ^ 200 * 3 ^ 154) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 554).trans hd) 1109 g1109 (by norm_num)

-- 3^556 + 1: 7 divides 41 + 1 and 223 + 1 (chains 41; 579353 -> 223).
theorem kill3_e556 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 556 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 556 = 3 ^ 200 * (3 ^ 200 * 3 ^ 156) by rw [← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 556).trans hd)
  have g579353 : 579353 ∈ P := S7 579353 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 556 = 3 ^ 200 * (3 ^ 200 * 3 ^ 156) by rw [← pow_add, ← pow_add]]; norm_num : 579353 ∣ 1 + 3 ^ 556).trans hd)
  have g223 : 223 ∈ P := S1 223 (by norm_num) (by norm_num) (hnz (by norm_num)) 579353 g579353 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 223 g223 (by norm_num) (by norm_num)
  omega

-- 3^557 + 1: 7^2 divides 495738992209 + 1 (chain 495738992209).
theorem kill3_e557 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 557 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g495738992209 : 495738992209 ∈ P := S7 495738992209 prime_495738992209 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 557 = 3 ^ 200 * (3 ^ 200 * 3 ^ 157) by rw [← pow_add, ← pow_add]]; norm_num : 495738992209 ∣ 1 + 3 ^ 557).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 495738992209 g495738992209 (by norm_num)

-- 3^562 + 1: 5 divides 3^562 + 1 and 29 + 1 (chain 3751695056761 -> 173 -> 29).
theorem kill3_e562 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 562 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3751695056761 : 3751695056761 ∈ P := S7 3751695056761 prime_3751695056761 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 562 = 3 ^ 200 * (3 ^ 200 * 3 ^ 162) by rw [← pow_add, ← pow_add]]; norm_num : 3751695056761 ∣ 1 + 3 ^ 562).trans hd)
  have g173 : 173 ∈ P := S1 173 (by norm_num) (by norm_num) (hnz (by norm_num)) 3751695056761 g3751695056761 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 562 = 3 ^ 200 * (3 ^ 200 * 3 ^ 162) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 562).trans hd) 29 g29 (by norm_num)

-- 3^563 + 1: 29 divides 13513 + 1 and 46901369347503080003230459 + 1 (chains 13513; 46901369347503080003230459).
theorem kill3_e563 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 563 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13513 : 13513 ∈ P := S7 13513 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 563 = 3 ^ 200 * (3 ^ 200 * 3 ^ 163) by rw [← pow_add, ← pow_add]]; norm_num : 13513 ∣ 1 + 3 ^ 563).trans hd)
  have g46901369347503080003230459 : 46901369347503080003230459 ∈ P := S7 46901369347503080003230459 prime_46901369347503080003230459 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 563 = 3 ^ 200 * (3 ^ 200 * 3 ^ 163) by rw [← pow_add, ← pow_add]]; norm_num : 46901369347503080003230459 ∣ 1 + 3 ^ 563).trans hd)
  have := S3 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 13513 g13513 46901369347503080003230459 g46901369347503080003230459 (by norm_num) (by norm_num)
  omega

-- 3^566 + 1: 5 divides 3^566 + 1 and 19 + 1 (chain 34523737 -> 37 -> 19).
theorem kill3_e566 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 566 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g34523737 : 34523737 ∈ P := S7 34523737 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 566 = 3 ^ 200 * (3 ^ 200 * 3 ^ 166) by rw [← pow_add, ← pow_add]]; norm_num : 34523737 ∣ 1 + 3 ^ 566).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 34523737 g34523737 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 566 = 3 ^ 200 * (3 ^ 200 * 3 ^ 166) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 566).trans hd) 19 g19 (by norm_num)

-- 3^569 + 1: 5 divides 29 + 1 and 19 + 1 (chains 37400371 -> 29; 37400371 -> 322417 -> 37 -> 19).
theorem kill3_e569 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 569 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37400371 : 37400371 ∈ P := S7 37400371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 569 = 3 ^ 200 * (3 ^ 200 * 3 ^ 169) by rw [← pow_add, ← pow_add]]; norm_num : 37400371 ∣ 1 + 3 ^ 569).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 37400371 g37400371 (by norm_num)
  have g322417 : 322417 ∈ P := S1 322417 (by norm_num) (by norm_num) (hnz (by norm_num)) 37400371 g37400371 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 322417 g322417 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^571 + 1: 7 divides 727 + 1 and 13 + 1 (chains 1942543 -> 727; 1942543 -> 727 -> 13).
theorem kill3_e571 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 571 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1942543 : 1942543 ∈ P := S7 1942543 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 571 = 3 ^ 200 * (3 ^ 200 * 3 ^ 171) by rw [← pow_add, ← pow_add]]; norm_num : 1942543 ∣ 1 + 3 ^ 571).trans hd)
  have g727 : 727 ∈ P := S1 727 (by norm_num) (by norm_num) (hnz (by norm_num)) 1942543 g1942543 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 727 g727 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 727 g727 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^586 + 1: 5 divides 3^586 + 1 and 146053437529 + 1 (chain 292106875057 -> 146053437529).
theorem kill3_e586 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 586 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g292106875057 : 292106875057 ∈ P := S7 292106875057 prime_292106875057 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 586 = 3 ^ 200 * (3 ^ 200 * 3 ^ 186) by rw [← pow_add, ← pow_add]]; norm_num : 292106875057 ∣ 1 + 3 ^ 586).trans hd)
  have g146053437529 : 146053437529 ∈ P := S1 146053437529 prime_146053437529 (by norm_num) (hnz (by norm_num)) 292106875057 g292106875057 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 586 = 3 ^ 200 * (3 ^ 200 * 3 ^ 186) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 586).trans hd) 146053437529 g146053437529 (by norm_num)

-- 3^587 + 1: 5 divides 235085219994159229 + 1 and 500181319136509 + 1 (chains 235085219994159229; 235085219994159229 -> 500181319136509).
theorem kill3_e587 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 587 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g235085219994159229 : 235085219994159229 ∈ P := S7 235085219994159229 prime_235085219994159229 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 587 = 3 ^ 200 * (3 ^ 200 * 3 ^ 187) by rw [← pow_add, ← pow_add]]; norm_num : 235085219994159229 ∣ 1 + 3 ^ 587).trans hd)
  have g500181319136509 : 500181319136509 ∈ P := S1 500181319136509 prime_500181319136509 (by norm_num) (hnz (by norm_num)) 235085219994159229 g235085219994159229 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 235085219994159229 g235085219994159229 500181319136509 g500181319136509 (by norm_num) (by norm_num)
  omega

-- 3^593 + 1: 5^2 divides 1256149 + 1 (chain 211197634469030854488137501976187207 -> 1256149).
theorem kill3_e593 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 593 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g211197634469030854488137501976187207 : 211197634469030854488137501976187207 ∈ P := S7 211197634469030854488137501976187207 prime_211197634469030854488137501976187207 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 593 = 3 ^ 200 * (3 ^ 200 * 3 ^ 193) by rw [← pow_add, ← pow_add]]; norm_num : 211197634469030854488137501976187207 ∣ 1 + 3 ^ 593).trans hd)
  have g1256149 : 1256149 ∈ P := S1 1256149 (by norm_num) (by norm_num) (hnz (by norm_num)) 211197634469030854488137501976187207 g211197634469030854488137501976187207 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1256149 g1256149 (by norm_num)

-- 3^596 + 1: 5^2 divides 199 + 1 (chain 1193 -> 199).
theorem kill3_e596 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 596 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1193 : 1193 ∈ P := S7 1193 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 596 = 3 ^ 200 * (3 ^ 200 * 3 ^ 196) by rw [← pow_add, ← pow_add]]; norm_num : 1193 ∣ 1 + 3 ^ 596).trans hd)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 1193 g1193 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

-- 3^599 + 1: 5^2 divides 499 + 1 (chain 27263461551898213 -> 499).
theorem kill3_e599 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 599 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g27263461551898213 : 27263461551898213 ∈ P := S7 27263461551898213 prime_27263461551898213 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 599 = 3 ^ 200 * (3 ^ 200 * 3 ^ 199) by rw [← pow_add, ← pow_add]]; norm_num : 27263461551898213 ∣ 1 + 3 ^ 599).trans hd)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 27263461551898213 g27263461551898213 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

-- 3^601 + 1: 3607 divides 3^601 + 1 and 7213 + 1 (chain 7213).
theorem kill3_e601 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 601 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7213 : 7213 ∈ P := S7 7213 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 601 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 1)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 7213 ∣ 1 + 3 ^ 601).trans hd)
  exact S8 3607 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 601 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 1)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3607 ∣ 1 + 3 ^ 601).trans hd) 7213 g7213 (by norm_num)

-- 3^604 + 1: 7^2 divides 2938627 + 1 (chain 624158251060640521747881981606817836433 -> 312079125530320260873940990803408918217 -> 2938627).
theorem kill3_e604 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 604 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g624158251060640521747881981606817836433 : 624158251060640521747881981606817836433 ∈ P := S7 624158251060640521747881981606817836433 prime_624158251060640521747881981606817836433 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 604 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 4)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 624158251060640521747881981606817836433 ∣ 1 + 3 ^ 604).trans hd)
  have g312079125530320260873940990803408918217 : 312079125530320260873940990803408918217 ∈ P := S1 312079125530320260873940990803408918217 prime_312079125530320260873940990803408918217 (by norm_num) (hnz (by norm_num)) 624158251060640521747881981606817836433 g624158251060640521747881981606817836433 (by norm_num)
  have g2938627 : 2938627 ∈ P := S1 2938627 (by norm_num) (by norm_num) (hnz (by norm_num)) 312079125530320260873940990803408918217 g312079125530320260873940990803408918217 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2938627 g2938627 (by norm_num)

-- 3^607 + 1: 5 divides 6829 + 1 and 19 + 1 (chains 54631 -> 6829; 54631 -> 6829 -> 683 -> 19).
theorem kill3_e607 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 607 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g54631 : 54631 ∈ P := S7 54631 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 607 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 7)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 54631 ∣ 1 + 3 ^ 607).trans hd)
  have g6829 : 6829 ∈ P := S1 6829 (by norm_num) (by norm_num) (hnz (by norm_num)) 54631 g54631 (by norm_num)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 6829 g6829 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6829 g6829 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^613 + 1: 11^2 divides 5807 + 1 (chain 582664694022060378487303494994260032536305143468203 -> 5807).
theorem kill3_e613 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 613 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g582664694022060378487303494994260032536305143468203 : 582664694022060378487303494994260032536305143468203 ∈ P := S7 582664694022060378487303494994260032536305143468203 prime_582664694022060378487303494994260032536305143468203 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 613 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 13)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 582664694022060378487303494994260032536305143468203 ∣ 1 + 3 ^ 613).trans hd)
  have g5807 : 5807 ∈ P := S1 5807 (by norm_num) (by norm_num) (hnz (by norm_num)) 582664694022060378487303494994260032536305143468203 g582664694022060378487303494994260032536305143468203 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5807 g5807 (by norm_num)

-- 3^614 + 1: 5 divides 3^614 + 1 and 1229 + 1 (chain 1229).
theorem kill3_e614 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 614 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1229 : 1229 ∈ P := S7 1229 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 614 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 14)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1229 ∣ 1 + 3 ^ 614).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 614 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 14)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 614).trans hd) 1229 g1229 (by norm_num)

-- 3^617 + 1: 5^2 divides 17236983499017921972849595101062911347678496967884099 + 1 (chain 17236983499017921972849595101062911347678496967884099).
theorem kill3_e617 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 617 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17236983499017921972849595101062911347678496967884099 : 17236983499017921972849595101062911347678496967884099 ∈ P := S7 17236983499017921972849595101062911347678496967884099 prime_17236983499017921972849595101062911347678496967884099 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 617 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 17)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 17236983499017921972849595101062911347678496967884099 ∣ 1 + 3 ^ 617).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 17236983499017921972849595101062911347678496967884099 g17236983499017921972849595101062911347678496967884099 (by norm_num)

-- 3^619 + 1: 5^2 divides 24909799 + 1 (chain 24909799).
theorem kill3_e619 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 619 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g24909799 : 24909799 ∈ P := S7 24909799 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 619 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 19)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 24909799 ∣ 1 + 3 ^ 619).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 24909799 g24909799 (by norm_num)

-- 3^622 + 1: 5 divides 3^622 + 1 and 36893309 + 1 (chain 36893309).
theorem kill3_e622 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 622 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g36893309 : 36893309 ∈ P := S7 36893309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 622 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 22)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 36893309 ∣ 1 + 3 ^ 622).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 622 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 22)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 622).trans hd) 36893309 g36893309 (by norm_num)

-- 3^626 + 1: 5 divides 3^626 + 1 and 8999 + 1 (chain 28462659967079735788297 -> 8999).
theorem kill3_e626 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 626 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g28462659967079735788297 : 28462659967079735788297 ∈ P := S7 28462659967079735788297 prime_28462659967079735788297 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 626 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 26)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 28462659967079735788297 ∣ 1 + 3 ^ 626).trans hd)
  have g8999 : 8999 ∈ P := S1 8999 (by norm_num) (by norm_num) (hnz (by norm_num)) 28462659967079735788297 g28462659967079735788297 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 626 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 26)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 626).trans hd) 8999 g8999 (by norm_num)

-- 3^628 + 1: 5 divides 79 + 1 and 24343016953382358704409035657305528570198669421823919 + 1 (chains 126170538473855459870995755264812959134139669176057183246713 -> 7009474359658636659499764181378497729674426065336510180373 -> 941 -> 157 -> 79; 126170538473855459870995755264812959134139669176057183246713 -> 7009474359658636659499764181378497729674426065336510180373 -> 24343016953382358704409035657305528570198669421823919).
theorem kill3_e628 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 628 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g126170538473855459870995755264812959134139669176057183246713 : 126170538473855459870995755264812959134139669176057183246713 ∈ P := S7 126170538473855459870995755264812959134139669176057183246713 prime_126170538473855459870995755264812959134139669176057183246713 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 628 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 28)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 126170538473855459870995755264812959134139669176057183246713 ∣ 1 + 3 ^ 628).trans hd)
  have g7009474359658636659499764181378497729674426065336510180373 : 7009474359658636659499764181378497729674426065336510180373 ∈ P := S1 7009474359658636659499764181378497729674426065336510180373 prime_7009474359658636659499764181378497729674426065336510180373 (by norm_num) (hnz (by norm_num)) 126170538473855459870995755264812959134139669176057183246713 g126170538473855459870995755264812959134139669176057183246713 (by norm_num)
  have g941 : 941 ∈ P := S1 941 (by norm_num) (by norm_num) (hnz (by norm_num)) 7009474359658636659499764181378497729674426065336510180373 g7009474359658636659499764181378497729674426065336510180373 (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 941 g941 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  have g24343016953382358704409035657305528570198669421823919 : 24343016953382358704409035657305528570198669421823919 ∈ P := S1 24343016953382358704409035657305528570198669421823919 prime_24343016953382358704409035657305528570198669421823919 (by norm_num) (hnz (by norm_num)) 7009474359658636659499764181378497729674426065336510180373 g7009474359658636659499764181378497729674426065336510180373 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 79 g79 24343016953382358704409035657305528570198669421823919 g24343016953382358704409035657305528570198669421823919 (by norm_num) (by norm_num)
  omega

-- 3^631 + 1: 5^2 divides 1677199 + 1 (chain 3354397 -> 1677199).
theorem kill3_e631 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 631 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3354397 : 3354397 ∈ P := S7 3354397 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 631 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 31)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3354397 ∣ 1 + 3 ^ 631).trans hd)
  have g1677199 : 1677199 ∈ P := S1 1677199 (by norm_num) (by norm_num) (hnz (by norm_num)) 3354397 g3354397 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1677199 g1677199 (by norm_num)

-- 3^634 + 1: 5 divides 3^634 + 1 and 10383775510679 + 1 (chain 472401162592505264461751488855196441634426625661 -> 10383775510679).
theorem kill3_e634 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 634 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g472401162592505264461751488855196441634426625661 : 472401162592505264461751488855196441634426625661 ∈ P := S7 472401162592505264461751488855196441634426625661 prime_472401162592505264461751488855196441634426625661 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 634 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 34)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 472401162592505264461751488855196441634426625661 ∣ 1 + 3 ^ 634).trans hd)
  have g10383775510679 : 10383775510679 ∈ P := S1 10383775510679 prime_10383775510679 (by norm_num) (hnz (by norm_num)) 472401162592505264461751488855196441634426625661 g472401162592505264461751488855196441634426625661 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 634 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 34)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 634).trans hd) 10383775510679 g10383775510679 (by norm_num)

-- 3^641 + 1: 7 divides 46633 + 1 and 3331 + 1 (chains 373063 -> 46633; 373063 -> 46633 -> 3331).
theorem kill3_e641 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 641 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g373063 : 373063 ∈ P := S7 373063 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 641 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 41)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 373063 ∣ 1 + 3 ^ 641).trans hd)
  have g46633 : 46633 ∈ P := S1 46633 (by norm_num) (by norm_num) (hnz (by norm_num)) 373063 g373063 (by norm_num)
  have g3331 : 3331 ∈ P := S1 3331 (by norm_num) (by norm_num) (hnz (by norm_num)) 46633 g46633 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 46633 g46633 3331 g3331 (by norm_num) (by norm_num)
  omega

-- 3^643 + 1: 5 divides 3297828698676263965255996064314097775904874359 + 1 and 19 + 1 (chains 3297828698676263965255996064314097775904874359; 3297828698676263965255996064314097775904874359 -> 14155301 -> 337031 -> 151 -> 19).
theorem kill3_e643 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 643 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3297828698676263965255996064314097775904874359 : 3297828698676263965255996064314097775904874359 ∈ P := S7 3297828698676263965255996064314097775904874359 prime_3297828698676263965255996064314097775904874359 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 643 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 43)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 3297828698676263965255996064314097775904874359 ∣ 1 + 3 ^ 643).trans hd)
  have g14155301 : 14155301 ∈ P := S1 14155301 (by norm_num) (by norm_num) (hnz (by norm_num)) 3297828698676263965255996064314097775904874359 g3297828698676263965255996064314097775904874359 (by norm_num)
  have g337031 : 337031 ∈ P := S1 337031 (by norm_num) (by norm_num) (hnz (by norm_num)) 14155301 g14155301 (by norm_num)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 337031 g337031 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3297828698676263965255996064314097775904874359 g3297828698676263965255996064314097775904874359 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^647 + 1: 7 divides 147517 + 1 and 41 + 1 (chains 295033 -> 147517; 295033 -> 147517 -> 41).
theorem kill3_e647 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 647 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g295033 : 295033 ∈ P := S7 295033 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 647 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 47)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 295033 ∣ 1 + 3 ^ 647).trans hd)
  have g147517 : 147517 ∈ P := S1 147517 (by norm_num) (by norm_num) (hnz (by norm_num)) 295033 g295033 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 147517 g147517 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 147517 g147517 41 g41 (by norm_num) (by norm_num)
  omega

-- 3^652 + 1: 5 divides 289489 + 1 and 28949 + 1 (chains 289489; 289489 -> 28949).
theorem kill3_e652 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 652 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g289489 : 289489 ∈ P := S7 289489 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 652 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 52)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 289489 ∣ 1 + 3 ^ 652).trans hd)
  have g28949 : 28949 ∈ P := S1 28949 (by norm_num) (by norm_num) (hnz (by norm_num)) 289489 g289489 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 289489 g289489 28949 g28949 (by norm_num) (by norm_num)
  omega

-- 3^653 + 1: 5^2 divides 2099 + 1 (chain 58771 -> 2099).
theorem kill3_e653 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 653 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58771 : 58771 ∈ P := S7 58771 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 653 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 53)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 58771 ∣ 1 + 3 ^ 653).trans hd)
  have g2099 : 2099 ∈ P := S1 2099 (by norm_num) (by norm_num) (hnz (by norm_num)) 58771 g58771 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2099 g2099 (by norm_num)

-- 3^659 + 1: 5^2 divides 291899 + 1 (chain 91072483 -> 22768121 -> 291899).
theorem kill3_e659 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 659 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g91072483 : 91072483 ∈ P := S7 91072483 prime_91072483 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 659 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 59)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 91072483 ∣ 1 + 3 ^ 659).trans hd)
  have g22768121 : 22768121 ∈ P := S1 22768121 (by norm_num) (by norm_num) (hnz (by norm_num)) 91072483 g91072483 (by norm_num)
  have g291899 : 291899 ∈ P := S1 291899 (by norm_num) (by norm_num) (hnz (by norm_num)) 22768121 g22768121 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 291899 g291899 (by norm_num)

-- 3^661 + 1: 5 divides 1051615000043032744519 + 1 and 65419 + 1 (chains 1051615000043032744519; 1051615000043032744519 -> 65419).
theorem kill3_e661 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 661 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1051615000043032744519 : 1051615000043032744519 ∈ P := S7 1051615000043032744519 prime_1051615000043032744519 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 661 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 61)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1051615000043032744519 ∣ 1 + 3 ^ 661).trans hd)
  have g65419 : 65419 ∈ P := S1 65419 (by norm_num) (by norm_num) (hnz (by norm_num)) 1051615000043032744519 g1051615000043032744519 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1051615000043032744519 g1051615000043032744519 65419 g65419 (by norm_num) (by norm_num)
  omega

-- 3^662 + 1: 5 divides 3^662 + 1 and 5854729 + 1 (chain 5854729).
theorem kill3_e662 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 662 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5854729 : 5854729 ∈ P := S7 5854729 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 662 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 62)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5854729 ∣ 1 + 3 ^ 662).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 662 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 62)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 662).trans hd) 5854729 g5854729 (by norm_num)

-- 3^668 + 1: 7 divides 41 + 1 and 2452897 + 1 (chains 41; 2452897).
theorem kill3_e668 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 668 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 668 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 68)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 668).trans hd)
  have g2452897 : 2452897 ∈ P := S7 2452897 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 668 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 68)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 2452897 ∣ 1 + 3 ^ 668).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 2452897 g2452897 (by norm_num) (by norm_num)
  omega

-- 3^673 + 1: 5 divides 226129 + 1 and 3769 + 1 (chains 226129; 226129 -> 22613 -> 3769).
theorem kill3_e673 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 673 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g226129 : 226129 ∈ P := S7 226129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 673 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 73)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 226129 ∣ 1 + 3 ^ 673).trans hd)
  have g22613 : 22613 ∈ P := S1 22613 (by norm_num) (by norm_num) (hnz (by norm_num)) 226129 g226129 (by norm_num)
  have g3769 : 3769 ∈ P := S1 3769 (by norm_num) (by norm_num) (hnz (by norm_num)) 22613 g22613 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 226129 g226129 3769 g3769 (by norm_num) (by norm_num)
  omega

-- 3^674 + 1: 11^2 divides 9437 + 1 (chain 9437).
theorem kill3_e674 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 674 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9437 : 9437 ∈ P := S7 9437 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 674 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 74)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 9437 ∣ 1 + 3 ^ 674).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 9437 g9437 (by norm_num)

-- 3^677 + 1: 5 divides 19 + 1 and 29 + 1 (chains 192173221 -> 96086611 -> 113 -> 19; 192173221 -> 96086611 -> 4523 -> 29).
theorem kill3_e677 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 677 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g192173221 : 192173221 ∈ P := S7 192173221 prime_192173221 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 677 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 77)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 192173221 ∣ 1 + 3 ^ 677).trans hd)
  have g96086611 : 96086611 ∈ P := S1 96086611 prime_96086611 (by norm_num) (hnz (by norm_num)) 192173221 g192173221 (by norm_num)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 96086611 g96086611 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
  have g4523 : 4523 ∈ P := S1 4523 (by norm_num) (by norm_num) (hnz (by norm_num)) 96086611 g96086611 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 4523 g4523 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

-- 3^683 + 1: 5^2 divides 4099 + 1 (chain 4099).
theorem kill3_e683 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 683 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4099 : 4099 ∈ P := S7 4099 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 683 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 83)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 4099 ∣ 1 + 3 ^ 683).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4099 g4099 (by norm_num)

-- 3^691 + 1: 5 divides 29 + 1 and 89 + 1 (chains 8913901 -> 4456951 -> 29; 8913901 -> 4456951 -> 19211 -> 1601 -> 89).
theorem kill3_e691 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 691 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8913901 : 8913901 ∈ P := S7 8913901 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 691 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 91)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 8913901 ∣ 1 + 3 ^ 691).trans hd)
  have g4456951 : 4456951 ∈ P := S1 4456951 (by norm_num) (by norm_num) (hnz (by norm_num)) 8913901 g8913901 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 4456951 g4456951 (by norm_num)
  have g19211 : 19211 ∈ P := S1 19211 (by norm_num) (by norm_num) (hnz (by norm_num)) 4456951 g4456951 (by norm_num)
  have g1601 : 1601 ∈ P := S1 1601 (by norm_num) (by norm_num) (hnz (by norm_num)) 19211 g19211 (by norm_num)
  have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 1601 g1601 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 89 g89 (by norm_num) (by norm_num)
  omega

-- 3^692 + 1: 7 divides 41 + 1 and 13 + 1 (chains 41; 9114428881 -> 13).
theorem kill3_e692 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 692 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 692 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 92)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 692).trans hd)
  have g9114428881 : 9114428881 ∈ P := S7 9114428881 prime_9114428881 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 692 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 92)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 9114428881 ∣ 1 + 3 ^ 692).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 9114428881 g9114428881 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^694 + 1: 5 divides 3^694 + 1 and 1072108053199 + 1 (chain 606813158110633 -> 1072108053199).
theorem kill3_e694 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 694 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g606813158110633 : 606813158110633 ∈ P := S7 606813158110633 prime_606813158110633 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 694 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 94)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 606813158110633 ∣ 1 + 3 ^ 694).trans hd)
  have g1072108053199 : 1072108053199 ∈ P := S1 1072108053199 prime_1072108053199 (by norm_num) (hnz (by norm_num)) 606813158110633 g606813158110633 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 694 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 94)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 694).trans hd) 1072108053199 g1072108053199 (by norm_num)

-- 3^698 + 1: 5 divides 3^698 + 1 and 59 + 1 (chain 8377 -> 59).
theorem kill3_e698 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 698 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8377 : 8377 ∈ P := S7 8377 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 698 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 98)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 8377 ∣ 1 + 3 ^ 698).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 8377 g8377 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 698 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 98)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 698).trans hd) 59 g59 (by norm_num)

-- 3^701 + 1: 11 divides 62426803493 + 1 and 593 + 1 (chains 790198478614393 -> 62426803493; 790198478614393 -> 62426803493 -> 2371 -> 593).
theorem kill3_e701 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 701 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g790198478614393 : 790198478614393 ∈ P := S7 790198478614393 prime_790198478614393 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 701 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 101)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 790198478614393 ∣ 1 + 3 ^ 701).trans hd)
  have g62426803493 : 62426803493 ∈ P := S1 62426803493 prime_62426803493 (by norm_num) (hnz (by norm_num)) 790198478614393 g790198478614393 (by norm_num)
  have g2371 : 2371 ∈ P := S1 2371 (by norm_num) (by norm_num) (hnz (by norm_num)) 62426803493 g62426803493 (by norm_num)
  have g593 : 593 ∈ P := S1 593 (by norm_num) (by norm_num) (hnz (by norm_num)) 2371 g2371 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 62426803493 g62426803493 593 g593 (by norm_num) (by norm_num)
  omega

-- 3^706 + 1: 5 divides 3^706 + 1 and 809 + 1 (chain 211902173811073 -> 809).
theorem kill3_e706 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 706 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g211902173811073 : 211902173811073 ∈ P := S7 211902173811073 prime_211902173811073 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 706 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 106)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 211902173811073 ∣ 1 + 3 ^ 706).trans hd)
  have g809 : 809 ∈ P := S1 809 (by norm_num) (by norm_num) (hnz (by norm_num)) 211902173811073 g211902173811073 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 706 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 106)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 706).trans hd) 809 g809 (by norm_num)

-- 3^709 + 1: 5 divides 19 + 1 and 19709 + 1 (chains 159280471573 -> 8238361 -> 19; 159280471573 -> 8238361 -> 19709).
theorem kill3_e709 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 709 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g159280471573 : 159280471573 ∈ P := S7 159280471573 prime_159280471573 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 709 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 109)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 159280471573 ∣ 1 + 3 ^ 709).trans hd)
  have g8238361 : 8238361 ∈ P := S1 8238361 (by norm_num) (by norm_num) (hnz (by norm_num)) 159280471573 g159280471573 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 8238361 g8238361 (by norm_num)
  have g19709 : 19709 ∈ P := S1 19709 (by norm_num) (by norm_num) (hnz (by norm_num)) 8238361 g8238361 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 19709 g19709 (by norm_num) (by norm_num)
  omega

-- 3^716 + 1: 5 divides 239 + 1 and 19 + 1 (chains 1433 -> 239; 5130857 -> 855143 -> 37 -> 19).
theorem kill3_e716 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 716 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1433 : 1433 ∈ P := S7 1433 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 716 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 116)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1433 ∣ 1 + 3 ^ 716).trans hd)
  have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 1433 g1433 (by norm_num)
  have g5130857 : 5130857 ∈ P := S7 5130857 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 716 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 116)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5130857 ∣ 1 + 3 ^ 716).trans hd)
  have g855143 : 855143 ∈ P := S1 855143 (by norm_num) (by norm_num) (hnz (by norm_num)) 5130857 g5130857 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 855143 g855143 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 239 g239 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^718 + 1: 5 divides 3^718 + 1 and 33029 + 1 (chain 33029).
theorem kill3_e718 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 718 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g33029 : 33029 ∈ P := S7 33029 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 718 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 118)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 33029 ∣ 1 + 3 ^ 718).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 718 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 118)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 718).trans hd) 33029 g33029 (by norm_num)

-- 3^719 + 1: 5 divides 19 + 1 and 59 + 1 (chains 362377 -> 37 -> 19; 362377 -> 59).
theorem kill3_e719 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 719 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g362377 : 362377 ∈ P := S7 362377 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 719 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 119)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 362377 ∣ 1 + 3 ^ 719).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 362377 g362377 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 362377 g362377 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 59 g59 (by norm_num) (by norm_num)
  omega

-- 3^724 + 1: 5 divides 95569 + 1 and 19 + 1 (chains 95569; 95569 -> 19).
theorem kill3_e724 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 724 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g95569 : 95569 ∈ P := S7 95569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 724 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 124)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 95569 ∣ 1 + 3 ^ 724).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 95569 g95569 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 95569 g95569 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^727 + 1: 7^2 divides 50196146839 + 1 (chain 50196146839).
theorem kill3_e727 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 727 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g50196146839 : 50196146839 ∈ P := S7 50196146839 prime_50196146839 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 727 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 127)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 50196146839 ∣ 1 + 3 ^ 727).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 50196146839 g50196146839 (by norm_num)

-- 3^733 + 1: 5 divides 29 + 1 and 19 + 1 (chains 9913093 -> 4956547 -> 347 -> 29; 9913093 -> 4956547 -> 3571 -> 19).
theorem kill3_e733 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 733 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9913093 : 9913093 ∈ P := S7 9913093 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 733 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 133)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 9913093 ∣ 1 + 3 ^ 733).trans hd)
  have g4956547 : 4956547 ∈ P := S1 4956547 (by norm_num) (by norm_num) (hnz (by norm_num)) 9913093 g9913093 (by norm_num)
  have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 4956547 g4956547 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
  have g3571 : 3571 ∈ P := S1 3571 (by norm_num) (by norm_num) (hnz (by norm_num)) 4956547 g4956547 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 3571 g3571 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 19 g19 (by norm_num) (by norm_num)
  omega

-- 3^734 + 1: 5 divides 3^734 + 1 and 8849 + 1 (chain 318557 -> 53093 -> 8849).
theorem kill3_e734 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 734 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g318557 : 318557 ∈ P := S7 318557 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 734 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 134)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 318557 ∣ 1 + 3 ^ 734).trans hd)
  have g53093 : 53093 ∈ P := S1 53093 (by norm_num) (by norm_num) (hnz (by norm_num)) 318557 g318557 (by norm_num)
  have g8849 : 8849 ∈ P := S1 8849 (by norm_num) (by norm_num) (hnz (by norm_num)) 53093 g53093 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 734 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 134)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 734).trans hd) 8849 g8849 (by norm_num)

-- 3^739 + 1: 37 divides 1258271653 + 1 and 73 + 1 (chains 1258271653; 1258271653 -> 73).
theorem kill3_e739 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 739 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1258271653 : 1258271653 ∈ P := S7 1258271653 prime_1258271653 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 739 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 139)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1258271653 ∣ 1 + 3 ^ 739).trans hd)
  have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 1258271653 g1258271653 (by norm_num)
  have := S3 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1258271653 g1258271653 73 g73 (by norm_num) (by norm_num)
  omega

-- 3^743 + 1: 5^2 divides 149 + 1 (chain 23929028034811 -> 314855632037 -> 11621 -> 149).
theorem kill3_e743 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 743 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23929028034811 : 23929028034811 ∈ P := S7 23929028034811 prime_23929028034811 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 743 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 143)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 23929028034811 ∣ 1 + 3 ^ 743).trans hd)
  have g314855632037 : 314855632037 ∈ P := S1 314855632037 prime_314855632037 (by norm_num) (hnz (by norm_num)) 23929028034811 g23929028034811 (by norm_num)
  have g11621 : 11621 ∈ P := S1 11621 (by norm_num) (by norm_num) (hnz (by norm_num)) 314855632037 g314855632037 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 11621 g11621 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- 3^746 + 1: 5 divides 3^746 + 1 and 1219676228250269 + 1 (chain 1219676228250269).
theorem kill3_e746 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 746 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1219676228250269 : 1219676228250269 ∈ P := S7 1219676228250269 prime_1219676228250269 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 746 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 146)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1219676228250269 ∣ 1 + 3 ^ 746).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 746 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 146)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 746).trans hd) 1219676228250269 g1219676228250269 (by norm_num)

-- 3^751 + 1: 13 divides 1820450411621866648422581981583631 + 1 and 181 + 1 (chains 1820450411621866648422581981583631; 1820450411621866648422581981583631 -> 181).
theorem kill3_e751 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 751 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1820450411621866648422581981583631 : 1820450411621866648422581981583631 ∈ P := S7 1820450411621866648422581981583631 prime_1820450411621866648422581981583631 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 751 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 151)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 1820450411621866648422581981583631 ∣ 1 + 3 ^ 751).trans hd)
  have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 1820450411621866648422581981583631 g1820450411621866648422581981583631 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1820450411621866648422581981583631 g1820450411621866648422581981583631 181 g181 (by norm_num) (by norm_num)
  omega

-- 3^757 + 1: 5 divides 19 + 1 and 1109 + 1 (chains 2099182693095646638569878483 -> 63716651 -> 19; 2099182693095646638569878483 -> 63716651 -> 31051 -> 1109).
theorem kill3_e757 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 757 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2099182693095646638569878483 : 2099182693095646638569878483 ∈ P := S7 2099182693095646638569878483 prime_2099182693095646638569878483 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 757 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 157)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 2099182693095646638569878483 ∣ 1 + 3 ^ 757).trans hd)
  have g63716651 : 63716651 ∈ P := S1 63716651 prime_63716651 (by norm_num) (hnz (by norm_num)) 2099182693095646638569878483 g2099182693095646638569878483 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 63716651 g63716651 (by norm_num)
  have g31051 : 31051 ∈ P := S1 31051 (by norm_num) (by norm_num) (hnz (by norm_num)) 63716651 g63716651 (by norm_num)
  have g1109 : 1109 ∈ P := S1 1109 (by norm_num) (by norm_num) (hnz (by norm_num)) 31051 g31051 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 1109 g1109 (by norm_num) (by norm_num)
  omega

-- 3^758 + 1: 5 divides 3^758 + 1 and 24698220820062044069 + 1 (chain 24698220820062044069).
theorem kill3_e758 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 758 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g24698220820062044069 : 24698220820062044069 ∈ P := S7 24698220820062044069 prime_24698220820062044069 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 758 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 158)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 24698220820062044069 ∣ 1 + 3 ^ 758).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 758 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 158)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 758).trans hd) 24698220820062044069 g24698220820062044069 (by norm_num)

-- 3^761 + 1: 5 divides 82189 + 1 and 8219 + 1 (chains 82189; 82189 -> 8219).
theorem kill3_e761 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 761 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g82189 : 82189 ∈ P := S7 82189 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 761 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 161)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 82189 ∣ 1 + 3 ^ 761).trans hd)
  have g8219 : 8219 ∈ P := S1 8219 (by norm_num) (by norm_num) (hnz (by norm_num)) 82189 g82189 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 82189 g82189 8219 g8219 (by norm_num) (by norm_num)
  omega

-- 3^766 + 1: 5 divides 3^766 + 1 and 89 + 1 (chain 656822133606644237 -> 87041 -> 89).
theorem kill3_e766 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 766 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g656822133606644237 : 656822133606644237 ∈ P := S7 656822133606644237 prime_656822133606644237 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 766 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 166)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 656822133606644237 ∣ 1 + 3 ^ 766).trans hd)
  have g87041 : 87041 ∈ P := S1 87041 (by norm_num) (by norm_num) (hnz (by norm_num)) 656822133606644237 g656822133606644237 (by norm_num)
  have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 87041 g87041 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 766 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 166)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 766).trans hd) 89 g89 (by norm_num)

-- 3^769 + 1: 11 divides 49354941703447993616761 + 1 and 593 + 1 (chains 49354941703447993616761; 49354941703447993616761 -> 2063851371725683433 -> 593).
theorem kill3_e769 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 769 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g49354941703447993616761 : 49354941703447993616761 ∈ P := S7 49354941703447993616761 prime_49354941703447993616761 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 769 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 169)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 49354941703447993616761 ∣ 1 + 3 ^ 769).trans hd)
  have g2063851371725683433 : 2063851371725683433 ∈ P := S1 2063851371725683433 prime_2063851371725683433 (by norm_num) (hnz (by norm_num)) 49354941703447993616761 g49354941703447993616761 (by norm_num)
  have g593 : 593 ∈ P := S1 593 (by norm_num) (by norm_num) (hnz (by norm_num)) 2063851371725683433 g2063851371725683433 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 49354941703447993616761 g49354941703447993616761 593 g593 (by norm_num) (by norm_num)
  omega

-- 3^772 + 1: 7 divides 41 + 1 and 1231 + 1 (chains 41; 443129 -> 14771 -> 1231).
theorem kill3_e772 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 772 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 772 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 172)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 772).trans hd)
  have g443129 : 443129 ∈ P := S7 443129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 772 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 172)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 443129 ∣ 1 + 3 ^ 772).trans hd)
  have g14771 : 14771 ∈ P := S1 14771 (by norm_num) (by norm_num) (hnz (by norm_num)) 443129 g443129 (by norm_num)
  have g1231 : 1231 ∈ P := S1 1231 (by norm_num) (by norm_num) (hnz (by norm_num)) 14771 g14771 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 1231 g1231 (by norm_num) (by norm_num)
  omega

-- 3^773 + 1: 7^2 divides 28909 + 1 (chain 454333843 -> 28909).
theorem kill3_e773 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 773 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g454333843 : 454333843 ∈ P := S7 454333843 prime_454333843 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 773 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 173)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 454333843 ∣ 1 + 3 ^ 773).trans hd)
  have g28909 : 28909 ∈ P := S1 28909 (by norm_num) (by norm_num) (hnz (by norm_num)) 454333843 g454333843 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 28909 g28909 (by norm_num)

-- 3^778 + 1: 5 divides 3^778 + 1 and 29 + 1 (chain 530597 -> 463 -> 29).
theorem kill3_e778 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 778 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g530597 : 530597 ∈ P := S7 530597 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 778 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 178)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 530597 ∣ 1 + 3 ^ 778).trans hd)
  have g463 : 463 ∈ P := S1 463 (by norm_num) (by norm_num) (hnz (by norm_num)) 530597 g530597 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 463 g463 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 778 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 178)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 778).trans hd) 29 g29 (by norm_num)

-- 3^787 + 1: 5^2 divides 599 + 1 (chain 2672085006016195513 -> 4823258133603241 -> 45523 -> 599).
theorem kill3_e787 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 787 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2672085006016195513 : 2672085006016195513 ∈ P := S7 2672085006016195513 prime_2672085006016195513 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 787 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 187)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 2672085006016195513 ∣ 1 + 3 ^ 787).trans hd)
  have g4823258133603241 : 4823258133603241 ∈ P := S1 4823258133603241 prime_4823258133603241 (by norm_num) (hnz (by norm_num)) 2672085006016195513 g2672085006016195513 (by norm_num)
  have g45523 : 45523 ∈ P := S1 45523 (by norm_num) (by norm_num) (hnz (by norm_num)) 4823258133603241 g4823258133603241 (by norm_num)
  have g599 : 599 ∈ P := S1 599 (by norm_num) (by norm_num) (hnz (by norm_num)) 45523 g45523 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 599 g599 (by norm_num)

-- 3^788 + 1: 7 divides 41 + 1 and 13 + 1 (chains 41; 94561 -> 13).
theorem kill3_e788 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 788 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 788 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 188)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 41 ∣ 1 + 3 ^ 788).trans hd)
  have g94561 : 94561 ∈ P := S7 94561 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 788 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 188)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 94561 ∣ 1 + 3 ^ 788).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 94561 g94561 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

-- 3^794 + 1: 5 divides 3^794 + 1 and 29 + 1 (chain 24382153 -> 12191077 -> 29).
theorem kill3_e794 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 794 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g24382153 : 24382153 ∈ P := S7 24382153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 794 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 194)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 24382153 ∣ 1 + 3 ^ 794).trans hd)
  have g12191077 : 12191077 ∈ P := S1 12191077 (by norm_num) (by norm_num) (hnz (by norm_num)) 24382153 g24382153 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 12191077 g12191077 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 794 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 194)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 794).trans hd) 29 g29 (by norm_num)

-- 3^796 + 1: 5^2 divides 439991139649 + 1 (chain 439991139649).
theorem kill3_e796 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 796 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g439991139649 : 439991139649 ∈ P := S7 439991139649 prime_439991139649 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 796 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 196)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 439991139649 ∣ 1 + 3 ^ 796).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 439991139649 g439991139649 (by norm_num)

-- 3^797 + 1: 7^2 divides 23911 + 1 (chain 23911).
theorem kill3_e797 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 797 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23911 : 23911 ∈ P := S7 23911 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 797 = 3 ^ 200 * (3 ^ 200 * (3 ^ 200 * 3 ^ 197)) by rw [← pow_add, ← pow_add, ← pow_add]]; norm_num : 23911 ∣ 1 + 3 ^ 797).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 23911 g23911 (by norm_num)

-- kernel 3^e: the new excluded classes (500 < d <= 800)
theorem core3_residues_800 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    e % 1004 ≠ 502 ∧
      e % 1006 ≠ 503 ∧
      e % 1016 ≠ 508 ∧
      e % 1018 ≠ 509 ∧
      e % 1024 ≠ 512 ∧
      e % 1028 ≠ 514 ∧
      e % 1042 ≠ 521 ∧
      e % 1046 ≠ 523 ∧
      e % 1048 ≠ 524 ∧
      e % 1052 ≠ 526 ∧
      e % 1076 ≠ 538 ∧
      e % 1082 ≠ 541 ∧
      e % 1084 ≠ 542 ∧
      e % 1094 ≠ 547 ∧
      e % 1096 ≠ 548 ∧
      e % 1108 ≠ 554 ∧
      e % 1112 ≠ 556 ∧
      e % 1114 ≠ 557 ∧
      e % 1124 ≠ 562 ∧
      e % 1126 ≠ 563 ∧
      e % 1132 ≠ 566 ∧
      e % 1138 ≠ 569 ∧
      e % 1142 ≠ 571 ∧
      e % 1172 ≠ 586 ∧
      e % 1174 ≠ 587 ∧
      e % 1186 ≠ 593 ∧
      e % 1192 ≠ 596 ∧
      e % 1198 ≠ 599 ∧
      e % 1202 ≠ 601 ∧
      e % 1208 ≠ 604 ∧
      e % 1214 ≠ 607 ∧
      e % 1226 ≠ 613 ∧
      e % 1228 ≠ 614 ∧
      e % 1234 ≠ 617 ∧
      e % 1238 ≠ 619 ∧
      e % 1244 ≠ 622 ∧
      e % 1252 ≠ 626 ∧
      e % 1256 ≠ 628 ∧
      e % 1262 ≠ 631 ∧
      e % 1268 ≠ 634 ∧
      e % 1282 ≠ 641 ∧
      e % 1286 ≠ 643 ∧
      e % 1294 ≠ 647 ∧
      e % 1304 ≠ 652 ∧
      e % 1306 ≠ 653 ∧
      e % 1318 ≠ 659 ∧
      e % 1322 ≠ 661 ∧
      e % 1324 ≠ 662 ∧
      e % 1336 ≠ 668 ∧
      e % 1346 ≠ 673 ∧
      e % 1348 ≠ 674 ∧
      e % 1354 ≠ 677 ∧
      e % 1366 ≠ 683 ∧
      e % 1382 ≠ 691 ∧
      e % 1384 ≠ 692 ∧
      e % 1388 ≠ 694 ∧
      e % 1396 ≠ 698 ∧
      e % 1402 ≠ 701 ∧
      e % 1412 ≠ 706 ∧
      e % 1418 ≠ 709 ∧
      e % 1432 ≠ 716 ∧
      e % 1436 ≠ 718 ∧
      e % 1438 ≠ 719 ∧
      e % 1448 ≠ 724 ∧
      e % 1454 ≠ 727 ∧
      e % 1466 ≠ 733 ∧
      e % 1468 ≠ 734 ∧
      e % 1478 ≠ 739 ∧
      e % 1486 ≠ 743 ∧
      e % 1492 ≠ 746 ∧
      e % 1502 ≠ 751 ∧
      e % 1514 ≠ 757 ∧
      e % 1516 ≠ 758 ∧
      e % 1522 ≠ 761 ∧
      e % 1532 ≠ 766 ∧
      e % 1538 ≠ 769 ∧
      e % 1544 ≠ 772 ∧
      e % 1546 ≠ 773 ∧
      e % 1556 ≠ 778 ∧
      e % 1574 ≠ 787 ∧
      e % 1576 ≠ 788 ∧
      e % 1588 ≠ 794 ∧
      e % 1592 ≠ 796 ∧
      e % 1594 ≠ 797 :=
  ⟨fun h => kill3_e502 hP E (one_add_pow_dvd_of_odd_mul (e0 := 502) (by omega)),
   fun h => kill3_e503 hP E (one_add_pow_dvd_of_odd_mul (e0 := 503) (by omega)),
   fun h => kill3_e508 hP E (one_add_pow_dvd_of_odd_mul (e0 := 508) (by omega)),
   fun h => kill3_e509 hP E (one_add_pow_dvd_of_odd_mul (e0 := 509) (by omega)),
   fun h => kill3_e512 hP E (one_add_pow_dvd_of_odd_mul (e0 := 512) (by omega)),
   fun h => kill3_e514 hP E (one_add_pow_dvd_of_odd_mul (e0 := 514) (by omega)),
   fun h => kill3_e521 hP E (one_add_pow_dvd_of_odd_mul (e0 := 521) (by omega)),
   fun h => kill3_e523 hP E (one_add_pow_dvd_of_odd_mul (e0 := 523) (by omega)),
   fun h => kill3_e524 hP E (one_add_pow_dvd_of_odd_mul (e0 := 524) (by omega)),
   fun h => kill3_e526 hP E (one_add_pow_dvd_of_odd_mul (e0 := 526) (by omega)),
   fun h => kill3_e538 hP E (one_add_pow_dvd_of_odd_mul (e0 := 538) (by omega)),
   fun h => kill3_e541 hP E (one_add_pow_dvd_of_odd_mul (e0 := 541) (by omega)),
   fun h => kill3_e542 hP E (one_add_pow_dvd_of_odd_mul (e0 := 542) (by omega)),
   fun h => kill3_e547 hP E (one_add_pow_dvd_of_odd_mul (e0 := 547) (by omega)),
   fun h => kill3_e548 hP E (one_add_pow_dvd_of_odd_mul (e0 := 548) (by omega)),
   fun h => kill3_e554 hP E (one_add_pow_dvd_of_odd_mul (e0 := 554) (by omega)),
   fun h => kill3_e556 hP E (one_add_pow_dvd_of_odd_mul (e0 := 556) (by omega)),
   fun h => kill3_e557 hP E (one_add_pow_dvd_of_odd_mul (e0 := 557) (by omega)),
   fun h => kill3_e562 hP E (one_add_pow_dvd_of_odd_mul (e0 := 562) (by omega)),
   fun h => kill3_e563 hP E (one_add_pow_dvd_of_odd_mul (e0 := 563) (by omega)),
   fun h => kill3_e566 hP E (one_add_pow_dvd_of_odd_mul (e0 := 566) (by omega)),
   fun h => kill3_e569 hP E (one_add_pow_dvd_of_odd_mul (e0 := 569) (by omega)),
   fun h => kill3_e571 hP E (one_add_pow_dvd_of_odd_mul (e0 := 571) (by omega)),
   fun h => kill3_e586 hP E (one_add_pow_dvd_of_odd_mul (e0 := 586) (by omega)),
   fun h => kill3_e587 hP E (one_add_pow_dvd_of_odd_mul (e0 := 587) (by omega)),
   fun h => kill3_e593 hP E (one_add_pow_dvd_of_odd_mul (e0 := 593) (by omega)),
   fun h => kill3_e596 hP E (one_add_pow_dvd_of_odd_mul (e0 := 596) (by omega)),
   fun h => kill3_e599 hP E (one_add_pow_dvd_of_odd_mul (e0 := 599) (by omega)),
   fun h => kill3_e601 hP E (one_add_pow_dvd_of_odd_mul (e0 := 601) (by omega)),
   fun h => kill3_e604 hP E (one_add_pow_dvd_of_odd_mul (e0 := 604) (by omega)),
   fun h => kill3_e607 hP E (one_add_pow_dvd_of_odd_mul (e0 := 607) (by omega)),
   fun h => kill3_e613 hP E (one_add_pow_dvd_of_odd_mul (e0 := 613) (by omega)),
   fun h => kill3_e614 hP E (one_add_pow_dvd_of_odd_mul (e0 := 614) (by omega)),
   fun h => kill3_e617 hP E (one_add_pow_dvd_of_odd_mul (e0 := 617) (by omega)),
   fun h => kill3_e619 hP E (one_add_pow_dvd_of_odd_mul (e0 := 619) (by omega)),
   fun h => kill3_e622 hP E (one_add_pow_dvd_of_odd_mul (e0 := 622) (by omega)),
   fun h => kill3_e626 hP E (one_add_pow_dvd_of_odd_mul (e0 := 626) (by omega)),
   fun h => kill3_e628 hP E (one_add_pow_dvd_of_odd_mul (e0 := 628) (by omega)),
   fun h => kill3_e631 hP E (one_add_pow_dvd_of_odd_mul (e0 := 631) (by omega)),
   fun h => kill3_e634 hP E (one_add_pow_dvd_of_odd_mul (e0 := 634) (by omega)),
   fun h => kill3_e641 hP E (one_add_pow_dvd_of_odd_mul (e0 := 641) (by omega)),
   fun h => kill3_e643 hP E (one_add_pow_dvd_of_odd_mul (e0 := 643) (by omega)),
   fun h => kill3_e647 hP E (one_add_pow_dvd_of_odd_mul (e0 := 647) (by omega)),
   fun h => kill3_e652 hP E (one_add_pow_dvd_of_odd_mul (e0 := 652) (by omega)),
   fun h => kill3_e653 hP E (one_add_pow_dvd_of_odd_mul (e0 := 653) (by omega)),
   fun h => kill3_e659 hP E (one_add_pow_dvd_of_odd_mul (e0 := 659) (by omega)),
   fun h => kill3_e661 hP E (one_add_pow_dvd_of_odd_mul (e0 := 661) (by omega)),
   fun h => kill3_e662 hP E (one_add_pow_dvd_of_odd_mul (e0 := 662) (by omega)),
   fun h => kill3_e668 hP E (one_add_pow_dvd_of_odd_mul (e0 := 668) (by omega)),
   fun h => kill3_e673 hP E (one_add_pow_dvd_of_odd_mul (e0 := 673) (by omega)),
   fun h => kill3_e674 hP E (one_add_pow_dvd_of_odd_mul (e0 := 674) (by omega)),
   fun h => kill3_e677 hP E (one_add_pow_dvd_of_odd_mul (e0 := 677) (by omega)),
   fun h => kill3_e683 hP E (one_add_pow_dvd_of_odd_mul (e0 := 683) (by omega)),
   fun h => kill3_e691 hP E (one_add_pow_dvd_of_odd_mul (e0 := 691) (by omega)),
   fun h => kill3_e692 hP E (one_add_pow_dvd_of_odd_mul (e0 := 692) (by omega)),
   fun h => kill3_e694 hP E (one_add_pow_dvd_of_odd_mul (e0 := 694) (by omega)),
   fun h => kill3_e698 hP E (one_add_pow_dvd_of_odd_mul (e0 := 698) (by omega)),
   fun h => kill3_e701 hP E (one_add_pow_dvd_of_odd_mul (e0 := 701) (by omega)),
   fun h => kill3_e706 hP E (one_add_pow_dvd_of_odd_mul (e0 := 706) (by omega)),
   fun h => kill3_e709 hP E (one_add_pow_dvd_of_odd_mul (e0 := 709) (by omega)),
   fun h => kill3_e716 hP E (one_add_pow_dvd_of_odd_mul (e0 := 716) (by omega)),
   fun h => kill3_e718 hP E (one_add_pow_dvd_of_odd_mul (e0 := 718) (by omega)),
   fun h => kill3_e719 hP E (one_add_pow_dvd_of_odd_mul (e0 := 719) (by omega)),
   fun h => kill3_e724 hP E (one_add_pow_dvd_of_odd_mul (e0 := 724) (by omega)),
   fun h => kill3_e727 hP E (one_add_pow_dvd_of_odd_mul (e0 := 727) (by omega)),
   fun h => kill3_e733 hP E (one_add_pow_dvd_of_odd_mul (e0 := 733) (by omega)),
   fun h => kill3_e734 hP E (one_add_pow_dvd_of_odd_mul (e0 := 734) (by omega)),
   fun h => kill3_e739 hP E (one_add_pow_dvd_of_odd_mul (e0 := 739) (by omega)),
   fun h => kill3_e743 hP E (one_add_pow_dvd_of_odd_mul (e0 := 743) (by omega)),
   fun h => kill3_e746 hP E (one_add_pow_dvd_of_odd_mul (e0 := 746) (by omega)),
   fun h => kill3_e751 hP E (one_add_pow_dvd_of_odd_mul (e0 := 751) (by omega)),
   fun h => kill3_e757 hP E (one_add_pow_dvd_of_odd_mul (e0 := 757) (by omega)),
   fun h => kill3_e758 hP E (one_add_pow_dvd_of_odd_mul (e0 := 758) (by omega)),
   fun h => kill3_e761 hP E (one_add_pow_dvd_of_odd_mul (e0 := 761) (by omega)),
   fun h => kill3_e766 hP E (one_add_pow_dvd_of_odd_mul (e0 := 766) (by omega)),
   fun h => kill3_e769 hP E (one_add_pow_dvd_of_odd_mul (e0 := 769) (by omega)),
   fun h => kill3_e772 hP E (one_add_pow_dvd_of_odd_mul (e0 := 772) (by omega)),
   fun h => kill3_e773 hP E (one_add_pow_dvd_of_odd_mul (e0 := 773) (by omega)),
   fun h => kill3_e778 hP E (one_add_pow_dvd_of_odd_mul (e0 := 778) (by omega)),
   fun h => kill3_e787 hP E (one_add_pow_dvd_of_odd_mul (e0 := 787) (by omega)),
   fun h => kill3_e788 hP E (one_add_pow_dvd_of_odd_mul (e0 := 788) (by omega)),
   fun h => kill3_e794 hP E (one_add_pow_dvd_of_odd_mul (e0 := 794) (by omega)),
   fun h => kill3_e796 hP E (one_add_pow_dvd_of_odd_mul (e0 := 796) (by omega)),
   fun h => kill3_e797 hP E (one_add_pow_dvd_of_odd_mul (e0 := 797) (by omega))⟩

-- Pure arithmetic: the exponents in 501..800 that avoid all excluded classes.
set_option maxHeartbeats 4000000 in
theorem exponent_sieve_800 (e : ℕ) (lo : 500 < e) (hi : e ≤ 800)
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
      e % 982 ≠ 491)
    (h2 : e % 1004 ≠ 502 ∧
      e % 1006 ≠ 503 ∧
      e % 1016 ≠ 508 ∧
      e % 1018 ≠ 509 ∧
      e % 1024 ≠ 512 ∧
      e % 1028 ≠ 514 ∧
      e % 1042 ≠ 521 ∧
      e % 1046 ≠ 523 ∧
      e % 1048 ≠ 524 ∧
      e % 1052 ≠ 526 ∧
      e % 1076 ≠ 538 ∧
      e % 1082 ≠ 541 ∧
      e % 1084 ≠ 542 ∧
      e % 1094 ≠ 547 ∧
      e % 1096 ≠ 548 ∧
      e % 1108 ≠ 554 ∧
      e % 1112 ≠ 556 ∧
      e % 1114 ≠ 557 ∧
      e % 1124 ≠ 562 ∧
      e % 1126 ≠ 563 ∧
      e % 1132 ≠ 566 ∧
      e % 1138 ≠ 569 ∧
      e % 1142 ≠ 571 ∧
      e % 1172 ≠ 586 ∧
      e % 1174 ≠ 587 ∧
      e % 1186 ≠ 593 ∧
      e % 1192 ≠ 596 ∧
      e % 1198 ≠ 599 ∧
      e % 1202 ≠ 601 ∧
      e % 1208 ≠ 604 ∧
      e % 1214 ≠ 607 ∧
      e % 1226 ≠ 613 ∧
      e % 1228 ≠ 614 ∧
      e % 1234 ≠ 617 ∧
      e % 1238 ≠ 619 ∧
      e % 1244 ≠ 622 ∧
      e % 1252 ≠ 626 ∧
      e % 1256 ≠ 628 ∧
      e % 1262 ≠ 631 ∧
      e % 1268 ≠ 634 ∧
      e % 1282 ≠ 641 ∧
      e % 1286 ≠ 643 ∧
      e % 1294 ≠ 647 ∧
      e % 1304 ≠ 652 ∧
      e % 1306 ≠ 653 ∧
      e % 1318 ≠ 659 ∧
      e % 1322 ≠ 661 ∧
      e % 1324 ≠ 662 ∧
      e % 1336 ≠ 668 ∧
      e % 1346 ≠ 673 ∧
      e % 1348 ≠ 674 ∧
      e % 1354 ≠ 677 ∧
      e % 1366 ≠ 683 ∧
      e % 1382 ≠ 691 ∧
      e % 1384 ≠ 692 ∧
      e % 1388 ≠ 694 ∧
      e % 1396 ≠ 698 ∧
      e % 1402 ≠ 701 ∧
      e % 1412 ≠ 706 ∧
      e % 1418 ≠ 709 ∧
      e % 1432 ≠ 716 ∧
      e % 1436 ≠ 718 ∧
      e % 1438 ≠ 719 ∧
      e % 1448 ≠ 724 ∧
      e % 1454 ≠ 727 ∧
      e % 1466 ≠ 733 ∧
      e % 1468 ≠ 734 ∧
      e % 1478 ≠ 739 ∧
      e % 1486 ≠ 743 ∧
      e % 1492 ≠ 746 ∧
      e % 1502 ≠ 751 ∧
      e % 1514 ≠ 757 ∧
      e % 1516 ≠ 758 ∧
      e % 1522 ≠ 761 ∧
      e % 1532 ≠ 766 ∧
      e % 1538 ≠ 769 ∧
      e % 1544 ≠ 772 ∧
      e % 1546 ≠ 773 ∧
      e % 1556 ≠ 778 ∧
      e % 1574 ≠ 787 ∧
      e % 1576 ≠ 788 ∧
      e % 1588 ≠ 794 ∧
      e % 1592 ≠ 796 ∧
      e % 1594 ≠ 797) :
    e = 577 ∨ e = 764 := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99⟩ := h0
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52, s53, s54, s55, s56, s57, s58, s59, s60, s61, s62, s63, s64, s65, s66, s67, s68, s69, s70, s71, s72, s73, s74, s75, s76, s77, s78, s79, s80, s81, s82, s83, s84, s85, s86, s87, s88, s89⟩ := h1
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, t81, t82, t83⟩ := h2
  interval_cases e
  · exact absurd rfl r87
  · exact absurd rfl t0
  · exact absurd rfl t1
  · exact absurd rfl r1
  · exact absurd rfl r58
  · exact absurd rfl r11
  · exact absurd rfl r24
  · exact absurd rfl t2
  · exact absurd rfl t3
  · exact absurd rfl r0
  · exact absurd rfl r44
  · exact absurd rfl t4
  · exact absurd rfl r2
  · exact absurd rfl t5
  · exact absurd rfl r59
  · exact absurd rfl r4
  · exact absurd rfl r29
  · exact absurd rfl r5
  · exact absurd rfl r90
  · exact absurd rfl r1
  · exact absurd rfl t6
  · exact absurd rfl r0
  · exact absurd rfl t7
  · exact absurd rfl t8
  · exact absurd rfl r6
  · exact absurd rfl t9
  · exact absurd rfl r8
  · exact absurd rfl r7
  · exact absurd rfl r12
  · exact absurd rfl r3
  · exact absurd rfl r2
  · exact absurd rfl r15
  · exact absurd rfl r25
  · exact absurd rfl r0
  · exact absurd rfl r61
  · exact absurd rfl r1
  · exact absurd rfl r92
  · exact absurd rfl t10
  · exact absurd rfl r30
  · exact absurd rfl r4
  · exact absurd rfl t11
  · exact absurd rfl t12
  · exact absurd rfl r93
  · exact absurd rfl r18
  · exact absurd rfl r62
  · exact absurd rfl r0
  · exact absurd rfl t13
  · exact absurd rfl t14
  · exact absurd rfl r2
  · exact absurd rfl r3
  · exact absurd rfl r16
  · exact absurd rfl r1
  · exact absurd rfl r48
  · exact absurd rfl t15
  · exact absurd rfl r6
  · exact absurd rfl t16
  · exact absurd rfl t17
  · exact absurd rfl r0
  · exact absurd rfl r26
  · exact absurd rfl r7
  · exact absurd rfl r8
  · exact absurd rfl t18
  · exact absurd rfl t19
  · exact absurd rfl r4
  · exact absurd rfl r63
  · exact absurd rfl t20
  · exact absurd rfl r2
  · exact absurd rfl r1
  · exact absurd rfl t21
  · exact absurd rfl r0
  · exact absurd rfl t22
  · exact absurd rfl r27
  · exact absurd rfl r95
  · exact absurd rfl r5
  · exact absurd rfl r12
  · exact absurd rfl r39
  · omega
  · exact absurd rfl r20
  · exact absurd rfl r96
  · exact absurd rfl r9
  · exact absurd rfl r50
  · exact absurd rfl r0
  · exact absurd rfl r32
  · exact absurd rfl r1
  · exact absurd rfl r2
  · exact absurd rfl t23
  · exact absurd rfl t24
  · exact absurd rfl r4
  · exact absurd rfl r17
  · exact absurd rfl r3
  · exact absurd rfl r98
  · exact absurd rfl r7
  · exact absurd rfl t25
  · exact absurd rfl r0
  · exact absurd rfl r8
  · exact absurd rfl t26
  · exact absurd rfl r99
  · exact absurd rfl r14
  · exact absurd rfl t27
  · exact absurd rfl r1
  · exact absurd rfl t28
  · exact absurd rfl r5
  · exact absurd rfl r2
  · exact absurd rfl t29
  · exact absurd rfl r33
  · exact absurd rfl r0
  · exact absurd rfl t30
  · exact absurd rfl r18
  · exact absurd rfl r10
  · exact absurd rfl r3
  · exact absurd rfl r29
  · exact absurd rfl r4
  · exact absurd rfl t31
  · exact absurd rfl t32
  · exact absurd rfl r6
  · exact absurd rfl r1
  · exact absurd rfl t33
  · exact absurd rfl r0
  · exact absurd rfl t34
  · exact absurd rfl r9
  · exact absurd rfl r2
  · exact absurd rfl t35
  · exact absurd rfl r52
  · exact absurd rfl r7
  · exact absurd rfl r13
  · exact absurd rfl t36
  · exact absurd rfl r19
  · exact absurd rfl t37
  · exact absurd rfl r8
  · exact absurd rfl r0
  · exact absurd rfl t38
  · exact absurd rfl r1
  · exact absurd rfl s3
  · exact absurd rfl t39
  · exact absurd rfl r69
  · exact absurd rfl r4
  · exact absurd rfl r30
  · exact absurd rfl r11
  · exact absurd rfl r2
  · exact absurd rfl r70
  · exact absurd rfl t40
  · exact absurd rfl r0
  · exact absurd rfl t41
  · exact absurd rfl r15
  · exact absurd rfl r6
  · exact absurd rfl r20
  · exact absurd rfl t42
  · exact absurd rfl r1
  · exact absurd rfl r36
  · exact absurd rfl r3
  · exact absurd rfl r10
  · exact absurd rfl t43
  · exact absurd rfl t44
  · exact absurd rfl r0
  · exact absurd rfl r71
  · exact absurd rfl r7
  · exact absurd rfl r2
  · exact absurd rfl r5
  · exact absurd rfl t45
  · exact absurd rfl r4
  · exact absurd rfl t46
  · exact absurd rfl t47
  · exact absurd rfl r8
  · exact absurd rfl r1
  · exact absurd rfl r21
  · exact absurd rfl r0
  · exact absurd rfl r12
  · exact absurd rfl t48
  · exact absurd rfl s7
  · exact absurd rfl r3
  · exact absurd rfl r37
  · exact absurd rfl r18
  · exact absurd rfl t49
  · exact absurd rfl t50
  · exact absurd rfl r2
  · exact absurd rfl r31
  · exact absurd rfl t51
  · exact absurd rfl r0
  · exact absurd rfl r57
  · exact absurd rfl r1
  · exact absurd rfl s9
  · exact absurd rfl r11
  · exact absurd rfl t52
  · exact absurd rfl r4
  · exact absurd rfl r74
  · exact absurd rfl r5
  · exact absurd rfl s10
  · exact absurd rfl r7
  · exact absurd rfl r32
  · exact absurd rfl r0
  · exact absurd rfl t53
  · exact absurd rfl t54
  · exact absurd rfl r2
  · exact absurd rfl t55
  · exact absurd rfl r75
  · exact absurd rfl r1
  · exact absurd rfl r8
  · exact absurd rfl t56
  · exact absurd rfl s11
  · exact absurd rfl r9
  · exact absurd rfl t57
  · exact absurd rfl r0
  · exact absurd rfl r22
  · exact absurd rfl r39
  · exact absurd rfl r6
  · exact absurd rfl t58
  · exact absurd rfl r58
  · exact absurd rfl r4
  · exact absurd rfl t59
  · exact absurd rfl r3
  · exact absurd rfl r2
  · exact absurd rfl r1
  · exact absurd rfl r12
  · exact absurd rfl r0
  · exact absurd rfl r33
  · exact absurd rfl t60
  · exact absurd rfl s13
  · exact absurd rfl t61
  · exact absurd rfl t62
  · exact absurd rfl r7
  · exact absurd rfl r59
  · exact absurd rfl r23
  · exact absurd rfl s14
  · exact absurd rfl t63
  · exact absurd rfl r13
  · exact absurd rfl r0
  · exact absurd rfl t64
  · exact absurd rfl r1
  · exact absurd rfl r2
  · exact absurd rfl r3
  · exact absurd rfl r8
  · exact absurd rfl r4
  · exact absurd rfl t65
  · exact absurd rfl t66
  · exact absurd rfl r6
  · exact absurd rfl r18
  · exact absurd rfl r41
  · exact absurd rfl r0
  · exact absurd rfl t67
  · exact absurd rfl r9
  · exact absurd rfl r24
  · exact absurd rfl r5
  · exact absurd rfl t68
  · exact absurd rfl r1
  · exact absurd rfl r80
  · exact absurd rfl t69
  · exact absurd rfl r2
  · exact absurd rfl r27
  · exact absurd rfl r61
  · exact absurd rfl r0
  · exact absurd rfl t70
  · exact absurd rfl r7
  · exact absurd rfl s17
  · exact absurd rfl r14
  · exact absurd rfl r81
  · exact absurd rfl r4
  · exact absurd rfl t71
  · exact absurd rfl t72
  · exact absurd rfl r12
  · exact absurd rfl r1
  · exact absurd rfl t73
  · exact absurd rfl r0
  · exact absurd rfl r62
  · omega
  · exact absurd rfl r2
  · exact absurd rfl t74
  · exact absurd rfl r36
  · exact absurd rfl s19
  · exact absurd rfl t75
  · exact absurd rfl r3
  · exact absurd rfl s20
  · exact absurd rfl t76
  · exact absurd rfl t77
  · exact absurd rfl r0
  · exact absurd rfl r13
  · exact absurd rfl r1
  · exact absurd rfl r10
  · exact absurd rfl t78
  · exact absurd rfl r25
  · exact absurd rfl r4
  · exact absurd rfl r43
  · exact absurd rfl r20
  · exact absurd rfl r2
  · exact absurd rfl r7
  · exact absurd rfl r82
  · exact absurd rfl r0
  · exact absurd rfl t79
  · exact absurd rfl t80
  · exact absurd rfl s22
  · exact absurd rfl r3
  · exact absurd rfl r63
  · exact absurd rfl r1
  · exact absurd rfl r37
  · exact absurd rfl t81
  · exact absurd rfl r6
  · exact absurd rfl t82
  · exact absurd rfl t83
  · exact absurd rfl r0
  · exact absurd rfl r8
  · exact absurd rfl r18

-- Pure arithmetic: the new classes in the set form of H1.
set_option maxRecDepth 100000 in
theorem odd_mul_three_800 {e : ℕ}
    (h2 : e % 1004 ≠ 502 ∧
      e % 1006 ≠ 503 ∧
      e % 1016 ≠ 508 ∧
      e % 1018 ≠ 509 ∧
      e % 1024 ≠ 512 ∧
      e % 1028 ≠ 514 ∧
      e % 1042 ≠ 521 ∧
      e % 1046 ≠ 523 ∧
      e % 1048 ≠ 524 ∧
      e % 1052 ≠ 526 ∧
      e % 1076 ≠ 538 ∧
      e % 1082 ≠ 541 ∧
      e % 1084 ≠ 542 ∧
      e % 1094 ≠ 547 ∧
      e % 1096 ≠ 548 ∧
      e % 1108 ≠ 554 ∧
      e % 1112 ≠ 556 ∧
      e % 1114 ≠ 557 ∧
      e % 1124 ≠ 562 ∧
      e % 1126 ≠ 563 ∧
      e % 1132 ≠ 566 ∧
      e % 1138 ≠ 569 ∧
      e % 1142 ≠ 571 ∧
      e % 1172 ≠ 586 ∧
      e % 1174 ≠ 587 ∧
      e % 1186 ≠ 593 ∧
      e % 1192 ≠ 596 ∧
      e % 1198 ≠ 599 ∧
      e % 1202 ≠ 601 ∧
      e % 1208 ≠ 604 ∧
      e % 1214 ≠ 607 ∧
      e % 1226 ≠ 613 ∧
      e % 1228 ≠ 614 ∧
      e % 1234 ≠ 617 ∧
      e % 1238 ≠ 619 ∧
      e % 1244 ≠ 622 ∧
      e % 1252 ≠ 626 ∧
      e % 1256 ≠ 628 ∧
      e % 1262 ≠ 631 ∧
      e % 1268 ≠ 634 ∧
      e % 1282 ≠ 641 ∧
      e % 1286 ≠ 643 ∧
      e % 1294 ≠ 647 ∧
      e % 1304 ≠ 652 ∧
      e % 1306 ≠ 653 ∧
      e % 1318 ≠ 659 ∧
      e % 1322 ≠ 661 ∧
      e % 1324 ≠ 662 ∧
      e % 1336 ≠ 668 ∧
      e % 1346 ≠ 673 ∧
      e % 1348 ≠ 674 ∧
      e % 1354 ≠ 677 ∧
      e % 1366 ≠ 683 ∧
      e % 1382 ≠ 691 ∧
      e % 1384 ≠ 692 ∧
      e % 1388 ≠ 694 ∧
      e % 1396 ≠ 698 ∧
      e % 1402 ≠ 701 ∧
      e % 1412 ≠ 706 ∧
      e % 1418 ≠ 709 ∧
      e % 1432 ≠ 716 ∧
      e % 1436 ≠ 718 ∧
      e % 1438 ≠ 719 ∧
      e % 1448 ≠ 724 ∧
      e % 1454 ≠ 727 ∧
      e % 1466 ≠ 733 ∧
      e % 1468 ≠ 734 ∧
      e % 1478 ≠ 739 ∧
      e % 1486 ≠ 743 ∧
      e % 1492 ≠ 746 ∧
      e % 1502 ≠ 751 ∧
      e % 1514 ≠ 757 ∧
      e % 1516 ≠ 758 ∧
      e % 1522 ≠ 761 ∧
      e % 1532 ≠ 766 ∧
      e % 1538 ≠ 769 ∧
      e % 1544 ≠ 772 ∧
      e % 1546 ≠ 773 ∧
      e % 1556 ≠ 778 ∧
      e % 1574 ≠ 787 ∧
      e % 1576 ≠ 788 ∧
      e % 1588 ≠ 794 ∧
      e % 1592 ≠ 796 ∧
      e % 1594 ≠ 797) :
    ∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, t81, t82, t83⟩ := h2
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1.H1 := by
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
  have r2 := core3_residues_800 hP E
  rcases Nat.lt_or_ge 800 (n.factorization 3) with hb | hle
  · exact (h1 n h hiff hb (odd_mul_three_800 r2) hG).trans (le_max_left _ _)
  · exact (h2 n h hiff (exponent_sieve_800 _ hbig hle r0 r1 r2) hG).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1
