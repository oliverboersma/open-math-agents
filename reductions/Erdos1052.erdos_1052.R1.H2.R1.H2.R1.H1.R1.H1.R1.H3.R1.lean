import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H3.R1
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1 in three.  Proving all three H
-- proves the step.
--
-- As in the parent files: n unitary perfect, a = padicValNat 2 n, S = the set of odd primes p with
-- p^2 | n (the kernel), a prime of n is SIMPLE if it divides n exactly once, and
-- Y = the product over S of (1 + 5/z).  The step is the thick part of the family:
-- 223, 991, 1783 | n, a >= 48, no prime of n below 1899 other than 2, 3, 5, 7, 19, 31, 223, 991, 1783,
-- and Y > 2501/2500.
--
-- What is proved here (theorem thick_split):
--   (1) the kernel has at least two primes;
--   (2) if a = 16 mod 32 then 65537^2 | n (2^16 + 1 = 65537 divides 2^a + 1 and cannot be simple,
--       because 11 | 65538 and 11 does not divide n);
--   (3) if a = 64 mod 128 then 274177^2 | n or 137089^2 | n (274177 divides 2^64 + 1; if it were
--       simple then 137089 | 274178 would divide n, and 137089 cannot be simple because 5 | 137090 and
--       the only simple prime p with 5 | p + 1 is 19).
-- Proof of (1): a single kernel prime z divides 2^a + 1, is 2 mod 3 and, by Y > 5001/5000, is below
-- 25000.  By (2) the case a = 16 mod 32 is out, so 64 | a, the order of 2 mod z is divisible by 128, and
-- z = 257 mod 384: one of 19 primes.  For 11 of them no a with 64 | a has z | 2^a + 1; for five
-- (3329, 7937, 11777, 14081, 23297) a = 64 mod 128 and (3) gives a contradiction; for 13313, 17921, 19457
-- the class of a mod the order forces the root 39937, 10753, 136193 of 2^a + 1, whose successor is
-- divisible by 1051, 283, 3 (primes that do not divide n, or a second parent of 3).
-- Since the family has 16 | a and a not 32 mod 64, there are three cases: a = 16 mod 32 (H1),
-- a = 64 mod 128 (H2), 128 | a (H3).
-- The sub-namespace Erdos1052C17 holds the helper theorems.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

namespace Erdos1052C17

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7

-- If B^o = 1 mod z then z | B^m + 1 only depends on m mod o.
theorem pow_mod_class {z B o m : ℕ} (hB : B ^ o % z = 1 % z) (hd : z ∣ B ^ m + 1) :
    z ∣ B ^ (m % o) + 1 := by
  have h1 : B ^ m ≡ B ^ (m % o) [MOD z] := by
    have h2 : (B ^ o) ^ (m / o) ≡ 1 ^ (m / o) [MOD z] := Nat.ModEq.pow _ hB
    have h3 := h2.mul_right (B ^ (m % o))
    rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at h3
    exact h3
  exact ((h1.add_right 1).dvd_iff dvd_rfl).mp hd

theorem neg_one_of_dvd {z a : ℕ} (hd : z ∣ 2 ^ a + 1) : (2 : ZMod z) ^ a = -1 := by
  have h0 : ((2 ^ a + 1 : ℕ) : ZMod z) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem neg_one_ne_one {z : ℕ} (hz : 2 < z) : (-1 : ZMod z) ≠ 1 := by
  intro h
  have e5 : (2 : ZMod z) = 0 := by linear_combination -h
  have h2 : ((2 : ℕ) : ZMod z) = 0 := by exact_mod_cast e5
  have h3 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 z).mp h2)
  omega

-- If 2^(c t) = 1 mod z with t odd, then z does not divide 2^a + 1 for any multiple a of c.
theorem no_div {z a c t : ℕ} (hz : 2 < z) (ht : Odd t) (h1 : (2 ^ c) ^ t % z = 1) (hc : c ∣ a)
    (hd : z ∣ 2 ^ a + 1) : False := by
  obtain ⟨k, rfl⟩ := hc
  have e1 := neg_one_of_dvd hd
  have e2 : ((2 : ZMod z) ^ c) ^ t = 1 := by
    have h0 : (((2 ^ c) ^ t : ℕ) : ZMod z) = ((1 : ℕ) : ZMod z) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    push_cast at h0
    exact h0
  have e3 : ((2 : ZMod z) ^ (c * k)) ^ t = -1 := by rw [e1, ht.neg_one_pow]
  have e4 : ((2 : ZMod z) ^ (c * k)) ^ t = 1 := by
    rw [← pow_mul, mul_right_comm, pow_mul, pow_mul, e2, one_pow]
  exact neg_one_ne_one hz (e3.symm.trans e4)

-- A prime z dividing 2^a + 1 with 64 | a is 1 mod 128 (the order of 2^(a/64) mod z is 128).
theorem mod128 {z a : ℕ} (hzp : z.Prime) (hz : 2 < z) (h64 : 64 ∣ a) (hd : z ∣ 2 ^ a + 1) :
    z % 128 = 1 := by
  have hf : Fact z.Prime := ⟨hzp⟩
  obtain ⟨m, rfl⟩ := h64
  have e1 := neg_one_of_dvd hd
  have hx64 : ((2 : ZMod z) ^ m) ^ 64 = -1 := by rw [← pow_mul, mul_comm]; exact e1
  have hord : orderOf ((2 : ZMod z) ^ m) = 2 ^ (6 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 6)
      (by rw [show (2 : ℕ) ^ 6 = 64 by norm_num, hx64]; exact neg_one_ne_one hz)
      (by rw [show (2 : ℕ) ^ (6 + 1) = 64 * 2 by norm_num, pow_mul, hx64]; norm_num)
  have hx0 : (2 : ZMod z) ^ m ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hx64
    exact one_ne_zero (neg_eq_zero.mp hx64.symm)
  obtain ⟨k, hk⟩ := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have := hzp.two_le
  omega

theorem odd_mult {c m : ℕ} (hm : Odd m) : 2 ^ c + 1 ∣ 2 ^ (c * m) + 1 := by
  have h := Odd.nat_add_dvd_pow_add_pow (2 ^ c) 1 hm
  rwa [one_pow, ← pow_mul] at h

-- The primes that are 257 mod 384 between 2100 and 25000.
theorem z_list {z : ℕ} (hzp : z.Prime) (h384 : z % 384 = 257) (hlo : 2100 ≤ z) (hhi : z < 25000) :
    z = 3329 ∨ z = 4481 ∨ z = 7937 ∨ z = 9473 ∨ z = 9857 ∨ z = 11393 ∨ z = 11777 ∨ z = 12161 ∨
    z = 13313 ∨ z = 13697 ∨ z = 14081 ∨ z = 15233 ∨ z = 16001 ∨ z = 17921 ∨ z = 19073 ∨
    z = 19457 ∨ z = 19841 ∨ z = 21377 ∨ z = 23297 := by
  have hj : z = 384 * (z / 384) + 257 := by omega
  generalize z / 384 = j at hj
  subst hj
  have h5 : 5 ≤ j := by omega
  have h64 : j ≤ 64 := by omega
  interval_cases j <;> first | (norm_num at hzp; done) | norm_num

-- If z | 2^a + 1 with 64 | a, the order of 2^64 mod z is o = 2 t, and r = t is the only class with
-- z | (2^64)^r + 1, then a is an odd multiple of 64 t, so every divisor of 2^(64 t) + 1 divides 2^a + 1.
theorem class_root {z q o t a : ℕ} (h64 : 64 ∣ a) (hd : z ∣ 2 ^ a + 1)
    (hB : (2 ^ 64) ^ o % z = 1 % z) (hu : ∀ r < o, z ∣ (2 ^ 64) ^ r + 1 → r = t) (ho : o = 2 * t)
    (ht : 0 < t) (hq : q ∣ (2 ^ 64) ^ t + 1) : q ∣ 2 ^ a + 1 := by
  obtain ⟨m, rfl⟩ := h64
  subst ho
  have hd' : z ∣ (2 ^ 64) ^ m + 1 := by rwa [← pow_mul]
  have hr := hu (m % (2 * t)) (Nat.mod_lt _ (by omega)) (pow_mod_class hB hd')
  have hm := Nat.div_add_mod m (2 * t)
  rw [hr] at hm
  have e : 64 * m = 64 * t * (2 * (m / (2 * t)) + 1) := by
    rw [show 64 * t * (2 * (m / (2 * t)) + 1) = 64 * (2 * t * (m / (2 * t)) + t) by ring, hm]
  rw [e]
  rw [← pow_mul] at hq
  exact hq.trans (odd_mult ⟨m / (2 * t), rfl⟩)

-- The Fermat factors.  Let a = m be the 2-adic valuation, with 5 and 19 simple and 11 not simple.
-- If a = 16 mod 32 then 2^16 + 1 = 65537 divides 2^a + 1; it cannot be simple (11 | 65538), so it is a
-- kernel prime.  If a = 64 mod 128 then 274177 | 2^64 + 1 | 2^a + 1; if 274177 were simple then
-- 137089 | 274178 would divide n, and 137089 cannot be simple (5 | 137090 but the parent of 5 is 19).
theorem fermat_kernel {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h11 : 11 ∉ P) (m19 : 19 ∈ P) :
    (m % 32 = 16 → 65537 ∈ N) ∧ (m % 128 = 64 → 274177 ∈ N ∨ 137089 ∈ N) := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  constructor
  · intro hm
    by_contra hN
    have hd : 65537 ∣ 2 ^ m + 1 := by
      have e : m = 16 * (2 * (m / 32) + 1) := by omega
      have h := odd_mult (c := 16) (m := 2 * (m / 32) + 1) ⟨m / 32, rfl⟩
      rw [← e] at h
      have e2 : (2 : ℕ) ^ 16 + 1 = 65537 := by norm_num
      rwa [e2] at h
    have hp := S5 65537 (by norm_num) (by norm_num) hN hd
    exact h11 (S1 11 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) 65537 hp
      (by norm_num))
  · intro hm
    by_contra hN
    rw [not_or] at hN
    have hd : 274177 ∣ 2 ^ m + 1 := by
      have e : m = 64 * (2 * (m / 128) + 1) := by omega
      have h := odd_mult (c := 64) (m := 2 * (m / 128) + 1) ⟨m / 128, rfl⟩
      rw [← e] at h
      exact (by decide : 274177 ∣ 2 ^ 64 + 1).trans h
    have hp := S5 274177 (by norm_num) (by norm_num) hN.1 hd
    have hp2 := S1 137089 (by norm_num) (by norm_num) hN.2 274177 hp (by norm_num)
    have h5 := S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) 137089 hp2 19 m19
      (by norm_num) (by norm_num)
    omega

-- The thick 223 family (Y > 5001/5000): the kernel has at least two primes, and a is 16 mod 32 (then
-- 65537 is a kernel prime), or 64 mod 128 (then 274177 or 137089 is a kernel prime), or 128 | a.
-- A single kernel prime z would be below 25000, divide 2^a + 1 and be 2 mod 3.  Then a = 16 mod 32 is
-- impossible (65537 would be the kernel prime), so 64 | a, z = 1 mod 128, z = 257 mod 384, and z is one
-- of 19 primes.  For 11 of them no a with 64 | a has z | 2^a + 1.  For 3329, 7937, 11777, 14081, 23297
-- necessarily a = 64 mod 128, and then 274177 or 137089 would be the kernel prime.  For 13313, 17921,
-- 19457 the class of a forces a root q = 39937, 10753, 136193 of 2^a + 1, and q + 1 is divisible by
-- 1051, 283, 3: a prime that does not divide n, or a second parent of 3.
theorem thick_split {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (hres : ∃ z ∈ S, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h19 : 19 ∣ n) (h16 : 16 ∣ padicValNat 2 n)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h0 : padicValNat 2 n ≠ 0)
    (h11 : ¬ 11 ∣ n) (h283 : ¬ 283 ∣ n) (h1051 : ¬ 1051 ∣ n)
    (hthick : 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) :
    2 ≤ S.card ∧
    ((padicValNat 2 n % 32 = 16 ∧ 65537 ^ 2 ∣ n) ∨
      (padicValNat 2 n % 128 = 64 ∧ (274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n)) ∨
      128 ∣ padicValNat 2 n) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr h0)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  obtain ⟨K, K', P, hP, hK, hKK1, hKr0, E, hmem⟩ := setup7 h hS h2
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have mem : ∀ q, q.Prime → q ∣ n → q < 2100 → q ≠ 2 → q ∈ P := fun q hq hqn hlt hq2 =>
    (hmem q).mpr ⟨hq, hq2, hqn, big_notMem hNb hlt⟩
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have h11P : 11 ∉ P := fun hx => h11 ((hmem 11).mp hx).2.2.1
  obtain ⟨F4, F6⟩ := fermat_kernel hP hK E hNb h11P m19
  have toSq : ∀ q, q ∈ S → q ^ 2 ∣ n := fun q hq => ((hS q).mp hq).2.2
  have hcases : (padicValNat 2 n % 32 = 16 ∧ 65537 ^ 2 ∣ n) ∨
      (padicValNat 2 n % 128 = 64 ∧ (274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n)) ∨
      128 ∣ padicValNat 2 n := by
    by_cases h32 : padicValNat 2 n % 32 = 16
    · exact Or.inl ⟨h32, toSq _ (F4 h32)⟩
    · by_cases h6 : padicValNat 2 n % 128 = 64
      · exact Or.inr (Or.inl ⟨h6, (F6 h6).imp (toSq _) (toSq _)⟩)
      · exact Or.inr (Or.inr (by omega))
  refine ⟨?_, hcases⟩
  by_contra hc
  obtain ⟨z, hzS, hzd, hz3⟩ := hres
  have hc1 : S.card = 1 := by
    have := Finset.card_pos.mpr ⟨z, hzS⟩
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
  have hzw : z = w := by
    rw [hw] at hzS
    exact Finset.mem_singleton.mp hzS
  subst hzw
  have hzlo := hNb z hzS
  have hzlt : z < 25000 := by
    rw [hw, Finset.prod_singleton] at hthick
    by_contra hge
    have hz' : (25000 : ℚ) ≤ z := by exact_mod_cast (by omega : 25000 ≤ z)
    have h5z : (5 : ℚ) / z ≤ 5 / 25000 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz'
    linarith
  have notS : ∀ q, q ≠ z → q ∉ S := fun q hq hx =>
    hq (by rw [hw] at hx; exact Finset.mem_singleton.mp hx)
  have hzp : z.Prime := ((hS z).mp hzS).1
  have h64d : 64 ∣ padicValNat 2 n := by
    have h32 : ¬ padicValNat 2 n % 32 = 16 := fun h32 => notS 65537 (by omega) (F4 h32)
    omega
  have hF6 : ¬ padicValNat 2 n % 128 = 64 := fun h6 => by
    rcases F6 h6 with hx | hx
    · exact notS 274177 (by omega) hx
    · exact notS 137089 (by omega) hx
  have hz128 := mod128 hzp (by omega) h64d hzd
  have hlist := z_list hzp (by omega) hzlo hzlt
  have root : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ z → q ∣ 2 ^ padicValNat 2 n + 1 → q ∈ P :=
    fun q hq hq2 hqz hd => S5 q hq hq2 (notS q hqz) hd
  rcases hlist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact hF6 (by
      have h128 : ¬ 128 ∣ padicValNat 2 n := fun hc =>
        no_div (c := 128) (t := 13) (by norm_num) (by decide) (by decide) hc hzd
      omega)
  · exact no_div (c := 64) (t := 35) (by norm_num) (by decide) (by decide) h64d hzd
  · exact hF6 (by
      have h128 : ¬ 128 ∣ padicValNat 2 n := fun hc =>
        no_div (c := 128) (t := 31) (by norm_num) (by decide) (by decide) hc hzd
      omega)
  · exact no_div (c := 64) (t := 37) (by norm_num) (by decide) (by decide) h64d hzd
  · exact no_div (c := 64) (t := 77) (by norm_num) (by decide) (by decide) h64d hzd
  · exact no_div (c := 64) (t := 89) (by norm_num) (by decide) (by decide) h64d hzd
  · exact hF6 (by
      have h128 : ¬ 128 ∣ padicValNat 2 n := fun hc =>
        no_div (c := 128) (t := 23) (by norm_num) (by decide) (by decide) hc hzd
      omega)
  · exact no_div (c := 64) (t := 95) (by norm_num) (by decide) (by decide) h64d hzd
  · have hq := class_root (q := 39937) (o := 104) (t := 52) h64d hzd (by decide) (by decide) rfl
      (by norm_num) (by decide)
    have hp := root 39937 (by norm_num) (by norm_num) (by norm_num) hq
    have hc := S1 1051 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) 39937 hp (by norm_num)
    exact h1051 ((hmem 1051).mp hc).2.2.1
  · exact no_div (c := 64) (t := 107) (by norm_num) (by decide) (by decide) h64d hzd
  · exact hF6 (by
      have h128 : ¬ 128 ∣ padicValNat 2 n := fun hc =>
        no_div (c := 128) (t := 55) (by norm_num) (by decide) (by decide) hc hzd
      omega)
  · exact no_div (c := 64) (t := 119) (by norm_num) (by decide) (by decide) h64d hzd
  · exact no_div (c := 64) (t := 125) (by norm_num) (by decide) (by decide) h64d hzd
  · have hq := class_root (q := 10753) (o := 140) (t := 70) h64d hzd (by decide) (by decide) rfl
      (by norm_num) (by decide)
    have hp := root 10753 (by norm_num) (by norm_num) (by norm_num) hq
    have hc := S1 283 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) 10753 hp (by norm_num)
    exact h283 ((hmem 283).mp hc).2.2.1
  · exact no_div (c := 64) (t := 149) (by norm_num) (by decide) (by decide) h64d hzd
  · have hq := class_root (q := 136193) (o := 76) (t := 38) h64d hzd (by decide) (by decide) rfl
      (by norm_num) (by decide)
    have hp := root 136193 (by norm_num) (by norm_num) (by norm_num) hq
    have h5 := S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) 136193 hp 5 m5
      (by norm_num) (by norm_num)
    omega
  · exact no_div (c := 64) (t := 155) (by norm_num) (by decide) (by decide) h64d hzd
  · exact no_div (c := 64) (t := 167) (by norm_num) (by decide) (by decide) h64d hzd
  · exact hF6 (by
      have h128 : ¬ 128 ∣ padicValNat 2 n := fun hc =>
        no_div (c := 128) (t := 91) (by norm_num) (by decide) (by decide) hc hzd
      omega)

end Erdos1052C17

-- The 2-adic valuation is bounded over the family of step H3 of R1.H2.R1.H2.R1.H1.R1.H1.R1 (223, 991,
-- 1783 | n, kernel not thin: Y > 2501/2500),
-- with at least two kernel primes, a = 16 mod 32, and 65537 a kernel prime.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → padicValNat 2 n % 32 = 16 → 65537 ^ 2 ∣ n →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H3 of R1.H2.R1.H2.R1.H1.R1.H1.R1 (223, 991,
-- 1783 | n, kernel not thin: Y > 2501/2500),
-- with at least two kernel primes, a = 64 mod 128, and 274177 or 137089 a kernel prime.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → padicValNat 2 n % 128 = 64 →
    (274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n) →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H3 of R1.H2.R1.H2.R1.H1.R1.H1.R1 (223, 991,
-- 1783 | n, kernel not thin: Y > 2501/2500),
-- with at least two kernel primes and 128 | a.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → 128 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.H3 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩ ⟨A3, hA3⟩
  refine ⟨max A1 (max A2 A3), fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
    h223 h991 h1783 h48 hk => ?_⟩
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hz := (hres S subset_rfl hNS hadm2).1
  have h11 : ¬ 11 ∣ n := fun hd => by
    rcases hl 11 (by norm_num) hd (by norm_num) with e | e | e | e | e | e | e | e | e <;>
      exact absurd e (by norm_num)
  have h283 : ¬ 283 ∣ n := fun hd => by
    rcases hl 283 (by norm_num) hd (by norm_num) with e | e | e | e | e | e | e | e | e <;>
      exact absurd e (by norm_num)
  have h1051 : ¬ 1051 ∣ n := fun hd => by
    rcases hl 1051 (by norm_num) hd (by norm_num) with e | e | e | e | e | e | e | e | e <;>
      exact absurd e (by norm_num)
  obtain ⟨hc, hcase⟩ := Erdos1052C17.thick_split h hS hadm1 hadm2 hz h3 h5 h19 h16 h64
    (fun h0 => by rw [h0] at h48; exact absurd h48 (by norm_num)) h11 h283 h1051 (lt_trans (by norm_num) hk)
  rcases hcase with ⟨h32, hq⟩ | ⟨h6, hq⟩ | h128
  · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h991 h1783 h48 hk hc h32 hq).trans (le_max_left _ _)
  · exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h991 h1783 h48 hk hc h6 hq).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hA3 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h991 h1783 h48 hk hc h128).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1
