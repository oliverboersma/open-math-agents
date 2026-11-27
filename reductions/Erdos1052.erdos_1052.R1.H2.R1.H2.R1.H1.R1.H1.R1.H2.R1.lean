import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1 in two.  Proving both H proves the step.
--
-- As in the parent files: n unitary perfect, a = padicValNat 2 n, S = the set of odd primes p with
-- p^2 | n (the kernel), a prime of n is SIMPLE if it divides n exactly once, and
-- Y = the product over S of (1 + 5/z).  The step is the thin 607, 3967 family: 223, 607, 3967 | n,
-- a >= 48, no prime of n below 5057 other than 2, 3, 5, 7, 19, 31, 223, 607, 3967, and Y <= 5001/5000.
--
-- What is proved here (theorem thin_split): 8191 | n or 7933 | n.
-- If neither 8191 nor 7933 divides n then the weight inequality masterU (of the parent file) applies
-- with weight 1 at the Mersenne prime 8191, and it closes both remaining cases:
--   19423 not simple   node_no19423   (parent of 607 at least 310783; total 1.99983778)
--   19423 simple       node_19423     (parent of 19423 at least 155383; total 1.99995361)
-- (in both: parent of 223 at least 213633, parent of 3967 at least 126943, every kernel prime at least
-- 12500, leaf constant D for Y <= 5001/5000).
-- H1 is the case 8191 | n; H2 is the case 8191 does not divide n and 7933 | n.
-- The sub-namespace Erdos1052C17 holds the helper theorems.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1

namespace Erdos1052C17

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7 OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C9
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C11 OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C16

-- Parent of 607 other than 1213 and 19423, when every other odd prime factor of p + 1 is at least
-- 3967: at least 310783 (1214 * 2^e - 1 is composite for e ≤ 7 except 1213 and 19423).
theorem T607d {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 607 ∨ 3967 ≤ r)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) :
    310783 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 8 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 8 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 607 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h1213 h19423 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Parent of 3967 other than 7933, when every other odd prime factor of p + 1 is at least 5057:
-- at least 126943 (7934 * 2^e - 1 is composite for e = 1, 2, 3).
theorem T3967a {p : ℕ} (hp : p.Prime) (hd : 3967 ∣ p + 1) (hsq : ¬ 3967 * 3967 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3967 ∨ 5057 ≤ r)
    (h7933 : p ≠ 7933) :
    126943 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 4 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 3967 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h7933 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 3967 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Parent of 19423, when every other odd prime factor of p + 1 is at least 12500: at least 155383
-- (38845 and 77691 are composite).
theorem T19423a {p : ℕ} (hp : p.Prime) (hd : 19423 ∣ p + 1) (hsq : ¬ 19423 * 19423 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 19423 ∨ 12500 ≤ r) :
    155383 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 2 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 19423 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp  <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 19423 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- The thin 607, 3967 family (prod (1 + 5/z) ≤ 5001/5000) without 7933, 8191 and 19423: impossible for
-- a ≥ 20 (masterU with weight 1 at 8191; chains 3 ← 5 ← 19 ← 607 with parent of 607 at least 310783,
-- 7 ← 223 with parent of 223 at least 213633, 31 ← 3967 with parent of 3967 at least 126943).
theorem node_no19423 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN5 : ∀ z ∈ N, 12500 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P)
    (h7933 : 7933 ∉ P) (h8191 : 8191 ∉ P) (h19423 : 19423 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have h3967N : 3967 ∉ N := fun h => by
    have := hN5 3967 h
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd
      (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → q ≠ 607 → q ≠ 3967 →
      5057 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223 e607 e3967
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ), (p + 1) = 66405563105280 := by
      decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ), p = 33209347945515 := by
      decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 12500) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      12500 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨ r = 3967 ∨
        5057 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN5 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (310784 / 310782)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (310784 / 310782))) else
      if p = 19 then 20 / 19 * (608 / 607 * (310784 / 310782)) else
      if p = 607 then 608 / 607 * (310784 / 310782) else
      if p = 7 then 8 / 7 * (224 / 223 * (213634 / 213632)) else
      if p = 223 then 224 / 223 * (213634 / 213632) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126942)) else
      if p = 3967 then 3968 / 3967 * (126944 / 126942) else
      if p = 8191 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (310784 / 310782)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (310784 / 310782))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (310784 / 310782)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (310784 / 310782) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (213634 / 213632)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (213634 / 213632) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126942)) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126942) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 → c ≠ 8191 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e8191 e127 => by
      rw [hβ, if_neg e3,
        if_neg e5,
        if_neg e19,
        if_neg e607,
        if_neg e7,
        if_neg e223,
        if_neg e31,
        if_neg e3967,
        if_neg e8191,
        if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607
    · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967
    · subst e3967; rw [b3967]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; exact absurd hp h8191
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e8191 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)))
    (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 310783 ≤ p := T607d (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 310783) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 213633 ≤ p := T223y (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
      rw [b223]
      exact step_ge (t := 213633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 3967 := T31 p hp hd
      rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967
    · subst e3967
      have hge : 126943 ≤ p := T3967a (hP p hp).1 hd
        (S4b 3967 (by norm_num) (by norm_num) h3967N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => h7933 (h ▸ hp))
      rw [b3967]
      exact step_ge (t := 126943) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      exact absurd hc h8191
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e8191 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · exact b8191.symm.le
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- The thin 607, 3967 family (prod (1 + 5/z) ≤ 5001/5000) with 19423, without 7933 and 8191: impossible
-- for a ≥ 20 (masterU with weight 1 at 8191; chains 3 ← 5 ← 19 ← 607 ← 19423 with parent of 19423 at
-- least 155383, 7 ← 223 with parent of 223 at least 213633, 31 ← 3967 with parent of 3967 at least 126943).
theorem node_19423 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN5 : ∀ z ∈ N, 12500 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P)
    (h19423 : 19423 ∈ P) (h19423N : 19423 ∉ N) (h7933 : 7933 ∉ P) (h8191 : 8191 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have h3967N : 3967 ∉ N := fun h => by
    have := hN5 3967 h
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd
      (by norm_num)
  have T607 : ∀ p ∈ P, 607 ∣ p + 1 → p = 19423 := fun p hp hd =>
    S2 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19423 h19423 hd
      (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 19423} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h19423
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → q ≠ 607 → q ≠ 3967 → q ≠ 19423 →
      6837 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223 e607 e3967 e19423
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967, 19423} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 19423} : Finset ℕ), (p + 1) = 1289861657756958720 := by
      decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 19423} : Finset ℕ), p = 645025165145737845 := by
      decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 12500) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      12500 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨ r = 3967 ∨ r = 19423 ∨
        6837 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN5 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e19423 : r = 19423
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e19423))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e19423)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382))))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382)))) else
      if p = 19 then 20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382))) else
      if p = 607 then 608 / 607 * (19424 / 19423 * (155384 / 155382)) else
      if p = 19423 then 19424 / 19423 * (155384 / 155382) else
      if p = 7 then 8 / 7 * (224 / 223 * (213634 / 213632)) else
      if p = 223 then 224 / 223 * (213634 / 213632) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126942)) else
      if p = 3967 then 3968 / 3967 * (126944 / 126942) else
      if p = 8191 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382)))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (19424 / 19423 * (155384 / 155382))) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (19424 / 19423 * (155384 / 155382)) := by rw [hβ]; norm_num
  have b19423 : β 19423 = 19424 / 19423 * (155384 / 155382) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (213634 / 213632)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (213634 / 213632) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126942)) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126942) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 19423 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 → c ≠ 8191 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e19423 e7 e223 e31 e3967 e8191 e127 => by
      rw [hβ, if_neg e3,
        if_neg e5,
        if_neg e19,
        if_neg e607,
        if_neg e19423,
        if_neg e7,
        if_neg e223,
        if_neg e31,
        if_neg e3967,
        if_neg e8191,
        if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607
    · subst e607; rw [b607]; norm_num
    by_cases e19423 : p = 19423
    · subst e19423; rw [b19423]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967
    · subst e3967; rw [b3967]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; exact absurd hp h8191
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e19423 e7 e223 e31 e3967 e8191 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)))
    (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      obtain rfl : p = 19423 := T607 p hp hd
      rw [b607, b19423]; norm_num
    by_cases e19423 : c = 19423
    · subst e19423
      have hge : 155383 ≤ p := T19423a (hP p hp).1 hd
        (S4b 19423 (by norm_num) (by norm_num) h19423N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
      rw [b19423]
      exact step_ge (t := 155383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 213633 ≤ p := T223y (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
      rw [b223]
      exact step_ge (t := 213633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 3967 := T31 p hp hd
      rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967
    · subst e3967
      have hge : 126943 ≤ p := T3967a (hP p hp).1 hd
        (S4b 3967 (by norm_num) (by norm_num) h3967N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => h7933 (h ▸ hp))
      rw [b3967]
      exact step_ge (t := 126943) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      exact absurd hc h8191
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e19423 e7 e223 e31 e3967 e8191 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · exact b8191.symm.le
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- The thin 607, 3967 family (hypotheses of step H2 of R1.H2.R1.H2.R1.H1.R1.H1.R1): 8191 | n or 7933 | n.
-- Otherwise 8191 and 7933 are not simple, the Mersenne chain at 8191 costs nothing, and one weight
-- inequality closes each of the two cases 19423 simple / not simple.
theorem thin_split {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h31 : 31 ∣ n)
    (hl : ∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967)
    (h223 : 223 ∣ n) (h607 : 607 ∣ n) (h3967 : 3967 ∣ n) (h48 : 48 ≤ padicValNat 2 n)
    (hthin : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) :
    8191 ∣ n ∨ 7933 ∣ n := by
  by_contra hcon
  rw [not_or] at hcon
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) h48)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  have hY := adm_hY hNS hadm2
  obtain ⟨K, K', P, hP, hK, hKK1, hKr0, E, hmem⟩ := setup7 h hS h2
  have hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100) := hKr0.trans (kk_bound subset_rfl hNb hY)
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have hge := ge_12500 (fun w hw => (hNS w hw).1.ne_zero) (hthin.trans (by norm_num))
  have mem : ∀ q, q.Prime → q ∣ n → q < 12500 → q ≠ 2 → q ∈ P := fun q hq hqn hlt hq2 =>
    (hmem q).mpr ⟨hq, hq2, hqn, fun hx => absurd (hge q hx) (not_le.mpr hlt)⟩
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m7 := mem 7 (by norm_num) h7 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have m31 := mem 31 (by norm_num) h31 (by norm_num) (by norm_num)
  have m223 := mem 223 (by norm_num) h223 (by norm_num) (by norm_num)
  have m607 := mem 607 (by norm_num) h607 (by norm_num) (by norm_num)
  have m3967 := mem 3967 (by norm_num) h3967 (by norm_num) (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 5 m5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19 m19 hd (by norm_num)
  have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := fun q hq hlt => by
    obtain ⟨hqp, hq2, hqn, _⟩ := (hmem q).mp hq
    rcases hl q hqp hqn (lt_trans hlt (by norm_num)) with e | e | e | e | e | e | e | e | e
    · exact absurd e hq2
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · exact absurd (e ▸ hlt) (by norm_num)
    · exact absurd (e ▸ hlt) (by norm_num)
    · exact absurd (e ▸ hlt) (by norm_num)
  have n8191 : 8191 ∉ P := fun hx => hcon.1 ((hmem 8191).mp hx).2.2.1
  have n7933 : 7933 ∉ P := fun hx => hcon.2 ((hmem 7933).mp hx).2.2.1
  have hD : ∀ U : Finset ℕ,
      (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)) :=
    fun U hU => sumD_thin
      (fun w hw => ⟨(hNS w hw).1, le_trans (by norm_num) (hge w hw)⟩) hthin U hU
  have hm20 : 20 ≤ padicValNat 2 n := le_trans (by norm_num) h48
  by_cases h19423 : 19423 ∈ P
  · exact node_19423 hP hNS hK hKr hKK1 hNb hge hD E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223 m607 m3967
      h19423 ((hmem 19423).mp h19423).2.2.2 n7933 n8191
  · exact node_no19423 hP hNS hK hKr hKK1 hNb hge hD E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223 m607
      m3967 n7933 n8191 h19423

end Erdos1052C17

-- The 2-adic valuation is bounded over the family of step H2 of R1.H2.R1.H2.R1.H1.R1.H1.R1 (223, 607,
-- 3967 | n, thin kernel: Y <= 5001/5000), restricted to 8191 | n.
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    8191 ∣ n →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H2 of R1.H2.R1.H2.R1.H1.R1.H1.R1 (223, 607,
-- 3967 | n, thin kernel: Y <= 5001/5000), restricted to 7933 | n with 8191 not dividing n.
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    ¬ 8191 ∣ n → 7933 ∣ n →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩
  refine ⟨max A1 A2, fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
    h223 h607 h3967 h48 hk => ?_⟩
  by_cases h8191 : 8191 ∣ n
  · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h607 h3967 h48 hk h8191).trans (le_max_left _ _)
  · have h7933 : 7933 ∣ n :=
      (Erdos1052C17.thin_split h hS hadm1 hadm2 h3 h5 h7 h19 h31 hl h223 h607 h3967 h48
        hk).resolve_left h8191
    exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
      h223 h607 h3967 h48 hk h8191 h7933).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1
