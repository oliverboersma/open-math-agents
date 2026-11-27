import OMAStatements.S_oeis_a000166
import Mathlib

/-
The odd-index square obstruction uses the two neighboring divisors of
D(n) + 1. At even indices, the quadratic character of -2 modulo n - 3
eliminates two residue classes. The signed recurrence supplies the
divisibility and valuation tests. For related periodicity and valuations,
see Piotr Miska, Arithmetic Properties of the Sequence of Derangements
and its Generalizations, https://arxiv.org/abs/1508.01987.
-/

-- Credit: @Heart-galaxy
-- Partial reduction; the full perfect-power conjecture is not proved here.

namespace A000166

theorem fourth_term : numDerangements 4 = 3 ^ 2 := by decide

/-- The signed recurrence and the two-step recurrence give the two adjacent divisors. -/
theorem odd_index_product_dvd (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    n * (n - 2) ∣ numDerangements n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  have hev : Even (m + 2) := by
    obtain ⟨q, hq⟩ := ho
    exact ⟨q, by omega⟩
  have hint := numDerangements_succ (m + 2)
  rw [Even.neg_one_pow hev] at hint
  have hNat : numDerangements (m + 3) + 1 = (m + 3) * numDerangements (m + 2) := by
    exact_mod_cast (show (numDerangements (m + 3) : ℤ) + 1 =
      ((m : ℤ) + 3) * numDerangements (m + 2) by push_cast at hint; linarith)
  rw [hNat, numDerangements_add_two m, ← mul_assoc]
  exact ⟨numDerangements m + numDerangements (m + 1), by congr 2⟩

theorem odd_index_product_mod_four (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    (n * (n - 2)) % 4 = 3 := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
  have hCases : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rw [Nat.mul_mod]
  rcases hCases with h | h
  · have h' : (n - 2) % 4 = 3 := by omega
    simp [h, h']
  · have h' : (n - 2) % 4 = 1 := by omega
    simp [h, h']

/-- A modulus congruent to three modulo four cannot divide a square plus one. -/
theorem not_dvd_square_add_one (m a : ℕ) (hm : m % 4 = 3) : ¬ m ∣ a ^ 2 + 1 := by
  intro hdiv
  have hz : (a : ZMod m) ^ 2 + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff (a ^ 2 + 1) m).mpr hdiv
  have hSquare : IsSquare (-1 : ZMod m) := by
    refine ⟨(a : ZMod m), ?_⟩
    rw [← pow_two]
    exact (eq_neg_iff_add_eq_zero.mpr hz).symm
  obtain ⟨x, y, heq⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one hSquare
  have hcast : (m : ZMod 4) = 3 := by
    exact (ZMod.natCast_eq_natCast_iff' m 3 4).mpr (by simpa using hm)
  have hxy : (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 = 3 := by
    have h := congrArg (fun z : ℕ => (z : ZMod 4)) heq
    simpa only [hcast, Nat.cast_add, Nat.cast_pow] using h.symm
  exact (show ∀ u v : ZMod 4, u ^ 2 + v ^ 2 ≠ 3 by decide) _ _ hxy

/-- Odd indices greater than two cannot give a square. -/
theorem odd_index_not_square (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    ¬ ∃ a : ℕ, numDerangements n = a ^ 2 := by
  rintro ⟨a, ha⟩
  exact not_dvd_square_add_one (n * (n - 2)) a (odd_index_product_mod_four n hn ho)
    (ha ▸ odd_index_product_dvd n hn ho)

theorem even_derangements_of_odd_index (n : ℕ) (ho : Odd n) : Even (numDerangements n) := by
  obtain ⟨k, rfl⟩ := ho
  cases k with
  | zero => simp
  | succ k =>
    rw [show 2 * k.succ + 1 = (2 * k + 1) + 2 by omega, numDerangements_add_two]
    exact (show Even ((2 * k + 1) + 1) from ⟨k + 1, by omega⟩).mul_right _

theorem odd_derangements_of_even_index (n : ℕ) (he : Even n) : Odd (numDerangements n) := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k.succ + k.succ = (k + k) + 2 by omega, numDerangements_add_two]
    have ho : Odd (k + k + 1) := ⟨k, by omega⟩
    exact ho.mul (ih.add_even (even_derangements_of_odd_index _ ho))

/-- At odd indices, the multiplicity of two is inherited exactly from the index minus one. -/
theorem two_factorization_of_odd_index (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    (numDerangements n).factorization 2 = (n - 1).factorization 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
  have hm' : Even (m + 1) := Nat.even_iff.mpr (by have := Nat.odd_iff.mp hm; omega)
  have hodd : Odd (numDerangements m + numDerangements (m + 1)) :=
    (even_derangements_of_odd_index _ hm).add_odd (odd_derangements_of_even_index _ hm')
  have hco : numDerangements m + numDerangements (m + 1) ≠ 0 := by
    intro h
    rw [h] at hodd
    exact (by decide : ¬ Odd (0 : ℕ)) hodd
  have hno : ¬2 ∣ numDerangements m + numDerangements (m + 1) :=
    fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  rw [numDerangements_add_two, Nat.factorization_mul (by omega) hco, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hno, add_zero]
  congr 2

/-- Odd-index candidates have an odd exponent dividing the corresponding two-adic valuation. -/
theorem odd_index_power_constraints {n a k : ℕ} (hn : 2 < n) (ho : Odd n)
    (heq : numDerangements n = a ^ k) : Odd k ∧ k ∣ (n - 1).factorization 2 := by
  constructor
  · rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hk
    · exfalso
      apply odd_index_not_square n hn ho
      refine ⟨a ^ j, ?_⟩
      rw [heq, ← pow_mul]
      congr 1
      omega
    · exact hk
  · rw [← two_factorization_of_odd_index n hn ho, heq, Nat.factorization_pow]
    exact ⟨a.factorization 2, Finsupp.smul_apply _ _ _⟩

theorem odd_index_power_mod_eight {n a k : ℕ} (hn : 2 < n) (ho : Odd n) (hk : 1 < k)
    (heq : numDerangements n = a ^ k) : n % 8 = 1 := by
  obtain ⟨hkOdd, hkDvd⟩ := odd_index_power_constraints hn ho heq
  have hk3 : 3 ≤ k := by have := Nat.odd_iff.mp hkOdd; omega
  have hne : n - 1 ≠ 0 := by omega
  have h2 : 2 ∣ n - 1 := (even_iff_two_dvd.mp <| Nat.even_iff.mpr (by
    have := Nat.odd_iff.mp ho
    omega))
  have hpos := Nat.prime_two.factorization_pos_of_dvd hne h2
  have h8 : 2 ^ 3 ∣ n - 1 := (Nat.prime_two.pow_dvd_iff_le_factorization hne).mpr
    (hk3.trans (Nat.le_of_dvd hpos hkDvd))
  have hm : (n - 1) % 8 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h8)
  omega

end A000166

-- Credit: @Heart-galaxy
-- Partial reduction; the full perfect-power conjecture is not proved here.

namespace A000166

@[simp] theorem signedDerangements_zero : ((-1 : ℤ) ^ (0) * (numDerangements (0) : ℤ)) = 1 := by
  simp

private theorem square_neg_one_pow (n : ℕ) : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]

theorem signedDerangements_succ (n : ℕ) :
    ((-1 : ℤ) ^ (n + 1) * (numDerangements (n + 1) : ℤ)) = 1 - ((n + 1 : ℕ) : ℤ) * ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) := by
  rw [numDerangements_succ, pow_succ]
  push_cast
  calc
    _ = ((-1 : ℤ) ^ n) ^ 2 - ((n : ℤ) + 1) * ((-1) ^ n * numDerangements n) := by ring
    _ = _ := by rw [square_neg_one_pow]

/-- The signs make the modular period exactly one shift by the modulus. -/
theorem signed_mod_period (m n : ℕ) :
    ((-1 : ℤ) ^ (n + m) * (numDerangements (n + m) : ℤ)) ≡ ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) [ZMOD (m : ℤ)] := by
  induction n with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      have hz : ((m + 1 : ℕ) : ℤ) * ((-1 : ℤ) ^ (m) * (numDerangements (m) : ℤ)) ≡ 0 [ZMOD ((m + 1 : ℕ) : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
      simpa only [Nat.zero_add, signedDerangements_succ, signedDerangements_zero, sub_zero] using
        (Int.ModEq.refl (n := ((m + 1 : ℕ) : ℤ)) 1).sub hz
  | succ n ih =>
    rw [show n.succ + m = n + m + 1 by omega, signedDerangements_succ, signedDerangements_succ]
    have hc : ((n + m + 1 : ℕ) : ℤ) ≡ ((n + 1 : ℕ) : ℤ) [ZMOD (m : ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      rw [show ((n + 1 : ℕ) : ℤ) - ((n + m + 1 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring]
      exact Int.dvd_neg.mpr (dvd_refl _)
    exact (Int.ModEq.refl _).sub (hc.mul ih)

theorem signed_mod_multiple (m n k : ℕ) :
    ((-1 : ℤ) ^ (n + m * k) * (numDerangements (n + m * k) : ℤ)) ≡ ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) [ZMOD (m : ℤ)] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact (signed_mod_period m (n + m * k)).trans ih

theorem signed_mod_reduce (m n : ℕ) :
    ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) ≡ ((-1 : ℤ) ^ (n % m) * (numDerangements (n % m) : ℤ)) [ZMOD (m : ℤ)] := by
  simpa only [Nat.mod_add_div] using signed_mod_multiple m (n % m) (n / m)

theorem dvd_signed_iff (m n : ℕ) : (m : ℤ) ∣ ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) ↔ m ∣ numDerangements n := by
  constructor
  · intro h
    have h' := dvd_mul_of_dvd_right h ((-1 : ℤ) ^ n)
    rw [← mul_assoc, ← pow_two, square_neg_one_pow, one_mul] at h'
    exact Int.natCast_dvd_natCast.mp h'
  · intro h
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h) ((-1 : ℤ) ^ n)

/-- Testing any modulus for divisibility only requires its reduced index. -/
theorem dvd_derangements_mod (m n : ℕ) :
    m ∣ numDerangements n ↔ m ∣ numDerangements (n % m) := by
  rw [← dvd_signed_iff, ← dvd_signed_iff, ← Int.modEq_zero_iff_dvd, ← Int.modEq_zero_iff_dvd]
  have hp := signed_mod_reduce m n
  exact ⟨fun h => hp.symm.trans h, fun h => hp.trans h⟩

theorem no_power_of_single_prime_factor {d p a k : ℕ} (hp : p.Prime)
    (hd : p ∣ d) (h2 : ¬ p ^ 2 ∣ d) (hk : 1 < k) (heq : d = a ^ k) : False := by
  have ha : p ∣ a := hp.dvd_of_dvd_pow (heq ▸ hd)
  apply h2
  rw [heq]
  exact (pow_dvd_pow_of_dvd ha 2).trans (pow_dvd_pow a (by omega))

/-- A certificate for a residue class in which a prime has multiplicity one. -/
theorem no_power_of_residue {n p a k : ℕ} (hp : p.Prime) (hk : 1 < k)
    (hd : p ∣ numDerangements (n % p))
    (h2 : ¬ p ^ 2 ∣ numDerangements (n % p ^ 2)) (heq : numDerangements n = a ^ k) : False :=
  no_power_of_single_prime_factor hp ((dvd_derangements_mod p n).mpr hd)
    (fun h => h2 ((dvd_derangements_mod (p ^ 2) n).mp h)) hk heq

theorem even_index_mod_sub_three (n : ℕ) (hn : 2 < n) (he : Even n) :
    (numDerangements n : ℤ) ≡ -2 [ZMOD ((n - 3 : ℕ) : ℤ)] := by
  have hp := signed_mod_period (n - 3) 3
  rw [show 3 + (n - 3) = n by omega, show ((-1 : ℤ) ^ (3) * (numDerangements (3) : ℤ)) = -2 by decide] at hp
  simpa only [he.neg_one_pow, one_mul] using hp

/-- A square at a positive even index requires one of two classes modulo eight. -/
theorem even_index_square_mod_eight {n a : ℕ} (hn : 2 < n) (he : Even n)
    (heq : numDerangements n = a ^ 2) : n % 8 = 4 ∨ n % 8 = 6 := by
  by_contra h
  let m := n - 3
  have hmOdd : Odd m := Nat.odd_iff.mpr (by dsimp [m]; have := Nat.even_iff.mp he; omega)
  have hm : m % 8 = 5 ∨ m % 8 = 7 := by dsimp [m]; have := Nat.even_iff.mp he; omega
  have hJacobi : jacobiSym (-2) m = -1 := by
    rw [jacobiSym.at_neg_two hmOdd, ZMod.χ₈'_nat_eq_if_mod_eight]
    rcases hm with hm | hm <;> simp [hm, Nat.odd_iff.mp hmOdd]
  apply ZMod.nonsquare_of_jacobiSym_eq_neg_one hJacobi
  refine ⟨(a : ZMod m), ?_⟩
  have hc := (ZMod.intCast_eq_intCast_iff (numDerangements n : ℤ) (-2) m).mpr
    (even_index_mod_sub_three n hn he)
  rw [heq] at hc
  push_cast at hc
  push_cast
  simpa only [pow_two] using hc.symm

theorem even_index_even_power_mod_eight {n a k : ℕ} (hn : 2 < n) (he : Even n)
    (hk : Even k) (heq : numDerangements n = a ^ k) : n % 8 = 4 ∨ n % 8 = 6 := by
  obtain ⟨r, rfl⟩ := hk
  apply even_index_square_mod_eight hn he (a := a ^ r)
  rw [heq, ← pow_mul, Nat.mul_two]

private theorem signed_cofactor (n : ℕ) :
    ((-1 : ℤ) ^ (n + 1) * (numDerangements (n + 1) : ℤ)) - ((-1 : ℤ) ^ (n) * (numDerangements (n) : ℤ)) =
      (-1 : ℤ) ^ (n + 1) * ((numDerangements n : ℤ) + numDerangements (n + 1)) := by
  rw [pow_succ]
  ring

/-- A prime dividing the index minus one can divide the cofactor only in a specific
residue of the signed derangement sequence. -/
theorem cofactor_not_dvd_of_residue {m p : ℕ} (hp : p.Prime) (hpd : p ∣ m + 1)
    (hex : ¬ ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) ≡ 1 [ZMOD (p : ℤ)]) :
    ¬ p ∣ numDerangements m + numDerangements (m + 1) := by
  intro hc
  obtain ⟨t, ht⟩ := hpd
  have htne : t ≠ 0 := by rintro rfl; simp at ht
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htne
  have hm : m = p - 1 + p * j := by
    have hpPos := hp.pos
    rw [Nat.mul_succ] at ht
    omega
  have htop : ((-1 : ℤ) ^ (m + 1) * (numDerangements (m + 1) : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
    simpa only [Nat.zero_add, ← ht, signedDerangements_zero] using signed_mod_multiple p 0 j.succ
  have hlow : ((-1 : ℤ) ^ (m) * (numDerangements (m) : ℤ)) ≡ ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) [ZMOD (p : ℤ)] := by
    rw [hm]
    exact signed_mod_multiple p (p - 1) j
  have hcz : ((numDerangements m : ℤ) + numDerangements (m + 1)) ≡ 0 [ZMOD (p : ℤ)] := by
    have hz := Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hc)
    simpa only [Nat.cast_add] using hz
  have hz : ((-1 : ℤ) ^ (m + 1) * (numDerangements (m + 1) : ℤ)) - ((-1 : ℤ) ^ (m) * (numDerangements (m) : ℤ)) ≡ 0 [ZMOD (p : ℤ)] := by
    rw [signed_cofactor]
    simpa only [mul_zero] using hcz.mul_left ((-1 : ℤ) ^ (m + 1))
  have hdiff : 1 - ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) ≡ 0 [ZMOD (p : ℤ)] := (htop.sub hlow).symm.trans hz
  apply hex
  simpa only [sub_sub_cancel, sub_zero] using hdiff.sub_left 1

theorem factorization_inherited_from_index {n p : ℕ} (hn : 2 < n) (hp : p.Prime)
    (hpd : p ∣ n - 1) (hex : ¬ ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) ≡ 1 [ZMOD (p : ℤ)]) :
    (numDerangements n).factorization p = (n - 1).factorization p := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have hC : ¬ p ∣ numDerangements m + numDerangements (m + 1) :=
    cofactor_not_dvd_of_residue hp (by simpa using hpd) hex
  have hCN : numDerangements m + numDerangements (m + 1) ≠ 0 :=
    fun h => hC (h ▸ dvd_zero p)
  rw [numDerangements_add_two, Nat.factorization_mul (by omega) hCN, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hC, add_zero]
  congr 2

theorem power_exponent_dvd_inherited_factorization {n p a k : ℕ} (hn : 2 < n) (hp : p.Prime)
    (hpd : p ∣ n - 1) (hex : ¬ ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) ≡ 1 [ZMOD (p : ℤ)])
    (heq : numDerangements n = a ^ k) : k ∣ (n - 1).factorization p := by
  rw [← factorization_inherited_from_index hn hp hpd hex, heq, Nat.factorization_pow]
  exact ⟨a.factorization p, Finsupp.smul_apply _ _ _⟩

theorem small_good_prime {p : ℕ} (hp : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨
    p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29) :
    p.Prime ∧ ¬ ((-1 : ℤ) ^ (p - 1) * (numDerangements (p - 1) : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- These primes cannot occur with multiplicity one in the index minus one of a power. -/
theorem no_power_of_small_prime_exactly_once {n p a k : ℕ} (hn : 2 < n) (hk : 1 < k)
    (hp : p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29)
    (hpd : p ∣ n - 1) (hp2 : ¬ p ^ 2 ∣ n - 1) (heq : numDerangements n = a ^ k) : False := by
  obtain ⟨hp, hex⟩ := small_good_prime hp
  have hn0 : n - 1 ≠ 0 := by omega
  have hpos := hp.factorization_pos_of_dvd hn0 hpd
  have hlt : (n - 1).factorization p < 2 :=
    Nat.lt_of_not_ge fun h => hp2 ((hp.pow_dvd_iff_le_factorization hn0).mpr h)
  have hval : (n - 1).factorization p = 1 := by omega
  have hdiv := power_exponent_dvd_inherited_factorization hn hp hpd hex heq
  rw [hval] at hdiv
  have hOne := Nat.dvd_one.mp hdiv
  omega

/-- On two classes modulo nine, the multiplicity of three is exactly two. -/
theorem three_factorization_mod_nine (n : ℕ) (hn : n % 9 = 4 ∨ n % 9 = 7) :
    (numDerangements n).factorization 3 = 2 := by
  have h9 : 9 ∣ numDerangements n := by
    rw [dvd_derangements_mod]
    rcases hn with hn | hn <;> rw [hn] <;> decide +kernel
  have hmod : n % 27 % 9 = n % 9 := Nat.mod_mod_of_dvd n (by decide)
  have hlt : n % 27 < 27 := Nat.mod_lt _ (by decide)
  have h27 : ¬27 ∣ numDerangements n := by
    rw [dvd_derangements_mod]
    have hh : n % 27 = 4 ∨ n % 27 = 7 ∨ n % 27 = 13 ∨ n % 27 = 16 ∨
        n % 27 = 22 ∨ n % 27 = 25 := by omega
    rcases hh with hh | hh | hh | hh | hh | hh <;> rw [hh] <;> decide +kernel
  have hne : numDerangements n ≠ 0 := fun h => h27 (h ▸ dvd_zero 27)
  have hLower := (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) hne).mp h9
  have hUpper : (numDerangements n).factorization 3 < 3 :=
    Nat.lt_of_not_ge fun h => h27 ((Nat.prime_three.pow_dvd_iff_le_factorization (k := 3) hne).mpr h)
  omega

theorem exponent_eq_two_mod_nine {n a k : ℕ} (hn : n % 9 = 4 ∨ n % 9 = 7)
    (hk : 1 < k) (heq : numDerangements n = a ^ k) : k = 2 := by
  have hval := three_factorization_mod_nine n hn
  rw [heq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hval
  have hdiv : k ∣ 2 := ⟨a.factorization 3, hval.symm⟩
  have hle := Nat.le_of_dvd (by decide : 0 < (2 : ℕ)) hdiv
  omega

end A000166

namespace OMA.R_oeis_a000166_R1

private theorem reduce_to_prime_exponent {a k : ℕ} (ha : 1 < a) (hk : 1 < k) :
    ∃ b p : ℕ, 1 < b ∧ p.Prime ∧ a ^ k = b ^ p := by
  obtain ⟨p, hp, q, hq⟩ := Nat.ne_one_iff_exists_prime_dvd.mp (ne_of_gt hk)
  have hqne : q ≠ 0 := by
    rintro rfl
    simp at hq
    omega
  refine ⟨a ^ q, p, Nat.one_lt_pow hqne ha, hp, ?_⟩
  rw [hq, ← pow_mul, Nat.mul_comm p q]


/-- The bounded portion verified by a modular power certificate. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 10000 →
    (∃ a k : ℕ, 1 < a ∧ 1 < k ∧ numDerangements n = a ^ k) → n = 4

/-- The remaining even indices at which a square can occur. -/
def H2 : Prop :=
  ∀ n a : ℕ, 10000 < n → Even n → (n % 8 = 4 ∨ n % 8 = 6) → 1 < a →
    (∀ p : ℕ, p ≤ 71 → p.Prime →
      p ∣ numDerangements (n % p) → p ^ 2 ∣ numDerangements (n % p ^ 2)) →
    (∀ p : ℕ, (p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29) →
      p ∣ n - 1 → p ^ 2 ∣ n - 1) →
    numDerangements n ≠ a ^ 2

/-- The remaining candidates with an odd prime exponent. -/
def H3 : Prop :=
  ∀ n a k : ℕ, 10000 < n → 1 < a → k.Prime → Odd k →
    (Odd n → n % 8 = 1 ∧ k ∣ (n - 1).factorization 2) →
    ¬ (n % 9 = 4 ∨ n % 9 = 7) →
    (∀ p : ℕ, p ≤ 71 → p.Prime →
      p ∣ numDerangements (n % p) → p ^ 2 ∣ numDerangements (n % p ^ 2)) →
    (∀ p : ℕ, (p = 2 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29) →
      p ∣ n - 1 → p ^ 2 ∣ n - 1) →
    numDerangements n ≠ a ^ k


/-- A prime exponent, the congruences on the index, and the local valuation
tests suffice for the unresolved range. -/
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a000166.main := by
  intro hSmall hSquare hOddPower
  refine ⟨A000166.fourth_term, ?_⟩
  intro n hn hpow
  by_cases hbound : n ≤ 10000
  · exact hSmall n hn hbound hpow
  obtain ⟨a, k, ha, hk, haeq⟩ := hpow
  obtain ⟨b, p, hb, hp, hpower⟩ := reduce_to_prime_exponent ha hk
  have heq := haeq.trans hpower
  have hLarge : 10000 < n := by omega
  have hResidues : ∀ q : ℕ, q ≤ 71 → q.Prime →
      q ∣ numDerangements (n % q) → q ^ 2 ∣ numDerangements (n % q ^ 2) := by
    intro q _ hq hqd
    by_contra hq2
    exact A000166.no_power_of_residue hq hp.one_lt hqd hq2 heq
  have hLinear : ∀ q : ℕ, (q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 17 ∨
      q = 19 ∨ q = 23 ∨ q = 29) → q ∣ n - 1 → q ^ 2 ∣ n - 1 := by
    intro q hq hqd
    by_contra hq2
    exact A000166.no_power_of_small_prime_exactly_once hn hp.one_lt hq hqd hq2 heq
  exfalso
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · rcases Nat.even_or_odd n with hne | hno
    · exact hSquare n b hLarge hne (A000166.even_index_square_mod_eight hn hne heq)
        hb hResidues hLinear heq
    · exact A000166.odd_index_not_square n hn hno ⟨b, heq⟩
  · have hOddIndex (hno : Odd n) : n % 8 = 1 ∧ p ∣ (n - 1).factorization 2 :=
      ⟨A000166.odd_index_power_mod_eight hn hno hp.one_lt heq,
        (A000166.odd_index_power_constraints hn hno heq).2⟩
    have hModNine : ¬ (n % 9 = 4 ∨ n % 9 = 7) := by
      intro h9
      have hp2 := A000166.exponent_eq_two_mod_nine h9 hp.one_lt heq
      exact (by decide : ¬ Odd (2 : ℕ)) (hp2 ▸ hpodd)
    exact hOddPower n b p hLarge hb hp hpodd hOddIndex hModNine hResidues hLinear heq

end OMA.R_oeis_a000166_R1
