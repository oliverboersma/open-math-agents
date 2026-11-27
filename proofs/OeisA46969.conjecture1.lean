import FormalConjectures.OEIS.«46969»
import Mathlib.NumberTheory.Basic

/-!
# OEIS A046969, Conjecture I

For primes `p > 3` and `q = 2 * p - 1`, the reduced denominator is exactly
`12 * q`. Von Staudt–Clausen gives the denominator of the Bernoulli number.
Faulhaber's formula and power sums modulo the squares of the two primes
determine which prime cancels in the Stirling coefficient.
-/

open Finset

namespace A046969Proof

private def IntegralAt (l : ℕ) (x : ℚ) : Prop := ¬ l ∣ x.den

private lemma integralAt_int {l : ℕ} (hl : l.Prime) (z : ℤ) :
    IntegralAt l (z : ℚ) := by
  simpa [IntegralAt] using hl.not_dvd_one

private lemma integralAt_nat {l : ℕ} (hl : l.Prime) (n : ℕ) :
    IntegralAt l (n : ℚ) := by
  simpa using integralAt_int hl (n : ℤ)

private lemma integralAt_mul {l : ℕ} (hl : l.Prime) {x y : ℚ}
    (hx : IntegralAt l x) (hy : IntegralAt l y) : IntegralAt l (x * y) := by
  intro h
  exact (hl.dvd_mul.mp (h.trans (Rat.mul_den_dvd x y))).elim hx hy

private lemma integralAt_sub {l : ℕ} (hl : l.Prime) {x y : ℚ}
    (hx : IntegralAt l x) (hy : IntegralAt l y) : IntegralAt l (x - y) := by
  intro h
  exact (hl.dvd_mul.mp (h.trans (Rat.sub_den_dvd x y))).elim hx hy

private lemma integralAt_sum {ι : Type*} {l : ℕ} (hl : l.Prime) (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, IntegralAt l (f i)) : IntegralAt l (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using integralAt_int hl 0
  | insert i s hi ih =>
    rw [sum_insert hi]
    intro hd
    rcases hl.dvd_mul.mp (hd.trans (Rat.add_den_dvd _ _)) with hd | hd
    · exact h i (mem_insert_self _ _) hd
    · exact ih (fun j hj => h j (mem_insert_of_mem hj)) hd

private lemma integralAt_one_div {l n : ℕ} (hn : n ≠ 0) (h : ¬ l ∣ n) :
    IntegralAt l ((1 : ℚ) / n) := by
  simpa [IntegralAt, one_div, hn] using h

-- Multiplying any Bernoulli number by the prime removes that prime from its denominator.
private lemma integralAt_mul_bernoulli {l : ℕ} (hl : l.Prime) (i : ℕ) :
    IntegralAt l ((l : ℚ) * bernoulli i) := by
  by_cases hi : Even i
  · obtain ⟨k, rfl⟩ := hi
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    rw [← two_mul] at ⊢
    let s := (range (2 * k + 2)).filter (fun t => t.Prime ∧ (t - 1) ∣ 2 * k)
    change (z : ℚ) = bernoulli (2 * k) + ∑ t ∈ s, (1 : ℚ) / t at hz
    have hEq : (l : ℚ) * bernoulli (2 * k) =
        (l : ℚ) * z - ∑ t ∈ s, (l : ℚ) * (1 / t) := by
      rw [← Finset.mul_sum, hz]
      ring
    rw [hEq]
    refine integralAt_sub hl (integralAt_mul hl (integralAt_nat hl l) (integralAt_int hl z)) ?_
    apply integralAt_sum hl
    intro t ht
    have htP := (mem_filter.mp ht).2.1
    by_cases heq : t = l
    · subst t
      have hlq : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
      simpa [hlq] using integralAt_int hl 1
    · have hnd : ¬ l ∣ t := fun hd => heq (((Nat.dvd_prime htP).mp hd).resolve_left hl.ne_one).symm
      exact integralAt_mul hl (integralAt_nat hl l) (integralAt_one_div htP.ne_zero hnd)
  · have hodd : Odd i := Nat.not_even_iff_odd.mp hi
    by_cases h1 : i = 1
    · subst i
      rw [bernoulli_one]
      by_cases hl2 : l = 2
      · subst l
        norm_num [IntegralAt]
      · have hEq : (l : ℚ) * (-1 / 2) = ((-(l : ℤ) : ℤ) : ℚ) * (1 / 2) := by
          push_cast
          ring
        rw [hEq]
        exact integralAt_mul hl (integralAt_int hl (-(l : ℤ)))
          (integralAt_one_div (n := 2) (by decide) (fun hd =>
            hl2 (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hl.ne_one)))
    · have hi1 : 1 < i := by obtain ⟨k, hk⟩ := hodd; omega
      rw [bernoulli_eq_zero_of_odd hodd hi1, mul_zero]
      simpa using integralAt_int hl 0

private def powerSum (l m : ℕ) : ℤ := ∑ a ∈ range l, (a : ℤ) ^ m

-- In Faulhaber's expansion all terms below the leading Bernoulli term contain
-- two powers of l after allowing one power for the Bernoulli denominator.
private lemma faulhaber_remainder {l m : ℕ} (hl : l.Prime)
    (hm : Even m) (hm4 : 4 ≤ m) (hnd : ¬ l ∣ m + 1) :
    ∃ X : ℚ, IntegralAt l X ∧
      (powerSum l m : ℚ) = (l : ℚ) * bernoulli m + (l : ℚ) ^ 2 * X := by
  let term (i : ℕ) : ℚ :=
    ((l : ℚ) * bernoulli i) * ((m + 1).choose i : ℚ) *
      (l : ℚ) ^ (m - 2 - i) * (1 / ((m + 1 : ℕ) : ℚ))
  refine ⟨∑ i ∈ range (m - 1), term i, integralAt_sum hl _ _ ?_, ?_⟩
  · intro i _
    refine integralAt_mul hl (integralAt_mul hl (integralAt_mul hl ?_ ?_) ?_) ?_
    · exact integralAt_mul_bernoulli hl i
    · exact integralAt_nat hl _
    · simpa only [Nat.cast_pow] using integralAt_nat hl (l ^ (m - 2 - i))
    · exact integralAt_one_div (Nat.succ_ne_zero m) hnd
  · simp only [powerSum, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
    rw [sum_range_pow, Finset.sum_range_succ]
    have hmain : bernoulli m * ((m + 1).choose m : ℚ) *
        (l : ℚ) ^ (m + 1 - m) / (m + 1) = (l : ℚ) * bernoulli m := by
      rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, pow_one]
      have hm0 : (m : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [hm0]
    rw [hmain, add_comm, Finset.mul_sum]
    rw [show range m = range (m - 1 + 1) from congrArg range (by omega), Finset.sum_range_succ]
    have hodd : Odd (m - 1) := by
      obtain ⟨k, hk⟩ := hm
      exact ⟨k - 1, by omega⟩
    rw [bernoulli_eq_zero_of_odd hodd (by omega), zero_mul, zero_mul, zero_div, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have he : m + 1 - i = 2 + 1 + (m - 2 - i) := by omega
    rw [he, pow_add, pow_add, pow_one]
    simp only [term, Nat.cast_add, Nat.cast_one]
    ring

private lemma dvd_of_integralAt_div_sq {l : ℕ} (hl : l.Prime) (z : ℤ)
    (h : IntegralAt l ((z : ℚ) / (l : ℚ) ^ 2)) : (l : ℤ) ^ 2 ∣ z := by
  have hl0 : (l : ℤ) ^ 2 ≠ 0 := by exact pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have hden : ((z : ℚ) / (l : ℚ) ^ 2).den ∣ l ^ 2 := by
    have hd := Rat.den_dvd z ((l : ℤ) ^ 2)
    rw [Rat.divInt_eq_div] at hd
    push_cast at hd
    exact Int.natCast_dvd_natCast.mp (mod_cast hd)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hl).mp hden
  have hk0 : k = 0 := by
    by_contra hn
    exact h (hk ▸ dvd_pow_self l hn)
  have hone : ((z : ℚ) / (l : ℚ) ^ 2).den = 1 := by simp [hk, hk0]
  apply (Rat.den_div_intCast_eq_one_iff z _ hl0).mp
  push_cast
  exact hone

private lemma faulhaber_dvd {l m : ℕ} (hl : l.Prime)
    (hm : Even m) (hm4 : 4 ≤ m) (hnd : ¬ l ∣ m + 1)
    {N : ℤ} (hN : bernoulli m = (N : ℚ) / 6) :
    (l : ℤ) ^ 2 ∣ 6 * powerSum l m - l * N := by
  obtain ⟨X, hX, hS⟩ := faulhaber_remainder hl hm hm4 hnd
  apply dvd_of_integralAt_div_sq hl
  have hl0 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hEq : ((6 * powerSum l m - l * N : ℤ) : ℚ) / (l : ℚ) ^ 2 = 6 * X := by
    push_cast
    rw [hS, hN]
    field_simp [hl0]
    ring
  rw [hEq]
  exact integralAt_mul hl (integralAt_nat hl 6) hX

private lemma int_dvd_iff_zmod (l : ℕ) (z : ℤ) :
    (l : ℤ) ∣ z ↔ (z : ZMod l) = 0 := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z l).symm

private lemma powerSum_double_prime {l : ℕ} (hl : l.Prime) (hl3 : 3 < l) :
    (l : ℤ) ^ 2 ∣ powerSum l (2 * l) := by
  let : Fact l.Prime := ⟨hl⟩
  have hl0 : 0 < l := hl.pos
  let f (a : ℕ) := (2 * a) % l
  have hmap : ∀ a ∈ range l, f a ∈ range l :=
    fun a _ => mem_range.mpr (Nat.mod_lt (2 * a) hl0)
  have hTwo : (2 : ZMod l) ≠ 0 := by
    exact mt (ZMod.natCast_eq_zero_iff 2 l).mp (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hinj : ∀ a ∈ range l, ∀ b ∈ range l, f a = f b → a = b := by
    intro a ha b hb hab
    have hcast : (2 : ZMod l) * (a : ZMod l) = 2 * (b : ZMod l) := by
      simpa [f, Nat.cast_mul, ZMod.natCast_mod] using congrArg (fun n : ℕ => (n : ZMod l)) hab
    have hab' := mul_left_cancel₀ hTwo hcast
    simpa [ZMod.val_cast_of_lt (mem_range.mp ha), ZMod.val_cast_of_lt (mem_range.mp hb)]
      using congrArg ZMod.val hab'
  have himage : (range l).image f = range l := by
    apply Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
    rw [Finset.card_image_of_injOn hinj]
  have hperm : (∑ a ∈ range l, (f a : ℤ) ^ (2 * l)) = powerSum l (2 * l) := by
    calc
      _ = ∑ a ∈ (range l).image f, (a : ℤ) ^ (2 * l) := (Finset.sum_image hinj).symm
      _ = _ := by rw [himage, powerSum]
  have hterm (a : ℕ) : (l : ℤ) ^ 2 ∣ (2 * (a : ℤ)) ^ (2 * l) - (f a : ℤ) ^ (2 * l) := by
    have hbase : (l : ℤ) ∣ 2 * (a : ℤ) - (f a : ℤ) := by
      rw [int_dvd_iff_zmod l]
      push_cast
      simp [f, ZMod.natCast_mod, Nat.cast_mul]
    have hpow : (l : ℤ) ^ 2 ∣ (2 * (a : ℤ)) ^ l - (f a : ℤ) ^ l := by
      simpa using dvd_sub_pow_of_dvd_sub hbase 1
    rw [Nat.mul_comm 2 l, pow_mul, pow_mul]
    exact hpow.trans (sub_dvd_pow_sub_pow _ _ _)
  have hsum := Finset.dvd_sum (s := range l) fun a _ => hterm a
  rw [Finset.sum_sub_distrib, hperm] at hsum
  simp only [mul_pow, ← Finset.mul_sum] at hsum
  change (l : ℤ) ^ 2 ∣ (2 : ℤ) ^ (2 * l) * powerSum l (2 * l) - powerSum l (2 * l) at hsum
  have hd : (l : ℤ) ^ 2 ∣ ((4 : ℤ) ^ l - 1) * powerSum l (2 * l) := by
    rw [show (4 : ℤ) ^ l = 2 ^ (2 * l) by rw [pow_mul]; norm_num]
    rwa [sub_mul, one_mul]
  have hnd : ¬ (l : ℤ) ∣ (4 : ℤ) ^ l - 1 := by
    intro h
    have hcast := (int_dvd_iff_zmod l _).mp h
    push_cast at hcast
    rw [ZMod.pow_card] at hcast
    have hthree : (3 : ZMod l) = 0 := by norm_num [show (4 : ZMod l) - 1 = 3 by ring] at hcast ⊢; exact hcast
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hl3 ((ZMod.natCast_eq_zero_iff 3 l).mp hthree)
  have hcop : Nat.Coprime ((4 : ℤ) ^ l - 1).natAbs (l ^ 2) :=
    ((hl.coprime_iff_not_dvd.mpr (fun h => hnd (Int.natAbs_dvd_natAbs.mp (by simpa using h)))).symm).pow_right _
  apply Int.natAbs_dvd_natAbs.mp
  have hd' := Int.natAbs_dvd_natAbs.mpr hd
  simp only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] at hd' ⊢
  exact hcop.symm.dvd_of_dvd_mul_left hd'

private lemma six_mul_powerSum_two (l : ℕ) :
    6 * powerSum l 2 = (l : ℤ) * ((l : ℤ) - 1) * (2 * (l : ℤ) - 1) := by
  induction l with
  | zero => simp [powerSum]
  | succ l ih =>
    simp only [powerSum, sum_range_succ, Nat.cast_succ] at ih ⊢
    linarith only [ih, show (6 : ℤ) * ((l : ℤ) ^ 2) =
      ((l : ℤ) + 1) * ((l : ℤ) + 1 - 1) * (2 * ((l : ℤ) + 1) - 1) -
        (l : ℤ) * ((l : ℤ) - 1) * (2 * (l : ℤ) - 1) by ring]

private lemma powerSum_prime_succ {l : ℕ} (hl : l.Prime) (hl3 : 3 < l) :
    (l : ℤ) ^ 2 ∣ 12 * powerSum l (l + 1) - l := by
  let : Fact l.Prime := ⟨hl⟩
  have hterm (a : ℕ) : (l : ℤ) ^ 2 ∣
      (a : ℤ) ^ (2 * l) - 2 * (a : ℤ) ^ (l + 1) + (a : ℤ) ^ 2 := by
    have ha : (l : ℤ) ∣ (a : ℤ) ^ l - a := by
      rw [int_dvd_iff_zmod l]
      push_cast
      rw [ZMod.pow_card, sub_self]
    have heq : (a : ℤ) ^ (2 * l) - 2 * (a : ℤ) ^ (l + 1) + (a : ℤ) ^ 2 =
        ((a : ℤ) ^ l - a) ^ 2 := by
      rw [Nat.mul_comm 2 l, pow_mul, pow_succ]
      ring
    rw [heq]
    exact pow_dvd_pow_of_dvd ha _
  have hsum := Finset.dvd_sum (s := range l) fun a _ => hterm a
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  change (l : ℤ) ^ 2 ∣ powerSum l (2 * l) - 2 * powerSum l (l + 1) + powerSum l 2 at hsum
  have hdouble := powerSum_double_prime hl hl3
  have hdiff : (l : ℤ) ^ 2 ∣ 2 * powerSum l (l + 1) - powerSum l 2 := by
    have heq : 2 * powerSum l (l + 1) - powerSum l 2 =
        powerSum l (2 * l) -
          (powerSum l (2 * l) - 2 * powerSum l (l + 1) + powerSum l 2) := by ring
    rw [heq]
    exact dvd_sub hdouble hsum
  have htwo : (l : ℤ) ^ 2 ∣ 6 * powerSum l 2 - l := by
    rw [six_mul_powerSum_two]
    exact ⟨2 * (l : ℤ) - 3, by ring⟩
  have heq : 12 * powerSum l (l + 1) - l =
      6 * (2 * powerSum l (l + 1) - powerSum l 2) + (6 * powerSum l 2 - l) := by ring
  rw [heq]
  exact dvd_add (dvd_mul_of_dvd_right hdiff 6) htwo


private lemma small_not_dvd_prime {r p : ℕ} (hp : p.Prime) (hr : 1 < r)
    (hrp : r < p) : ¬ r ∣ p := by
  intro h
  rcases (Nat.dvd_prime hp).mp h with h | h <;> omega

private lemma bernoulli_num {p : ℕ} (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hp3 : 3 < p) : ∃ z : ℤ, bernoulli (2 * p) = ((6 * z - 5 : ℤ) : ℚ) / 6 := by
  have h3p := small_not_dvd_prime hp (r := 3) (by decide) hp3
  have h3q := small_not_dvd_prime hq (r := 3) (by decide) (by omega)
  have hqmod : (2 * p - 1) % 3 ≠ 0 := fun h =>
    h3q (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hnotp1 : ¬ (p + 1).Prime := by
    intro h
    have h2p := small_not_dvd_prime hp (r := 2) (by decide) (by omega)
    exact small_not_dvd_prime h (r := 2) (by decide) (by omega) (by omega)
  have hnot2p1 : ¬ (2 * p + 1).Prime := by
    intro h
    have hmod : p % 3 = 1 := by
      have hpmod : p % 3 ≠ 0 := fun h => h3p (Nat.dvd_iff_mod_eq_zero.mpr h)
      have hcast : (↑(2 * p - 1) : ℤ) = 2 * (p : ℤ) - 1 := by omega
      have hmod' : ((2 * (p : ℤ) - 1) % 3) ≠ 0 := by
        rw [← hcast]
        exact_mod_cast hqmod
      omega
    exact small_not_dvd_prime h (r := 3) (by decide) (by omega) (by omega)
  have hfilter :
      (range (2 * p + 2)).filter (fun t => t.Prime ∧ (t - 1) ∣ 2 * p) =
        {2, 3} := by
    ext t
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, ht, hd⟩
      obtain ⟨u, v, hu, hv, huv⟩ := Nat.dvd_mul.mp hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hu with hu | hu <;>
        rcases (Nat.dvd_prime hp).mp hv with hv | hv <;> subst u <;> subst v <;>
        (try simp only [one_mul, mul_one] at huv)
      · left
        have := ht.two_le
        omega
      · exfalso
        exact hnotp1 (by convert ht using 1; have := ht.two_le; omega)
      · right
        omega
      · exfalso
        exact hnot2p1 (by convert ht using 1; have := ht.two_le; omega)
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.prime_two, one_dvd _⟩
      · exact ⟨by omega, Nat.prime_three, dvd_mul_right 2 p⟩
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen p
  rw [hfilter, Finset.sum_insert (by decide), Finset.sum_singleton] at hz
  refine ⟨z, ?_⟩
  push_cast
  norm_num at hz ⊢
  linarith

private lemma cancel_prime_from_square {l : ℕ} (hl : l.Prime) (z : ℤ)
    (h : (l : ℤ) ^ 2 ∣ (l : ℤ) * z) : (l : ℤ) ∣ z := by
  rw [pow_two] at h
  exact (Int.mul_dvd_mul_iff_left (by exact_mod_cast hl.ne_zero)).mp h

private lemma stirling_denominator {p : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp3 : 3 < p) :
    OeisA46969.a p = 12 * (2 * p - 1) := by
  let q := 2 * p - 1
  have hq3 : 3 < q := by dsimp [q]; omega
  have hm4 : 4 ≤ 2 * p := by omega
  have hm : Even (2 * p) := ⟨p, by omega⟩
  obtain ⟨z, hz⟩ := bernoulli_num hp hq hp3
  let N : ℤ := 6 * z - 5
  have hpnd : ¬ p ∣ 2 * p + 1 := by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_left p 2)).mpr h)
  have hqnd : ¬ q ∣ 2 * p + 1 := by
    intro h
    rw [show 2 * p + 1 = q + 2 by dsimp [q]; omega] at h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < q)
      ((Nat.dvd_add_iff_right (dvd_refl q)).mpr h)
  have hpFaul := faulhaber_dvd hp hm hm4 hpnd (N := N) hz
  have hqFaul := faulhaber_dvd hq hm hm4 hqnd (N := N) hz
  have hpN : (p : ℤ) ∣ N := by
    apply cancel_prime_from_square hp
    have h := dvd_sub (dvd_mul_of_dvd_right (powerSum_double_prime hp hp3) (6 : ℤ)) hpFaul
    have heq : (p : ℤ) * N = 6 * powerSum p (2 * p) -
        (6 * powerSum p (2 * p) - p * N) := by ring
    rw [heq]
    exact h
  have hqN : ¬ (q : ℤ) ∣ N := by
    have hqm : q + 1 = 2 * p := by dsimp [q]; omega
    have hsum := powerSum_prime_succ hq hq3
    rw [hqm] at hsum
    have hdiff := dvd_sub (dvd_mul_of_dvd_right hqFaul (2 : ℤ)) hsum
    have hqDiff : (q : ℤ) ∣ 1 - 2 * N := by
      apply cancel_prime_from_square hq
      have heq : (q : ℤ) * (1 - 2 * N) =
          2 * (6 * powerSum q (2 * p) - q * N) -
            (12 * powerSum q (2 * p) - q) := by ring
      rw [heq]
      exact hdiff
    intro h
    have hone : (q : ℤ) ∣ 1 := by
      have heq : (1 - 2 * N) + 2 * N = 1 := by ring
      rw [← heq]
      exact dvd_add hqDiff (dvd_mul_of_dvd_right h 2)
    exact hq.not_dvd_one (by exact_mod_cast hone)
  obtain ⟨N', hN⟩ := hpN
  have h2 : ¬ (2 : ℤ) ∣ N := by dsimp [N]; omega
  have h3 : ¬ (3 : ℤ) ∣ N := by dsimp [N]; omega
  have hcop2 : N'.natAbs.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr
    (fun h => h2 (hN ▸ dvd_mul_of_dvd_right (Int.natCast_dvd.mpr h) (p : ℤ)))).symm
  have hcop3 : N'.natAbs.Coprime 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr
    (fun h => h3 (hN ▸ dvd_mul_of_dvd_right (Int.natCast_dvd.mpr h) (p : ℤ)))).symm
  have hcopq : N'.natAbs.Coprime q := (hq.coprime_iff_not_dvd.mpr
    (fun h => hqN (hN ▸ dvd_mul_of_dvd_right (Int.natCast_dvd.mpr h) (p : ℤ)))).symm
  have hcop : N'.natAbs.Coprime (12 * q) := (show N'.natAbs.Coprime (2 ^ 2 * 3)
    from (hcop2.pow_right 2).mul_right hcop3).mul_right hcopq
  have hrat : bernoulli (2 * p) / (((2 * p * q : ℕ)) : ℚ) =
      (N' : ℚ) / (((12 * q : ℕ) : ℤ) : ℚ) := by
    rw [hz, ← show N = 6 * z - 5 from rfl, hN]
    have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hqq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    push_cast
    field_simp [hpq, hqq]
    ring
  have hden := Rat.den_div_eq_of_coprime
    (a := N') (b := ((12 * q : ℕ) : ℤ)) (by positivity)
    (by simpa only [Int.natAbs_natCast] using hcop)
  rw [OeisA46969.a, if_neg hp.ne_zero]
  change (bernoulli (2 * p) / (((2 * p * q : ℕ)) : ℚ)).den = 12 * q
  rw [hrat]
  exact_mod_cast hden

end A046969Proof

theorem OMA.solution : type_of% @OeisA46969.conjecture1 := by
  intro p hp hq hp3
  rw [A046969Proof.stirling_denominator hp hq hp3, Nat.mul_comm, Nat.mul_div_cancel _ (by decide)]
  exact hq
