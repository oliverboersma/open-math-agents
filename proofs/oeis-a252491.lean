import OMAStatements.S_oeis_a252491
import Mathlib

namespace OMA.A252491Proof

open Finset

lemma key (y n : ℕ) (hy : 1 ≤ y) : (∑ i ∈ range n, y ^ i) * (y - 1) = y ^ n - 1 := by
  have := geom_sum_mul_add (y - 1) n
  rw [Nat.sub_add_cancel hy] at this
  omega

lemma sum_dvd (y a b : ℕ) (hy : 2 ≤ y) (hab : a ∣ b) :
    (∑ i ∈ range a, y ^ i) ∣ (∑ i ∈ range b, y ^ i) := by
  have h : (∑ i ∈ range a, y ^ i) * (y - 1) ∣ (∑ i ∈ range b, y ^ i) * (y - 1) := by
    rw [key y a (by omega), key y b (by omega)]
    exact Nat.pow_sub_one_dvd_pow_sub_one y hab
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h

lemma sum_lt (y a b : ℕ) (hy : 1 ≤ y) (hab : a < b) :
    (∑ i ∈ range a, y ^ i) < (∑ i ∈ range b, y ^ i) := by
  apply Finset.sum_lt_sum_of_subset (i := a)
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · simpa using hab
  · simp
  · positivity
  · intro _ _ _
    exact Nat.zero_le _

lemma one_lt (y n : ℕ) (hy : 1 ≤ y) (hn : 2 ≤ n) : 1 < ∑ i ∈ range n, y ^ i := by
  have := sum_lt y 1 n hy (by omega)
  simpa using this

lemma coprime_dvd (p q : ℕ) (hpq : Nat.Coprime p q) :
    (∑ i ∈ range q, 10 ^ i) ∣ (∑ i ∈ range q, (10 ^ p) ^ i) := by
  have hM := key 10 q (by norm_num)
  have hP := key 10 p (by norm_num)
  have hS := key (10 ^ p) q (Nat.one_le_pow _ _ (by norm_num))
  have hd : 10 ^ q - 1 ∣ 10 ^ (p * q) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 10 (dvd_mul_left q p)
  rw [pow_mul, ← hS, ← hM, ← hP] at hd
  norm_num at hd
  have h1 : (∑ i ∈ range q, 10 ^ i) ∣
      (∑ i ∈ range q, (10 ^ p) ^ i) * (∑ i ∈ range p, 10 ^ i) := by
    apply Nat.dvd_of_mul_dvd_mul_right (show 0 < 9 by norm_num)
    rw [mul_assoc]
    exact hd
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 10 q p
  rw [Nat.gcd_comm q p, hpq, ← hM, ← hP] at hg
  norm_num at hg
  rw [Nat.gcd_mul_right] at hg
  have hc : Nat.Coprime (∑ i ∈ range q, 10 ^ i) (∑ i ∈ range p, 10 ^ i) := by
    unfold Nat.Coprime
    omega
  exact hc.dvd_of_dvd_mul_right h1

lemma small_lt (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (∑ i ∈ range q, 10 ^ i) < (∑ i ∈ range q, (10 ^ p) ^ i) := by
  have h100 : 10 ^ 2 ≤ 10 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  apply Finset.sum_lt_sum
  · intro i _
    exact Nat.pow_le_pow_left (by norm_num at h100 ⊢; omega) i
  · refine ⟨1, by simp; omega, ?_⟩
    norm_num at h100 ⊢
    omega

lemma not_prime (p q : ℕ) (hp : p.Prime) (ha : ¬ (OMA.S_oeis_a252491.a p).Prime)
    (hq : 2 ≤ q) : ¬ (∑ i ∈ range q, (10 ^ p) ^ i).Prime := by
  have hp2 := hp.two_le
  have hx : 2 ≤ 10 ^ p := by
    have : 10 ^ 1 ≤ 10 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  intro hpr
  by_cases hpq : p ∣ q
  · obtain ⟨m, rfl⟩ := hpq
    rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h
    · subst h; simp at hq
    · subst h
      apply ha
      unfold OMA.S_oeis_a252491.a
      rw [sq, pow_mul, ← Nat.geomSum_eq hx]
      simpa using hpr
    · have d := sum_dvd (10 ^ p) p (p * m) hx (dvd_mul_right p m)
      rcases hpr.eq_one_or_self_of_dvd _ d with h1 | h1
      · have := one_lt (10 ^ p) p (by omega) hp2
        omega
      · have := sum_lt (10 ^ p) p (p * m) (by omega) (by nlinarith)
        omega
  · have hc : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    have d := coprime_dvd p q hc
    rcases hpr.eq_one_or_self_of_dvd _ d with h1 | h1
    · have := one_lt 10 q (by norm_num) hq
      omega
    · have := small_lt p q hp2 hq
      omega

lemma digits_len (p : ℕ) (hp : 1 ≤ p) : (Nat.digits 10 (10 ^ (p - 1))).length = p := by
  rw [Nat.digits_len 10 _ (by norm_num) (by positivity), Nat.log_pow (by norm_num)]
  omega

lemma candidate (p r : ℕ) (hp : 1 ≤ p) :
    10 ^ (p - 1) * (∑ i ∈ range r, (10 ^ p) ^ i) * 10 + 1 =
      ∑ i ∈ range (r + 1), (10 ^ p) ^ i := by
  rw [Finset.sum_range_succ']
  have h : 10 ^ (p - 1) * 10 = 10 ^ p := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [pow_succ, ← Finset.sum_mul, pow_zero]
  rw [mul_comm (10 ^ (p - 1)), mul_assoc, h]

end OMA.A252491Proof

open OMA.A252491Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a252491.main := by
  intro p hp ha
  have hp1 : 1 ≤ p := hp.one_lt.le
  unfold OMA.S_oeis_a252491.repetitionCount
  rw [if_neg (by positivity), digits_len p hp1]
  convert Nat.sInf_empty
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hr hprime
  rw [candidate p r hp1] at hprime
  exact not_prime p (r + 1) hp ha (by omega) hprime
