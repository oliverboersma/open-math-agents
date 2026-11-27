import OMAReductions.R_Erdos384_erdos_384_R1_H2_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic

/-!
# Proof of Erdos 384 Case 3 (R1.H2.R1.H4)

This file proves `OMA.R_Erdos384_erdos_384_R1_H2_R1.H4`: for all `n k : ℕ` with `60 ≤ k` and
`2 * k ≤ n < 16 * k`, there exists a prime `p` dividing `n.choose k` with `2 * p ≤ n`.
-/

namespace Erdos384H4Proof

open scoped BigOperators Classical

/- ## Section 1: Prime Powers in Factorials and Bounded-Range Prime Ladders -/

lemma prime_sq_dvd_two_mul_factorial {p : ℕ} (hp : p.Prime) :
    p ^ 2 ∣ (2 * p).factorial := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : 2 * p = (2 * p - 1) + 1 := by omega
  rw [h1, Nat.factorial_succ, ← h1, sq]
  have hdvd1 : p ∣ 2 * p := dvd_mul_left p 2
  have hdvd2 : p ∣ (2 * p - 1).factorial := Nat.dvd_factorial hp.pos (by omega)
  exact mul_dvd_mul hdvd1 hdvd2

lemma prime_cube_dvd_three_mul_factorial {p : ℕ} (hp : p.Prime) :
    p ^ 3 ∣ (3 * p).factorial := by
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : 3 * p = (3 * p - 1) + 1 := by omega
  rw [h1, Nat.factorial_succ, ← h1]
  have hdvd1 : p ∣ 3 * p := dvd_mul_left p 3
  have hdvd2 : p ^ 2 ∣ (3 * p - 1).factorial :=
    dvd_trans (prime_sq_dvd_two_mul_factorial hp) (Nat.factorial_dvd_factorial (by omega))
  have hpow : p ^ 3 = p * p ^ 2 := by ring
  rw [hpow]
  exact mul_dvd_mul hdvd1 hdvd2

lemma not_prime_sq_dvd_factorial_of_lt_two_mul {p m : ℕ} (hp : p.Prime) (hm : m < 2 * p) :
    ¬ (p ^ 2 ∣ m.factorial) := by
  induction m with
  | zero =>
    intro hdvd
    have hle : p ^ 2 ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  | succ m ih =>
    intro hdvd
    rw [Nat.factorial_succ] at hdvd
    by_cases hmp : m + 1 = p
    · rw [hmp, sq] at hdvd
      have hdvd' : p ∣ m.factorial := (mul_dvd_mul_iff_left hp.pos.ne').mp hdvd
      have hndvd : ¬ (p ∣ m.factorial) := mt hp.dvd_factorial.mp (by omega)
      exact hndvd hdvd'
    · have hndvd_m1 : ¬ (p ∣ m + 1) := by
        rintro ⟨c, hc⟩
        rcases eq_or_ne c 0 with rfl | hc0
        · omega
        · rcases eq_or_ne c 1 with rfl | hc1
          · omega
          · have hc2 : 2 ≤ c := by omega
            have hge : 2 * p ≤ p * c := by nlinarith
            omega
      have hcop : Nat.Coprime (p ^ 2) (m + 1) := (hp.coprime_iff_not_dvd.mpr hndvd_m1).pow_left 2
      exact ih (by omega) (hcop.dvd_of_dvd_mul_left hdvd)

lemma dvd_choose_of_gt_and_lt_two_mul {n k p : ℕ} (hp : p.Prime)
    (hkp : k < p) (hsub : n - k < 2 * p) (h2p : 2 * p ≤ n) :
    p ∣ n.choose k := by
  by_contra hndvd
  have hkn : k ≤ n := by omega
  have hfac : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkn
  have hdvd_n : p ^ 2 ∣ n.factorial :=
    dvd_trans (prime_sq_dvd_two_mul_factorial hp) (Nat.factorial_dvd_factorial h2p)
  rw [← hfac] at hdvd_n
  have hndvd_k : ¬ (p ∣ k.factorial) := mt hp.dvd_factorial.mp (by omega)
  have hndvd_prod : ¬ (p ∣ n.choose k * k.factorial) := by
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact hndvd h1
    · exact hndvd_k h2
  have hcop : Nat.Coprime (p ^ 2) (n.choose k * k.factorial) :=
    (hp.coprime_iff_not_dvd.mpr hndvd_prod).pow_left 2
  have hdvd_nk : p ^ 2 ∣ (n - k).factorial := hcop.dvd_of_dvd_mul_left hdvd_n
  exact not_prime_sq_dvd_factorial_of_lt_two_mul hp hsub hdvd_nk

lemma prime_sq_dvd_or_of_cube_dvd_mul {p a b : ℕ} (hp : p.Prime) (h : p ^ 3 ∣ a * b) :
    p ^ 2 ∣ a ∨ p ^ 2 ∣ b := by
  by_cases hpa : p ∣ a
  · obtain ⟨a', rfl⟩ := hpa
    have h2 : p ^ 2 ∣ a' * b := by
      have hrw : p ^ 3 = p * p ^ 2 := by ring
      have hmul : p * p ^ 2 ∣ p * (a' * b) := by
        rw [← hrw, ← mul_assoc]
        exact h
      exact (mul_dvd_mul_iff_left hp.pos.ne').mp hmul
    by_cases hpa' : p ∣ a'
    · obtain ⟨a'', rfl⟩ := hpa'
      exact Or.inl ⟨a'', by ring⟩
    · have hcop : Nat.Coprime (p ^ 2) a' := (hp.coprime_iff_not_dvd.mpr hpa').pow_left 2
      exact Or.inr (hcop.dvd_of_dvd_mul_left h2)
  · have hcop : Nat.Coprime (p ^ 3) a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left 3
    have hb3 : p ^ 3 ∣ b := hcop.dvd_of_dvd_mul_left h
    exact Or.inr (dvd_trans ⟨p, by ring⟩ hb3)

lemma dvd_choose_of_lt_two_mul_and_three_mul_le {n k p : ℕ} (hp : p.Prime)
    (hk2p : k < 2 * p) (hsub : n - k < 2 * p) (h3p : 3 * p ≤ n) :
    p ∣ n.choose k := by
  by_contra hndvd
  have hkn : k ≤ n := by omega
  have hfac : n.choose k * (k.factorial * (n - k).factorial) = n.factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hkn
  have hdvd_n : p ^ 3 ∣ n.factorial :=
    dvd_trans (prime_cube_dvd_three_mul_factorial hp) (Nat.factorial_dvd_factorial h3p)
  rw [← hfac] at hdvd_n
  have hcop : Nat.Coprime (p ^ 3) (n.choose k) := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left 3
  have hdvd_prod : p ^ 3 ∣ k.factorial * (n - k).factorial := hcop.dvd_of_dvd_mul_left hdvd_n
  rcases prime_sq_dvd_or_of_cube_dvd_mul hp hdvd_prod with hk_sq | hnk_sq
  · exact not_prime_sq_dvd_factorial_of_lt_two_mul hp hk2p hk_sq
  · exact not_prime_sq_dvd_factorial_of_lt_two_mul hp hsub hnk_sq

lemma step87 {x : ℕ} (q : ℕ) {p : ℕ} (hp : p.Prime) (hcov : 7 * p ≤ 8 * q)
    (ih : x < q → ∃ r : ℕ, r.Prime ∧ x < r ∧ 7 * r ≤ 8 * x) (hx : x < p) :
    ∃ r : ℕ, r.Prime ∧ x < r ∧ 7 * r ≤ 8 * x := by
  by_cases hxq : x < q
  · exact ih hxq
  · exact ⟨p, hp, hx, by omega⟩

lemma step1615 {x : ℕ} (q : ℕ) {p : ℕ} (hp : p.Prime) (hcov : 15 * p ≤ 16 * q)
    (ih : x < q → ∃ r : ℕ, r.Prime ∧ x < r ∧ 15 * r ≤ 16 * x) (hx : x < p) :
    ∃ r : ℕ, r.Prime ∧ x < r ∧ 15 * r ≤ 16 * x := by
  by_cases hxq : x < q
  · exact ih hxq
  · exact ⟨p, hp, hx, by omega⟩

lemma ladder87 {x : ℕ} (hx1 : 37 ≤ x) (hx2 : x < 18503) :
    ∃ r : ℕ, r.Prime ∧ x < r ∧ 7 * r ≤ 8 * x := by
  revert hx2
  refine step87 16193 (p := 18503) (by norm_num1) (by norm_num1) ?_
  refine step87 14177 (p := 16193) (by norm_num1) (by norm_num1) ?_
  refine step87 12413 (p := 14177) (by norm_num1) (by norm_num1) ?_
  refine step87 10867 (p := 12413) (by norm_num1) (by norm_num1) ?_
  refine step87 9511 (p := 10867) (by norm_num1) (by norm_num1) ?_
  refine step87 8329 (p := 9511) (by norm_num1) (by norm_num1) ?_
  refine step87 7297 (p := 8329) (by norm_num1) (by norm_num1) ?_
  refine step87 6389 (p := 7297) (by norm_num1) (by norm_num1) ?_
  refine step87 5591 (p := 6389) (by norm_num1) (by norm_num1) ?_
  refine step87 4909 (p := 5591) (by norm_num1) (by norm_num1) ?_
  refine step87 4297 (p := 4909) (by norm_num1) (by norm_num1) ?_
  refine step87 3769 (p := 4297) (by norm_num1) (by norm_num1) ?_
  refine step87 3299 (p := 3769) (by norm_num1) (by norm_num1) ?_
  refine step87 2887 (p := 3299) (by norm_num1) (by norm_num1) ?_
  refine step87 2531 (p := 2887) (by norm_num1) (by norm_num1) ?_
  refine step87 2221 (p := 2531) (by norm_num1) (by norm_num1) ?_
  refine step87 1951 (p := 2221) (by norm_num1) (by norm_num1) ?_
  refine step87 1723 (p := 1951) (by norm_num1) (by norm_num1) ?_
  refine step87 1511 (p := 1723) (by norm_num1) (by norm_num1) ?_
  refine step87 1327 (p := 1511) (by norm_num1) (by norm_num1) ?_
  refine step87 1171 (p := 1327) (by norm_num1) (by norm_num1) ?_
  refine step87 1033 (p := 1171) (by norm_num1) (by norm_num1) ?_
  refine step87 907 (p := 1033) (by norm_num1) (by norm_num1) ?_
  refine step87 797 (p := 907) (by norm_num1) (by norm_num1) ?_
  refine step87 701 (p := 797) (by norm_num1) (by norm_num1) ?_
  refine step87 619 (p := 701) (by norm_num1) (by norm_num1) ?_
  refine step87 547 (p := 619) (by norm_num1) (by norm_num1) ?_
  refine step87 479 (p := 547) (by norm_num1) (by norm_num1) ?_
  refine step87 421 (p := 479) (by norm_num1) (by norm_num1) ?_
  refine step87 373 (p := 421) (by norm_num1) (by norm_num1) ?_
  refine step87 331 (p := 373) (by norm_num1) (by norm_num1) ?_
  refine step87 293 (p := 331) (by norm_num1) (by norm_num1) ?_
  refine step87 257 (p := 293) (by norm_num1) (by norm_num1) ?_
  refine step87 227 (p := 257) (by norm_num1) (by norm_num1) ?_
  refine step87 199 (p := 227) (by norm_num1) (by norm_num1) ?_
  refine step87 179 (p := 199) (by norm_num1) (by norm_num1) ?_
  refine step87 157 (p := 179) (by norm_num1) (by norm_num1) ?_
  refine step87 139 (p := 157) (by norm_num1) (by norm_num1) ?_
  refine step87 127 (p := 139) (by norm_num1) (by norm_num1) ?_
  refine step87 113 (p := 127) (by norm_num1) (by norm_num1) ?_
  refine step87 101 (p := 113) (by norm_num1) (by norm_num1) ?_
  refine step87 89 (p := 101) (by norm_num1) (by norm_num1) ?_
  refine step87 83 (p := 89) (by norm_num1) (by norm_num1) ?_
  refine step87 73 (p := 83) (by norm_num1) (by norm_num1) ?_
  refine step87 67 (p := 73) (by norm_num1) (by norm_num1) ?_
  refine step87 59 (p := 67) (by norm_num1) (by norm_num1) ?_
  refine step87 53 (p := 59) (by norm_num1) (by norm_num1) ?_
  refine step87 47 (p := 53) (by norm_num1) (by norm_num1) ?_
  refine step87 43 (p := 47) (by norm_num1) (by norm_num1) ?_
  refine step87 41 (p := 43) (by norm_num1) (by norm_num1) ?_
  refine step87 37 (p := 41) (by norm_num1) (by norm_num1) ?_
  intro hx
  omega

lemma ladder1615 {x : ℕ} (hx1 : 149 ≤ x) (hx2 : x < 149839) :
    ∃ r : ℕ, r.Prime ∧ x < r ∧ 15 * r ≤ 16 * x := by
  revert hx2
  refine step1615 140477 (p := 149839) (by norm_num1) (by norm_num1) ?_
  refine step1615 131707 (p := 140477) (by norm_num1) (by norm_num1) ?_
  refine step1615 123479 (p := 131707) (by norm_num1) (by norm_num1) ?_
  refine step1615 115763 (p := 123479) (by norm_num1) (by norm_num1) ?_
  refine step1615 108529 (p := 115763) (by norm_num1) (by norm_num1) ?_
  refine step1615 101749 (p := 108529) (by norm_num1) (by norm_num1) ?_
  refine step1615 95393 (p := 101749) (by norm_num1) (by norm_num1) ?_
  refine step1615 89431 (p := 95393) (by norm_num1) (by norm_num1) ?_
  refine step1615 83843 (p := 89431) (by norm_num1) (by norm_num1) ?_
  refine step1615 78607 (p := 83843) (by norm_num1) (by norm_num1) ?_
  refine step1615 73709 (p := 78607) (by norm_num1) (by norm_num1) ?_
  refine step1615 69109 (p := 73709) (by norm_num1) (by norm_num1) ?_
  refine step1615 64793 (p := 69109) (by norm_num1) (by norm_num1) ?_
  refine step1615 60757 (p := 64793) (by norm_num1) (by norm_num1) ?_
  refine step1615 56963 (p := 60757) (by norm_num1) (by norm_num1) ?_
  refine step1615 53419 (p := 56963) (by norm_num1) (by norm_num1) ?_
  refine step1615 50087 (p := 53419) (by norm_num1) (by norm_num1) ?_
  refine step1615 46957 (p := 50087) (by norm_num1) (by norm_num1) ?_
  refine step1615 44041 (p := 46957) (by norm_num1) (by norm_num1) ?_
  refine step1615 41299 (p := 44041) (by norm_num1) (by norm_num1) ?_
  refine step1615 38737 (p := 41299) (by norm_num1) (by norm_num1) ?_
  refine step1615 36319 (p := 38737) (by norm_num1) (by norm_num1) ?_
  refine step1615 34061 (p := 36319) (by norm_num1) (by norm_num1) ?_
  refine step1615 31981 (p := 34061) (by norm_num1) (by norm_num1) ?_
  refine step1615 29989 (p := 31981) (by norm_num1) (by norm_num1) ?_
  refine step1615 28123 (p := 29989) (by norm_num1) (by norm_num1) ?_
  refine step1615 26371 (p := 28123) (by norm_num1) (by norm_num1) ?_
  refine step1615 24733 (p := 26371) (by norm_num1) (by norm_num1) ?_
  refine step1615 23201 (p := 24733) (by norm_num1) (by norm_num1) ?_
  refine step1615 21751 (p := 23201) (by norm_num1) (by norm_num1) ?_
  refine step1615 20393 (p := 21751) (by norm_num1) (by norm_num1) ?_
  refine step1615 19121 (p := 20393) (by norm_num1) (by norm_num1) ?_
  refine step1615 17939 (p := 19121) (by norm_num1) (by norm_num1) ?_
  refine step1615 16823 (p := 17939) (by norm_num1) (by norm_num1) ?_
  refine step1615 15773 (p := 16823) (by norm_num1) (by norm_num1) ?_
  refine step1615 14797 (p := 15773) (by norm_num1) (by norm_num1) ?_
  refine step1615 13873 (p := 14797) (by norm_num1) (by norm_num1) ?_
  refine step1615 13009 (p := 13873) (by norm_num1) (by norm_num1) ?_
  refine step1615 12203 (p := 13009) (by norm_num1) (by norm_num1) ?_
  refine step1615 11447 (p := 12203) (by norm_num1) (by norm_num1) ?_
  refine step1615 10733 (p := 11447) (by norm_num1) (by norm_num1) ?_
  refine step1615 10067 (p := 10733) (by norm_num1) (by norm_num1) ?_
  refine step1615 9439 (p := 10067) (by norm_num1) (by norm_num1) ?_
  refine step1615 8863 (p := 9439) (by norm_num1) (by norm_num1) ?_
  refine step1615 8311 (p := 8863) (by norm_num1) (by norm_num1) ?_
  refine step1615 7793 (p := 8311) (by norm_num1) (by norm_num1) ?_
  refine step1615 7321 (p := 7793) (by norm_num1) (by norm_num1) ?_
  refine step1615 6871 (p := 7321) (by norm_num1) (by norm_num1) ?_
  refine step1615 6451 (p := 6871) (by norm_num1) (by norm_num1) ?_
  refine step1615 6053 (p := 6451) (by norm_num1) (by norm_num1) ?_
  refine step1615 5683 (p := 6053) (by norm_num1) (by norm_num1) ?_
  refine step1615 5333 (p := 5683) (by norm_num1) (by norm_num1) ?_
  refine step1615 5003 (p := 5333) (by norm_num1) (by norm_num1) ?_
  refine step1615 4691 (p := 5003) (by norm_num1) (by norm_num1) ?_
  refine step1615 4409 (p := 4691) (by norm_num1) (by norm_num1) ?_
  refine step1615 4139 (p := 4409) (by norm_num1) (by norm_num1) ?_
  refine step1615 3889 (p := 4139) (by norm_num1) (by norm_num1) ?_
  refine step1615 3659 (p := 3889) (by norm_num1) (by norm_num1) ?_
  refine step1615 3433 (p := 3659) (by norm_num1) (by norm_num1) ?_
  refine step1615 3221 (p := 3433) (by norm_num1) (by norm_num1) ?_
  refine step1615 3023 (p := 3221) (by norm_num1) (by norm_num1) ?_
  refine step1615 2837 (p := 3023) (by norm_num1) (by norm_num1) ?_
  refine step1615 2663 (p := 2837) (by norm_num1) (by norm_num1) ?_
  refine step1615 2503 (p := 2663) (by norm_num1) (by norm_num1) ?_
  refine step1615 2357 (p := 2503) (by norm_num1) (by norm_num1) ?_
  refine step1615 2213 (p := 2357) (by norm_num1) (by norm_num1) ?_
  refine step1615 2081 (p := 2213) (by norm_num1) (by norm_num1) ?_
  refine step1615 1951 (p := 2081) (by norm_num1) (by norm_num1) ?_
  refine step1615 1847 (p := 1951) (by norm_num1) (by norm_num1) ?_
  refine step1615 1741 (p := 1847) (by norm_num1) (by norm_num1) ?_
  refine step1615 1637 (p := 1741) (by norm_num1) (by norm_num1) ?_
  refine step1615 1543 (p := 1637) (by norm_num1) (by norm_num1) ?_
  refine step1615 1451 (p := 1543) (by norm_num1) (by norm_num1) ?_
  refine step1615 1361 (p := 1451) (by norm_num1) (by norm_num1) ?_
  refine step1615 1279 (p := 1361) (by norm_num1) (by norm_num1) ?_
  refine step1615 1201 (p := 1279) (by norm_num1) (by norm_num1) ?_
  refine step1615 1129 (p := 1201) (by norm_num1) (by norm_num1) ?_
  refine step1615 1063 (p := 1129) (by norm_num1) (by norm_num1) ?_
  refine step1615 997 (p := 1063) (by norm_num1) (by norm_num1) ?_
  refine step1615 941 (p := 997) (by norm_num1) (by norm_num1) ?_
  refine step1615 887 (p := 941) (by norm_num1) (by norm_num1) ?_
  refine step1615 839 (p := 887) (by norm_num1) (by norm_num1) ?_
  refine step1615 797 (p := 839) (by norm_num1) (by norm_num1) ?_
  refine step1615 751 (p := 797) (by norm_num1) (by norm_num1) ?_
  refine step1615 709 (p := 751) (by norm_num1) (by norm_num1) ?_
  refine step1615 673 (p := 709) (by norm_num1) (by norm_num1) ?_
  refine step1615 631 (p := 673) (by norm_num1) (by norm_num1) ?_
  refine step1615 593 (p := 631) (by norm_num1) (by norm_num1) ?_
  refine step1615 557 (p := 593) (by norm_num1) (by norm_num1) ?_
  refine step1615 523 (p := 557) (by norm_num1) (by norm_num1) ?_
  refine step1615 491 (p := 523) (by norm_num1) (by norm_num1) ?_
  refine step1615 467 (p := 491) (by norm_num1) (by norm_num1) ?_
  refine step1615 449 (p := 467) (by norm_num1) (by norm_num1) ?_
  refine step1615 421 (p := 449) (by norm_num1) (by norm_num1) ?_
  refine step1615 397 (p := 421) (by norm_num1) (by norm_num1) ?_
  refine step1615 373 (p := 397) (by norm_num1) (by norm_num1) ?_
  refine step1615 353 (p := 373) (by norm_num1) (by norm_num1) ?_
  refine step1615 331 (p := 353) (by norm_num1) (by norm_num1) ?_
  refine step1615 311 (p := 331) (by norm_num1) (by norm_num1) ?_
  refine step1615 293 (p := 311) (by norm_num1) (by norm_num1) ?_
  refine step1615 283 (p := 293) (by norm_num1) (by norm_num1) ?_
  refine step1615 271 (p := 283) (by norm_num1) (by norm_num1) ?_
  refine step1615 257 (p := 271) (by norm_num1) (by norm_num1) ?_
  refine step1615 241 (p := 257) (by norm_num1) (by norm_num1) ?_
  refine step1615 233 (p := 241) (by norm_num1) (by norm_num1) ?_
  refine step1615 223 (p := 233) (by norm_num1) (by norm_num1) ?_
  refine step1615 211 (p := 223) (by norm_num1) (by norm_num1) ?_
  refine step1615 199 (p := 211) (by norm_num1) (by norm_num1) ?_
  refine step1615 193 (p := 199) (by norm_num1) (by norm_num1) ?_
  refine step1615 181 (p := 193) (by norm_num1) (by norm_num1) ?_
  refine step1615 173 (p := 181) (by norm_num1) (by norm_num1) ?_
  refine step1615 167 (p := 173) (by norm_num1) (by norm_num1) ?_
  refine step1615 157 (p := 167) (by norm_num1) (by norm_num1) ?_
  refine step1615 149 (p := 157) (by norm_num1) (by norm_num1) ?_
  intro hx
  omega

lemma erdos384_H4_small {n k : ℕ} (hk60 : 60 ≤ k) (hk_lt : k < 18000)
    (hn16 : n < 16 * k) (h2k : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_cases hn3k : 3 * k ≤ n
  · let x : ℕ := (n - k) / 2
    by_cases hx149 : x < 149
    · obtain ⟨p, hp, hxp, hp_le⟩ := ladder87 (x := x) (by dsimp [x]; omega) (by omega)
      have h2p : 2 * p ≤ n := by dsimp [x] at hp_le; omega
      have hkp : k < p := by dsimp [x] at hxp; omega
      have hsub : n - k < 2 * p := by dsimp [x] at hxp; omega
      exact ⟨p, hp, dvd_choose_of_gt_and_lt_two_mul hp hkp hsub h2p, h2p⟩
    · obtain ⟨p, hp, hxp, hp_le⟩ := ladder1615 (x := x) (by omega) (by dsimp [x]; omega)
      have h2p : 2 * p ≤ n := by dsimp [x] at hp_le; omega
      have hkp : k < p := by dsimp [x] at hxp; omega
      have hsub : n - k < 2 * p := by dsimp [x] at hxp; omega
      exact ⟨p, hp, dvd_choose_of_gt_and_lt_two_mul hp hkp hsub h2p, h2p⟩
  · by_cases h7n : 16 * k ≤ 7 * n
    · obtain ⟨p, hp, hkp, hp_le⟩ := ladder87 (x := k) (by omega) (by omega)
      have h2p : 2 * p ≤ n := by omega
      have hsub : n - k < 2 * p := by omega
      exact ⟨p, hp, dvd_choose_of_gt_and_lt_two_mul hp hkp hsub h2p, h2p⟩
    · let x : ℕ := (n - k) / 2
      by_cases hx37 : x < 37
      · refine ⟨37, by norm_num1, ?_, by omega⟩
        apply dvd_choose_of_lt_two_mul_and_three_mul_le (by norm_num1)
        · dsimp [x] at hx37; omega
        · dsimp [x] at hx37; omega
        · omega
      · obtain ⟨p, hp, hxp, hp_le⟩ := ladder87 (x := x) (by omega) (by dsimp [x]; omega)
        have h3p : 3 * p ≤ n := by dsimp [x] at hp_le; omega
        have hk2p : k < 2 * p := by dsimp [x] at hxp; omega
        have hsub : n - k < 2 * p := by dsimp [x] at hxp; omega
        exact ⟨p, hp, dvd_choose_of_lt_two_mul_and_three_mul_le hp hk2p hsub h3p, by omega⟩

/- ## Section 2: Chebyshev Step Identities, Stirling Bounds, and Large k Proof -/

lemma log_choose_le_theta_sub_theta {n k : ℕ} (_hk1 : 1 ≤ k) (h2k : 2 * k ≤ n)
    (hno : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p) :
    Real.log (n.choose k : ℝ) ≤ Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n - k : ℕ) : ℝ) := by
  let m : ℕ := n - k
  have hkn : k ≤ n := by omega
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hfac : n.choose k * k.factorial * m.factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkn
  have hpf_prop : ∀ p ∈ (n.choose k).primeFactors,
      p.Prime ∧ m < p ∧ p ≤ n ∧ (n.choose k).factorization p = 1 := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hdvd : p ∣ n.choose k := Nat.dvd_of_mem_primeFactors hp_mem
    have hgt : n < 2 * p := hno p hp hdvd
    have hmp : m < p := by
      by_contra hle
      have hpm : p ≤ m := by omega
      have hdvd_m : p ∣ m.factorial := Nat.dvd_factorial hp.pos hpm
      have hsq_dvd : p ^ 2 ∣ n.factorial := by
        rw [← hfac, sq]
        exact dvd_trans (mul_dvd_mul hdvd hdvd_m) ⟨k.factorial, by ring⟩
      exact not_prime_sq_dvd_factorial_of_lt_two_mul hp hgt hsq_dvd
    have hpn : p ≤ n := by
      have hdvd_n : p ∣ n.factorial := by
        rw [← hfac]
        exact dvd_trans hdvd ⟨k.factorial * m.factorial, by ring⟩
      exact hp.dvd_factorial.mp hdvd_n
    have hval1 : (n.choose k).factorization p = 1 := by
      have hne0 : (n.choose k).factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp (Nat.support_factorization (n.choose k) ▸ hp_mem)
      by_contra hne1
      have hge2 : 2 ≤ (n.choose k).factorization p := by omega
      have hsq_c : p ^ 2 ∣ n.choose k :=
        dvd_trans (pow_dvd_pow p hge2) (Nat.ordProj_dvd (n.choose k) p)
      have hsq_n : p ^ 2 ∣ n.factorial := by
        rw [← hfac]
        exact dvd_trans hsq_c ⟨k.factorial * m.factorial, by ring⟩
      exact not_prime_sq_dvd_factorial_of_lt_two_mul hp hgt hsq_n
    exact ⟨hp, hmp, hpn, hval1⟩
  let Pn : Finset ℕ := (Finset.Ioc 0 n).filter Nat.Prime
  let Pm : Finset ℕ := (Finset.Ioc 0 m).filter Nat.Prime
  have hPm_sub_Pn : Pm ⊆ Pn := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (by omega)⟩, hp.2⟩
  have hsub_sdiff : (n.choose k).primeFactors ⊆ Pn \ Pm := by
    intro p hp_mem
    obtain ⟨hp, hmp, hpn, _⟩ := hpf_prop p hp_mem
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨⟨hp.pos, hpn⟩, hp⟩, fun h => by omega⟩
  have hprod_le : n.choose k ≤ ∏ p ∈ Pn \ Pm, p := by
    have heq : n.choose k = ∏ p ∈ (n.choose k).primeFactors, p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hchoose_pos.ne']
      rw [Nat.prod_factorization_eq_prod_primeFactors]
      refine Finset.prod_congr rfl (fun p hp_mem => ?_)
      rw [(hpf_prop p hp_mem).2.2.2, pow_one]
    rw [heq]
    refine Finset.prod_le_prod_of_subset_of_one_le' hsub_sdiff (fun p hp _ => ?_)
    have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    exact hprime.one_le
  have hlog_le : Real.log (n.choose k : ℝ) ≤ Real.log ((∏ p ∈ Pn \ Pm, p : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hprod_le)
  have hlog_prod :
      Real.log ((∏ p ∈ Pn \ Pm, p : ℕ) : ℝ) =
        Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => ?_)]
    · rw [Finset.sum_sdiff_eq_sub hPm_sub_Pn]
      simp [Chebyshev.theta, Pn, Pm]
    · have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      exact_mod_cast hprime.pos.ne'
  exact hlog_le.trans_eq hlog_prod

lemma succ_div_eq_add_ite (N d : ℕ) (hd : 0 < d) :
    (N + 1) / d = N / d + if d ∣ N + 1 then 1 else 0 := by
  let q : ℕ := N / d
  let r : ℕ := N % d
  have hdiv : d * q + r = N := Nat.div_add_mod N d
  have hmod : r < d := Nat.mod_lt N hd
  by_cases hrd : r + 1 = d
  · have hN1 : N + 1 = d * (q + 1) := by
      calc N + 1 = d * q + (r + 1) := by omega
        _ = d * (q + 1) := by rw [hrd]; ring
    have hdvd : d ∣ N + 1 := ⟨q + 1, hN1⟩
    rw [if_pos hdvd, hN1, Nat.mul_div_right (q + 1) hd]
  · have hlt : r + 1 < d := by omega
    have hN1 : N + 1 = (r + 1) + d * q := by omega
    have hrem : (N + 1) % d = r + 1 := by
      rw [hN1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hndvd : ¬ (d ∣ N + 1) := by
      rw [Nat.dvd_iff_mod_eq_zero, hrem]
      omega
    rw [if_neg hndvd, hN1, Nat.add_mul_div_left _ _ hd, Nat.div_eq_zero_iff.mpr (Or.inr hlt)]
    omega

lemma log_factorial_eq_sum_vonMangoldt_self (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Ioc 0 N, ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hNfac_pos : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
    have hN1_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul hN1_pos.ne' hNfac_pos.ne', ih,
      ← ArithmeticFunction.vonMangoldt_sum]
    have hdiv_sum :
        (∑ d ∈ (N + 1).divisors, ArithmeticFunction.vonMangoldt d) =
          ∑ d ∈ Finset.Ioc 0 (N + 1),
            (if d ∣ N + 1 then (1 : ℝ) else 0) * ArithmeticFunction.vonMangoldt d := by
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega), Nat.le_of_dvd (by omega) h.1⟩, h.1⟩,
        fun h => ⟨h.2, by omega⟩⟩
    have hprev_sum :
        (∑ d ∈ Finset.Ioc 0 N, ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) =
          ∑ d ∈ Finset.Ioc 0 (N + 1), ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
      refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right (Nat.le_succ N)) (fun d hd hnot => ?_)
      rw [Finset.mem_Ioc] at hd hnot
      have hd_eq : d = N + 1 := by omega
      subst hd_eq
      rw [Nat.div_eq_zero_iff.mpr (Or.inr (Nat.lt_succ_self N))]
      simp
    rw [hdiv_sum, hprev_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd_pos : 0 < d := (Finset.mem_Ioc.mp hd).1
    rw [succ_div_eq_add_ite N d hd_pos]
    split_ifs <;> push_cast <;> ring

lemma log_factorial_eq_sum_vonMangoldt {N X : ℕ} (hNX : N ≤ X) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Ioc 0 X, ((N / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
  rw [log_factorial_eq_sum_vonMangoldt_self N]
  refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hNX) (fun d hd hnot => ?_)
  rw [Finset.mem_Ioc] at hd hnot
  have hgt : N < d := by omega
  rw [Nat.div_eq_zero_iff.mpr (Or.inr hgt)]
  simp

def g30 (t : ℕ) : ℤ :=
  (t : ℤ) + (t / 30 : ℕ) - (t / 2 : ℕ) - (t / 3 : ℕ) - (t / 5 : ℕ)

lemma g30_add (t : ℕ) : g30 (t + 30) = g30 t := by
  dsimp [g30]
  have d30 : ((t : ℤ) + 30) / 30 = (t : ℤ) / 30 + 1 := by omega
  have d2 : ((t : ℤ) + 30) / 2 = (t : ℤ) / 2 + 15 := by omega
  have d3 : ((t : ℤ) + 30) / 3 = (t : ℤ) / 3 + 10 := by omega
  have d5 : ((t : ℤ) + 30) / 5 = (t : ℤ) / 5 + 6 := by omega
  linarith

lemma g30_mul_add (t k : ℕ) : g30 (t + 30 * k) = g30 t := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, g30_add, ih]

lemma g30_bounds (t : ℕ) : 0 ≤ g30 t ∧ g30 t ≤ 1 := by
  have hbase : ∀ r : Fin 30, 0 ≤ g30 r.val ∧ g30 r.val ≤ 1 := by decide +kernel
  have hdiv : t % 30 + 30 * (t / 30) = t := by rw [Nat.add_comm, Nat.div_add_mod]
  rw [← hdiv, g30_mul_add]
  exact hbase ⟨t % 30, Nat.mod_lt t (by positivity)⟩

noncomputable def L30 (m : ℕ) : ℝ :=
  Real.log (m.factorial : ℝ) + Real.log ((m / 30).factorial : ℝ) -
    Real.log ((m / 2).factorial : ℝ) - Real.log ((m / 3).factorial : ℝ) -
    Real.log ((m / 5).factorial : ℝ)

lemma L30_le_psi (m : ℕ) : L30 m ≤ Chebyshev.psi (m : ℝ) := by
  unfold L30
  rw [log_factorial_eq_sum_vonMangoldt (le_refl m),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self m 30),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self m 2),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self m 3),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self m 5)]
  have hdiv_comm : ∀ a d : ℕ, (m / a) / d = (m / d) / a := by
    intro a d
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  simp_rw [hdiv_comm]
  have hcomb :
      (∑ d ∈ Finset.Ioc 0 m, ((m / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) +
        (∑ d ∈ Finset.Ioc 0 m, (((m / d) / 30 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 m, (((m / d) / 2 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 m, (((m / d) / 3 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 m, (((m / d) / 5 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) =
      ∑ d ∈ Finset.Ioc 0 m, ((g30 (m / d) : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [g30, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    ring
  rw [hcomb, Chebyshev.psi, Nat.floor_natCast]
  refine Finset.sum_le_sum (fun d _ => ?_)
  have hg1 : ((g30 (m / d) : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (g30_bounds (m / d)).2
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith

def g420 (t : ℕ) : ℤ :=
  (t : ℤ) + (t / 6 : ℕ) + (t / 10 : ℕ) + (t / 14 : ℕ) -
    (t / 2 : ℕ) - (t / 3 : ℕ) - (t / 5 : ℕ) - (t / 7 : ℕ) -
    (t / 12 : ℕ) - (t / 20 : ℕ) - (t / 42 : ℕ) - 2 * ((t / 420 : ℕ) : ℤ)

lemma g420_add (t : ℕ) : g420 (t + 420) = g420 t := by
  dsimp [g420]
  have d6 : ((t : ℤ) + 420) / 6 = (t : ℤ) / 6 + 70 := by omega
  have d10 : ((t : ℤ) + 420) / 10 = (t : ℤ) / 10 + 42 := by omega
  have d14 : ((t : ℤ) + 420) / 14 = (t : ℤ) / 14 + 30 := by omega
  have d2 : ((t : ℤ) + 420) / 2 = (t : ℤ) / 2 + 210 := by omega
  have d3 : ((t : ℤ) + 420) / 3 = (t : ℤ) / 3 + 140 := by omega
  have d5 : ((t : ℤ) + 420) / 5 = (t : ℤ) / 5 + 84 := by omega
  have d7 : ((t : ℤ) + 420) / 7 = (t : ℤ) / 7 + 60 := by omega
  have d12 : ((t : ℤ) + 420) / 12 = (t : ℤ) / 12 + 35 := by omega
  have d20 : ((t : ℤ) + 420) / 20 = (t : ℤ) / 20 + 21 := by omega
  have d42 : ((t : ℤ) + 420) / 42 = (t : ℤ) / 42 + 10 := by omega
  have d420 : ((t : ℤ) + 420) / 420 = (t : ℤ) / 420 + 1 := by omega
  linarith

lemma g420_mul_add (t k : ℕ) : g420 (t + 420 * k) = g420 t := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, g420_add, ih]

lemma g420_nonneg (t : ℕ) : 0 ≤ g420 t := by
  have hbase : ∀ r : Fin 420, 0 ≤ g420 r.val := by decide +kernel
  have hdiv : t % 420 + 420 * (t / 420) = t := by rw [Nat.add_comm, Nat.div_add_mod]
  rw [← hdiv, g420_mul_add]
  exact hbase ⟨t % 420, Nat.mod_lt t (by positivity)⟩

lemma g420_ge_one {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t < 420) : 1 ≤ g420 t := by
  have hbase : ∀ r : Fin 420, 1 ≤ r.val → 1 ≤ g420 r.val := by decide +kernel
  exact hbase ⟨t, ht2⟩ ht1

noncomputable def L420 (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) + Real.log ((n / 6).factorial : ℝ) +
    Real.log ((n / 10).factorial : ℝ) + Real.log ((n / 14).factorial : ℝ) -
    Real.log ((n / 2).factorial : ℝ) - Real.log ((n / 3).factorial : ℝ) -
    Real.log ((n / 5).factorial : ℝ) - Real.log ((n / 7).factorial : ℝ) -
    Real.log ((n / 12).factorial : ℝ) - Real.log ((n / 20).factorial : ℝ) -
    Real.log ((n / 42).factorial : ℝ) - 2 * Real.log ((n / 420).factorial : ℝ)

lemma theta_le_L420_add (n : ℕ) :
    Chebyshev.theta (n : ℝ) ≤ L420 n + Real.log 4 * ((n : ℝ) / 420) := by
  unfold L420
  rw [log_factorial_eq_sum_vonMangoldt (le_refl n),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 6),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 10),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 14),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 2),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 3),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 5),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 7),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 12),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 20),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 42),
    log_factorial_eq_sum_vonMangoldt (Nat.div_le_self n 420)]
  have hdiv_comm : ∀ a d : ℕ, (n / a) / d = (n / d) / a := by
    intro a d
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  simp_rw [hdiv_comm]
  rw [Finset.mul_sum]
  have hcomb :
      (∑ d ∈ Finset.Ioc 0 n, ((n / d : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) +
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 6 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) +
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 10 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) +
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 14 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 2 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 3 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 5 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 7 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 12 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 20 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, (((n / d) / 42 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d) -
        (∑ d ∈ Finset.Ioc 0 n, 2 * ((((n / d) / 420 : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt d)) =
      ∑ d ∈ Finset.Ioc 0 n, ((g420 (n / d) : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [g420, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    ring
  rw [hcomb]
  let P_all : Finset ℕ := (Finset.Ioc 0 n).filter Nat.Prime
  let P_low : Finset ℕ := (Finset.Ioc 0 (n / 420)).filter Nat.Prime
  have hP_sub : P_low ⊆ P_all := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.div_le_self n 420)⟩, hp.2⟩
  have hhigh_le :
      (∑ p ∈ P_all \ P_low, Real.log (p : ℝ)) ≤
        ∑ d ∈ Finset.Ioc 0 n, ((g420 (n / d) : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
    have hsdiff_sub : P_all \ P_low ⊆ Finset.Ioc 0 n :=
      fun p hp => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
    have h1 :
        (∑ p ∈ P_all \ P_low, Real.log (p : ℝ)) ≤
          ∑ d ∈ P_all \ P_low, ((g420 (n / d) : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt d := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      obtain ⟨hp_all, hp_not_low⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp_ioc, hprime⟩ := Finset.mem_filter.mp hp_all
      rw [Finset.mem_Ioc] at hp_ioc
      have hp_gt : n / 420 < p := by
        by_contra hle
        exact hp_not_low (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_ioc.1, by omega⟩, hprime⟩)
      have hnp_ge1 : 1 ≤ n / p := Nat.div_pos hp_ioc.2 hprime.pos
      have hnp_lt : n / p < 420 := by
        by_contra hge
        have h1 : 420 * p ≤ (n / p) * p := Nat.mul_le_mul_right p (by omega)
        have h2 : (n / p) * p ≤ n := Nat.div_mul_le_self n p
        omega
      have hg1 : (1 : ℝ) ≤ ((g420 (n / p) : ℤ) : ℝ) := by
        exact_mod_cast g420_ge_one hnp_ge1 hnp_lt
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
      have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
      nlinarith
    refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg hsdiff_sub (fun d _ _ => ?_))
    exact mul_nonneg (by exact_mod_cast g420_nonneg (n / d)) ArithmeticFunction.vonMangoldt_nonneg
  have htheta_split :
      Chebyshev.theta (n : ℝ) =
        (∑ p ∈ P_all \ P_low, Real.log (p : ℝ)) + Chebyshev.theta ((n / 420 : ℕ) : ℝ) := by
    have h : ∑ p ∈ P_all \ P_low, Real.log (p : ℝ) =
        (∑ p ∈ P_all, Real.log (p : ℝ)) - ∑ p ∈ P_low, Real.log (p : ℝ) :=
      Finset.sum_sdiff_eq_sub hP_sub
    simp only [Chebyshev.theta, Nat.floor_natCast]
    change ∑ p ∈ P_all, Real.log (p : ℝ) =
      (∑ p ∈ P_all \ P_low, Real.log (p : ℝ)) + ∑ p ∈ P_low, Real.log (p : ℝ)
    linarith
  have hlow_le : Chebyshev.theta ((n / 420 : ℕ) : ℝ) ≤ Real.log 4 * ((n : ℝ) / 420) := by
    calc Chebyshev.theta ((n / 420 : ℕ) : ℝ)
        ≤ Real.log 4 * ((n / 420 : ℕ) : ℝ) := Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ Real.log 4 * ((n : ℝ) / 420) := by
          gcongr
          exact Nat.cast_div_le
  linarith

noncomputable def stirlingMain (y : ℝ) : ℝ := y * Real.log y - y

lemma stirlingMain_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    stirlingMain a ≤ stirlingMain b := by
  have hb_pos : 0 < b := by linarith
  have ha_pos : 0 < a := by linarith
  have hlog_div : Real.log (a / b) ≤ a / b - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha_pos hb_pos)
  rw [Real.log_div ha_pos.ne' hb_pos.ne'] at hlog_div
  have h1 : 0 ≤ b * (Real.log b - Real.log a + a / b - 1) :=
    mul_nonneg hb_pos.le (by linarith)
  have h2 : 0 ≤ (b - a) * Real.log a :=
    mul_nonneg (by linarith) (Real.log_nonneg ha)
  have hid :
      stirlingMain b - stirlingMain a =
        b * (Real.log b - Real.log a + a / b - 1) + (b - a) * Real.log a := by
    unfold stirlingMain
    field_simp [hb_pos.ne']
    ring
  linarith

lemma log_factorial_bounds {q : ℕ} (hq : 1 ≤ q) :
    stirlingMain q + Real.log q / 2 ≤ Real.log (q.factorial : ℝ) ∧
      Real.log (q.factorial : ℝ) ≤ stirlingMain q + Real.log q / 2 + 1 := by
  have hq0 : q ≠ 0 := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  refine ⟨?_, ?_⟩
  · have hlow := Stirling.le_log_factorial_stirling hq0
    have h2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
      apply div_nonneg (Real.log_nonneg ?_) (by norm_num)
      linarith [Real.pi_gt_three]
    unfold stirlingMain
    linarith
  · have hm : q = (q - 1) + 1 := by omega
    have hant := Stirling.log_stirlingSeq'_antitone (Nat.zero_le (q - 1))
    simp only [Function.comp_apply, Nat.succ_eq_add_one, ← hm] at hant
    rw [Stirling.log_stirlingSeq_formula q, Stirling.stirlingSeq_one,
      Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
      Real.log_sqrt (by norm_num), Real.log_mul (by norm_num) hq_pos.ne',
      Real.log_div hq_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at hant
    unfold stirlingMain
    linarith

lemma log_div_factorial_bounds {x d : ℕ} (hx : 420 ≤ x) (hd1 : 1 ≤ d) (hd2 : d ≤ 420) :
    stirlingMain ((x : ℝ) / d) - Real.log x / 2 - 1 / 2 ≤
        Real.log ((x / d).factorial : ℝ) ∧
      Real.log ((x / d).factorial : ℝ) ≤
        stirlingMain ((x : ℝ) / d) + Real.log x / 2 + 1 := by
  let q : ℕ := x / d
  have hq1 : 1 ≤ q := Nat.div_pos (le_trans hd2 hx) (by omega)
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxd_ge1 : (1 : ℝ) ≤ (x : ℝ) / d := by
    rw [one_le_div hd_pos]
    exact_mod_cast le_trans hd2 hx
  have hq_le_xd : (q : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
  have hxd_le_q1 : (x : ℝ) / d ≤ ((q + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hd_pos]
    have hlt : x < (q + 1) * d := by
      have hdiv := Nat.div_add_mod x d
      have hmod := Nat.mod_lt x (by omega : 0 < d)
      change d * q + x % d = x at hdiv
      have hmul : (q + 1) * d = d * q + d := by ring
      omega
    exact_mod_cast hlt.le
  refine ⟨?_, ?_⟩
  · have hq1_fac : Real.log ((q + 1).factorial : ℝ) =
        Real.log (q.factorial : ℝ) + Real.log ((q + 1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos q).ne')]
      ring
    have hlow := (log_factorial_bounds (by omega : 1 ≤ q + 1)).1
    have hmono := stirlingMain_mono hxd_ge1 hxd_le_q1
    have hq1_le_2x : ((q + 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
      have hq_le_x : q ≤ x := Nat.div_le_self x d
      exact_mod_cast (by omega : q + 1 ≤ 2 * x)
    have hlog_q1 : Real.log ((q + 1 : ℕ) : ℝ) ≤ Real.log x + 1 := by
      calc Real.log ((q + 1 : ℕ) : ℝ)
          ≤ Real.log (2 * (x : ℝ)) := Real.log_le_log (by positivity) hq1_le_2x
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx_pos.ne'
        _ ≤ 1 + Real.log x := by linarith [Real.log_two_lt_d9]
        _ = Real.log x + 1 := by ring
    linarith
  · have hup := (log_factorial_bounds hq1).2
    have hmono := stirlingMain_mono (by exact_mod_cast hq1) hq_le_xd
    have hlog_q : Real.log (q : ℝ) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self x d)
    linarith

lemma stirlingMain_div (x d : ℝ) (hx : 0 < x) (hd : 0 < d) :
    stirlingMain (x / d) =
      (1 / d) * (x * Real.log x - x) - (Real.log d / d) * x := by
  unfold stirlingMain
  rw [Real.log_div hx.ne' hd.ne']
  ring

noncomputable def cHigh : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (39 / 140 : ℝ) * Real.log 3 +
    (13 / 84 : ℝ) * Real.log 5 + (1 / 10 : ℝ) * Real.log 7

noncomputable def cLow : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 + (1 / 6 : ℝ) * Real.log 5

lemma L420_upper {n : ℕ} (hn : 420 ≤ n) :
    L420 n + Real.log 4 * ((n : ℝ) / 420) ≤ cHigh * (n : ℝ) + (13 / 2 : ℝ) * Real.log n + 17 / 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have b1   := (log_div_factorial_bounds hn (d := 1)   (by omega) (by omega)).2
  have b6   := (log_div_factorial_bounds hn (d := 6)   (by omega) (by omega)).2
  have b10  := (log_div_factorial_bounds hn (d := 10)  (by omega) (by omega)).2
  have b14  := (log_div_factorial_bounds hn (d := 14)  (by omega) (by omega)).2
  have b2   := (log_div_factorial_bounds hn (d := 2)   (by omega) (by omega)).1
  have b3   := (log_div_factorial_bounds hn (d := 3)   (by omega) (by omega)).1
  have b5   := (log_div_factorial_bounds hn (d := 5)   (by omega) (by omega)).1
  have b7   := (log_div_factorial_bounds hn (d := 7)   (by omega) (by omega)).1
  have b12  := (log_div_factorial_bounds hn (d := 12)  (by omega) (by omega)).1
  have b20  := (log_div_factorial_bounds hn (d := 20)  (by omega) (by omega)).1
  have b42  := (log_div_factorial_bounds hn (d := 42)  (by omega) (by omega)).1
  have b420 := (log_div_factorial_bounds hn (d := 420) (by omega) (by omega)).1
  simp only [Nat.div_one] at b1
  simp only [Nat.cast_one, Nat.cast_ofNat] at b1 b6 b10 b14 b2 b3 b5 b7 b12 b20 b42 b420
  rw [stirlingMain_div _ 1 hn_pos (by norm_num)] at b1
  rw [stirlingMain_div _ 6 hn_pos (by norm_num)] at b6
  rw [stirlingMain_div _ 10 hn_pos (by norm_num)] at b10
  rw [stirlingMain_div _ 14 hn_pos (by norm_num)] at b14
  rw [stirlingMain_div _ 2 hn_pos (by norm_num)] at b2
  rw [stirlingMain_div _ 3 hn_pos (by norm_num)] at b3
  rw [stirlingMain_div _ 5 hn_pos (by norm_num)] at b5
  rw [stirlingMain_div _ 7 hn_pos (by norm_num)] at b7
  rw [stirlingMain_div _ 12 hn_pos (by norm_num)] at b12
  rw [stirlingMain_div _ 20 hn_pos (by norm_num)] at b20
  rw [stirlingMain_div _ 42 hn_pos (by norm_num)] at b42
  rw [stirlingMain_div _ 420 hn_pos (by norm_num)] at b420
  have hl1 : Real.log 1 = 0 := Real.log_one
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [(by norm_num : (4 : ℝ) = 2 ^ 2), Real.log_pow]; norm_num
  have hl6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [(by norm_num : (6 : ℝ) = 2 * 3), Real.log_mul (by norm_num) (by norm_num)]
  have hl10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [(by norm_num : (10 : ℝ) = 2 * 5), Real.log_mul (by norm_num) (by norm_num)]
  have hl14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [(by norm_num : (14 : ℝ) = 2 * 7), Real.log_mul (by norm_num) (by norm_num)]
  have hl12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [(by norm_num : (12 : ℝ) = 4 * 3), Real.log_mul (by norm_num) (by norm_num), hl4]
  have hl20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [(by norm_num : (20 : ℝ) = 4 * 5), Real.log_mul (by norm_num) (by norm_num), hl4]
  have hl42 : Real.log 42 = Real.log 2 + Real.log 3 + Real.log 7 := by
    rw [(by norm_num : (42 : ℝ) = 6 * 7), Real.log_mul (by norm_num) (by norm_num), hl6]
  have hl420 : Real.log 420 = 2 * Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
    rw [(by norm_num : (420 : ℝ) = 12 * 35), Real.log_mul (by norm_num) (by norm_num),
      (by norm_num : (35 : ℝ) = 5 * 7), Real.log_mul (by norm_num) (by norm_num), hl12]
    ring
  rw [hl1] at b1
  rw [hl6] at b6
  rw [hl10] at b10
  rw [hl14] at b14
  rw [hl12] at b12
  rw [hl20] at b20
  rw [hl42] at b42
  rw [hl420] at b420
  unfold L420 cHigh
  rw [hl4]
  linarith

lemma L30_lower {m : ℕ} (hm : 420 ≤ m) :
    cLow * (m : ℝ) - (5 / 2 : ℝ) * Real.log m - 4 ≤ L30 m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have b1  := (log_div_factorial_bounds hm (d := 1)  (by omega) (by omega)).1
  have b30 := (log_div_factorial_bounds hm (d := 30) (by omega) (by omega)).1
  have b2  := (log_div_factorial_bounds hm (d := 2)  (by omega) (by omega)).2
  have b3  := (log_div_factorial_bounds hm (d := 3)  (by omega) (by omega)).2
  have b5  := (log_div_factorial_bounds hm (d := 5)  (by omega) (by omega)).2
  simp only [Nat.div_one] at b1
  simp only [Nat.cast_one, Nat.cast_ofNat] at b1 b30 b2 b3 b5
  rw [stirlingMain_div _ 1 hm_pos (by norm_num)] at b1
  rw [stirlingMain_div _ 30 hm_pos (by norm_num)] at b30
  rw [stirlingMain_div _ 2 hm_pos (by norm_num)] at b2
  rw [stirlingMain_div _ 3 hm_pos (by norm_num)] at b3
  rw [stirlingMain_div _ 5 hm_pos (by norm_num)] at b5
  have hl1 : Real.log 1 = 0 := Real.log_one
  have hl30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [(by norm_num : (30 : ℝ) = (2 * 3) * 5), Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hl1] at b1
  rw [hl30] at b30
  unfold L30 cLow
  linarith

lemma prime_log_bounds :
    (19 / 12 : ℝ) * Real.log 2 < Real.log 3 ∧
      Real.log 3 < (65 / 41 : ℝ) * Real.log 2 ∧
      (65 / 28 : ℝ) * Real.log 2 < Real.log 5 ∧
      Real.log 5 < (72 / 31 : ℝ) * Real.log 2 ∧
      Real.log 7 < (73 / 26 : ℝ) * Real.log 2 := by
  have h3_lo : Real.log ((2 : ℝ) ^ 19) < Real.log ((3 : ℝ) ^ 12) :=
    Real.log_lt_log (by positivity) (by norm_num)
  have h3_hi : Real.log ((3 : ℝ) ^ 41) < Real.log ((2 : ℝ) ^ 65) :=
    Real.log_lt_log (by positivity) (by norm_num)
  have h5_lo : Real.log ((2 : ℝ) ^ 65) < Real.log ((5 : ℝ) ^ 28) :=
    Real.log_lt_log (by positivity) (by norm_num)
  have h5_hi : Real.log ((5 : ℝ) ^ 31) < Real.log ((2 : ℝ) ^ 72) :=
    Real.log_lt_log (by positivity) (by norm_num)
  have h7_hi : Real.log ((7 : ℝ) ^ 26) < Real.log ((2 : ℝ) ^ 73) :=
    Real.log_lt_log (by positivity) (by norm_num)
  simp only [Real.log_pow, Nat.cast_ofNat] at h3_lo h3_hi h5_lo h5_hi h7_hi
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma concave_binom_entropy (a b : ℝ) :
    ConcaveOn ℝ (Set.Icc (2 : ℝ) 16)
      (fun x => x * Real.log x - (x - 1) * Real.log (x - 1) - a * x - b) := by
  let f : ℝ → ℝ := fun x => x * Real.log x - (x - 1) * Real.log (x - 1) - a * x - b
  let f' : ℝ → ℝ := fun x => Real.log x - Real.log (x - 1) - a
  have hf_deriv : ∀ x > (1 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
      exact ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0)).congr_deriv (by
        field_simp [hx0])
    have hsub1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := (hasDerivAt_id' x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => (t - 1) * Real.log (t - 1)) (Real.log (x - 1) + 1) x := by
      exact (hsub1.mul (hsub1.log hx1)).congr_deriv (by
        field_simp [hx1])
    have h3 : HasDerivAt (fun t : ℝ => a * t) a x := by
      simpa using (hasDerivAt_id' x).const_mul a
    exact (((h1.sub h2).sub h3).sub_const b).congr_deriv (by
      dsimp [f']
      ring)
  have hf'' : ∀ x > (1 : ℝ), HasDerivAt f' (x⁻¹ - (x - 1)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have h1 := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t : ℝ => Real.log (t - 1)) (x - 1)⁻¹ x := by
      simpa using ((hasDerivAt_id x).sub_const 1).log hx1
    exact (h1.sub h2).sub_const a
  apply concaveOn_of_deriv2_nonpos (convex_Icc 2 16)
  · intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  · intro x hx
    rw [interior_Icc] at hx
    exact (hf_deriv x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have heq : Set.EqOn (deriv f) f' (Set.Ioo 2 16) :=
      fun y hy => (hf_deriv y (by linarith [hy.1])).deriv
    exact ((hf'' x (by linarith [hx.1])).differentiableAt.differentiableWithinAt).congr
      (fun y hy => heq (by rwa [interior_Icc] at hy)) (heq hx)
  · intro x hx
    rw [interior_Icc] at hx
    rw [Function.iterate_succ_apply', Function.iterate_one]
    have h_ev : deriv f =ᶠ[nhds x] f' := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hf_deriv y (by linarith [hy.1])).deriv
    rw [h_ev.deriv_eq, (hf'' x (by linarith [hx.1])).deriv]
    have hpos1 : (0 : ℝ) < x - 1 := by linarith [hx.1]
    have hpos2 : x - 1 < x := by linarith
    have hinv : x⁻¹ ≤ (x - 1)⁻¹ := (inv_le_inv₀ (by linarith) hpos1).mpr hpos2.le
    linarith

lemma main_entropy_secant_bound {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) (hn16 : n ≤ 16 * k) :
    (118 / 1000 : ℝ) * (k : ℝ) + (16 / 1000 : ℝ) * (n : ℝ) ≤
      ((n : ℝ) * Real.log n - (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ)) -
        (cHigh * (n : ℝ) - cLow * ((n - k : ℕ) : ℝ)) := by
  let x : ℝ := (n : ℝ) / (k : ℝ)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx2 : (2 : ℝ) ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hk_pos]
    exact_mod_cast h2k
  have hx16 : x ≤ 16 := by
    dsimp [x]
    rw [div_le_iff₀ hk_pos]
    exact_mod_cast hn16
  let a : ℝ := cHigh - cLow + 16 / 1000
  let b : ℝ := cLow + 118 / 1000
  let φ : ℝ → ℝ := fun t => t * Real.log t - (t - 1) * Real.log (t - 1) - a * t - b
  have hconc : ConcaveOn ℝ (Set.Icc (2 : ℝ) 16) φ := concave_binom_entropy a b
  obtain ⟨h3_lo, h3_hi, h5_lo, h5_hi, h7_hi⟩ := prime_log_bounds
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  have hφ2 : 0 ≤ φ 2 := by
    dsimp [φ, a, b, cHigh, cLow]
    norm_num1
    rw [Real.log_one]
    linarith
  have hφ16 : 0 ≤ φ 16 := by
    have hl16 : Real.log 16 = 4 * Real.log 2 := by
      rw [(by norm_num : (16 : ℝ) = 2 ^ 4), Real.log_pow]; norm_num
    have hl15 : Real.log 15 = Real.log 3 + Real.log 5 := by
      rw [(by norm_num : (15 : ℝ) = 3 * 5), Real.log_mul (by norm_num) (by norm_num)]
    dsimp [φ, a, b, cHigh, cLow]
    norm_num1
    rw [hl16, hl15]
    linarith
  have hmin : min (φ 2) (φ 16) ≤ φ x :=
    hconc.min_le_of_mem_Icc ⟨le_refl 2, by norm_num⟩ ⟨by norm_num, le_refl 16⟩ ⟨hx2, hx16⟩
  have hφx : 0 ≤ φ x := le_trans (le_min hφ2 hφ16) hmin
  have hn_eq : (n : ℝ) = x * (k : ℝ) := by
    dsimp [x]
    field_simp [hk_pos.ne']
  have hmk_eq : ((n - k : ℕ) : ℝ) = (x - 1) * (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n), hn_eq]
    ring
  have hx_pos : 0 < x := by linarith
  have hx1_pos : 0 < x - 1 := by linarith
  have hscale :
      ((n : ℝ) * Real.log n - (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ)) -
        (cHigh * (n : ℝ) - cLow * ((n - k : ℕ) : ℝ)) -
        ((118 / 1000 : ℝ) * (k : ℝ) + (16 / 1000 : ℝ) * (n : ℝ)) =
      (k : ℝ) * φ x := by
    rw [hn_eq, hmk_eq, Real.log_mul hx_pos.ne' hk_pos.ne', Real.log_mul hx1_pos.ne' hk_pos.ne']
    dsimp [φ, a, b]
    ring
  have hprod_nn : 0 ≤ (k : ℝ) * φ x := mul_nonneg hk_pos.le hφx
  linarith

lemma rpow_inv_three_le_sqrt_div_four {m : ℕ} (hm : 4096 ≤ m) :
    (m : ℝ) ^ (3 : ℝ)⁻¹ ≤ Real.sqrt m / 4 := by
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [le_div_iff₀ (by norm_num)]
  have hpow : (((m : ℝ) ^ (3 : ℝ)⁻¹) * 4) ^ 6 ≤ (Real.sqrt m) ^ 6 := by
    rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (3 : ℝ)⁻¹) 6, ← Real.rpow_mul hm_nn]
    norm_num1
    have hsq6 : (Real.sqrt m) ^ 6 = ((Real.sqrt m) ^ 2) ^ 3 := by ring
    rw [hsq6, Real.sq_sqrt hm_nn, Real.rpow_two]
    have hm_real : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [sq_nonneg (m : ℝ)]
  by_contra hlt
  push Not at hlt
  have hgt : (Real.sqrt m) ^ 6 < (((m : ℝ) ^ (3 : ℝ)⁻¹) * 4) ^ 6 :=
    pow_lt_pow_left₀ hlt (Real.sqrt_nonneg m) (by omega)
  linarith

lemma rpow_inv_five_le_sqrt_div_four {m : ℕ} (hm : 4096 ≤ m) :
    (m : ℝ) ^ (5 : ℝ)⁻¹ ≤ Real.sqrt m / 4 := by
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [le_div_iff₀ (by norm_num)]
  have hpow : (((m : ℝ) ^ (5 : ℝ)⁻¹) * 4) ^ 10 ≤ (Real.sqrt m) ^ 10 := by
    rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (5 : ℝ)⁻¹) 10, ← Real.rpow_mul hm_nn]
    norm_num1
    have hsq10 : (Real.sqrt m) ^ 10 = ((Real.sqrt m) ^ 2) ^ 5 := by ring
    rw [hsq10, Real.sq_sqrt hm_nn, Real.rpow_two]
    have hm_real : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm3 : (1048576 : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith [sq_nonneg (m : ℝ)]
    nlinarith [sq_nonneg (m : ℝ)]
  by_contra hlt
  push Not at hlt
  have hgt : (Real.sqrt m) ^ 10 < (((m : ℝ) ^ (5 : ℝ)⁻¹) * 4) ^ 10 :=
    pow_lt_pow_left₀ hlt (Real.sqrt_nonneg m) (by omega)
  linarith

lemma log_le_sqrt_div_three {n : ℕ} (hn : 20736 ≤ n) :
    Real.log (n : ℝ) ≤ Real.sqrt n / 3 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let v : ℝ := Real.sqrt (Real.sqrt n)
  have hv_pos : 0 < v := by dsimp [v]; positivity
  have hv2 : v ^ 2 = Real.sqrt n := Real.sq_sqrt (Real.sqrt_nonneg n)
  have hv4 : v ^ 4 = (n : ℝ) := by
    calc v ^ 4 = (v ^ 2) ^ 2 := by ring
      _ = (Real.sqrt n) ^ 2 := by rw [hv2]
      _ = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hv12 : (12 : ℝ) ≤ v := by
    by_contra hlt
    push Not at hlt
    have hlt4 : v ^ 4 < (12 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hv_pos.le (by omega)
    rw [hv4] at hlt4
    have hn_real : (20736 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    norm_num1 at hlt4
    linarith
  have hlog_v : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hv_pos
  have hlog_n : Real.log (n : ℝ) = 4 * Real.log v := by
    rw [← hv4, Real.log_pow]
    norm_num
  rw [hlog_n, ← hv2]
  nlinarith

lemma erdos384_H4_large {n k : ℕ} (hk : 18000 ≤ k) (hn16 : n < 16 * k) (h2k : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_contra hnone
  push Not at hnone
  have hno : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p := by
    intro p hp hdvd
    have h := hnone p hp hdvd
    omega
  let m : ℕ := n - k
  have hm_ge : 18000 ≤ m := by omega
  have hn_ge : 36000 ≤ n := by omega
  have hkn : k ≤ n := by omega
  -- 1. Upper bound on log (n.choose k) via theta(n) - theta(m)
  have hchoose_le_theta :
      Real.log (n.choose k : ℝ) ≤ Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ) :=
    log_choose_le_theta_sub_theta (by omega) h2k hno
  -- 2. Bound theta(n) - theta(m) via L420(n), L30(m), and Costa-Pereira
  have htheta_n : Chebyshev.theta (n : ℝ) ≤ L420 n + Real.log 4 * ((n : ℝ) / 420) :=
    theta_le_L420_add n
  have hL420 :
      L420 n + Real.log 4 * ((n : ℝ) / 420) ≤
        cHigh * (n : ℝ) + (13 / 2 : ℝ) * Real.log n + 17 / 2 :=
    L420_upper (by omega)
  have hL30_psi : L30 m ≤ Chebyshev.psi (m : ℝ) := L30_le_psi m
  have hL30 : cLow * (m : ℝ) - (5 / 2 : ℝ) * Real.log m - 4 ≤ L30 m := L30_lower (by omega)
  have hcp_raw := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (m : ℝ)
  have hpsi2 : Chebyshev.psi ((m : ℝ) ^ (2 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hpsi3 : Chebyshev.psi ((m : ℝ) ^ (3 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * (Real.sqrt m / 4) := by
    refine (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (Nat.cast_nonneg m) _)).trans ?_
    have hlog4_pos : 0 ≤ Real.log 4 + 4 := by
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left (rpow_inv_three_le_sqrt_div_four (by omega)) hlog4_pos
  have hpsi5 : Chebyshev.psi ((m : ℝ) ^ (5 : ℝ)⁻¹) ≤ (Real.log 4 + 4) * (Real.sqrt m / 4) := by
    refine (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (Nat.cast_nonneg m) _)).trans ?_
    have hlog4_pos : 0 ≤ Real.log 4 + 4 := by
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left (rpow_inv_five_le_sqrt_div_four (by omega)) hlog4_pos
  have hl4_lt : Real.log 4 + 4 ≤ (27 / 5 : ℝ) := by
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [(by norm_num : (4 : ℝ) = 2 ^ 2), Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have hsqrt_m_le_n : Real.sqrt m ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast (by omega : m ≤ n))
  have hcp_bound : Chebyshev.psi (m : ℝ) - Chebyshev.theta (m : ℝ) ≤ (81 / 10 : ℝ) * Real.sqrt n := by
    have hsum_psi :
        Chebyshev.psi ((m : ℝ) ^ (2 : ℝ)⁻¹) + Chebyshev.psi ((m : ℝ) ^ (3 : ℝ)⁻¹) +
          Chebyshev.psi ((m : ℝ) ^ (5 : ℝ)⁻¹) ≤
        (Real.log 4 + 4) * ((3 / 2 : ℝ) * Real.sqrt m) := by linarith
    have hsqrt_nn : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
    nlinarith
  -- 3. Lower bound on log (n.choose k) from Stirling
  have hchoose_id :
      Real.log (n.choose k : ℝ) =
        Real.log (n.factorial : ℝ) - Real.log (k.factorial : ℝ) - Real.log (m.factorial : ℝ) := by
    have hfac := Nat.choose_mul_factorial_mul_factorial hkn
    have hc_pos : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn
    have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hm_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hcast : (n.choose k : ℝ) * (k.factorial : ℝ) * (m.factorial : ℝ) = (n.factorial : ℝ) := by
      exact_mod_cast hfac
    rw [← hcast, Real.log_mul (mul_pos hc_pos hk_pos).ne' hm_pos.ne',
      Real.log_mul hc_pos.ne' hk_pos.ne']
    ring
  have hst_n := (log_factorial_bounds (by omega : 1 ≤ n)).1
  have hst_k := (log_factorial_bounds (by omega : 1 ≤ k)).2
  have hst_m := (log_factorial_bounds (by omega : 1 ≤ m)).2
  have hlog_m_le_n : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast (by omega : m ≤ n))
  have hlog_k_le_n : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hkn)
  have hchoose_low :
      ((n : ℝ) * Real.log n - (k : ℝ) * Real.log k - (m : ℝ) * Real.log m) -
        Real.log n / 2 - 2 ≤ Real.log (n.choose k : ℝ) := by
    rw [hchoose_id]
    unfold stirlingMain at hst_n hst_k hst_m
    have hsum_nkm : (n : ℝ) = (k : ℝ) + (m : ℝ) := by
      dsimp [m]
      rw [Nat.cast_sub hkn]
      ring
    linarith
  -- 4. Combine with main_entropy_secant_bound and quadratic completion
  have hsec := main_entropy_secant_bound (by omega) h2k (by omega)
  change (118 / 1000 : ℝ) * (k : ℝ) + (16 / 1000 : ℝ) * (n : ℝ) ≤
    ((n : ℝ) * Real.log n - (k : ℝ) * Real.log k - (m : ℝ) * Real.log m) -
      (cHigh * (n : ℝ) - cLow * (m : ℝ)) at hsec
  have hlog_n_sqrt : Real.log (n : ℝ) ≤ Real.sqrt n / 3 := log_le_sqrt_div_three (by omega)
  have hsq_n : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hk_real : (18000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [sq_nonneg ((4 : ℝ) * Real.sqrt n - 1413)]

theorem erdos384_H4_main : OMA.R_Erdos384_erdos_384_R1_H2_R1.H4 := by
  intro n k hk60 hn16 h2k
  by_cases hk_lt : k < 18000
  · exact erdos384_H4_small hk60 hk_lt hn16 h2k
  · exact erdos384_H4_large (by omega) hn16 h2k

end Erdos384H4Proof

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1_H2_R1.H4 :=
  Erdos384H4Proof.erdos384_H4_main
