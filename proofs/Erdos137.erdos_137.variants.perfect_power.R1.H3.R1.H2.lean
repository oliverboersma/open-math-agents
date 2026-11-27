import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Pow

/-! # The Erdős–Selfridge theorem for consecutive products

The valuation proof and numerical certificates are adapted from the accepted proof
of Erdős Problem 930 in this repository, PR 5357 (commit
98226adfec7b7eb3e58ec827182f018456efed38). The two boundary cases below
reuse the accepted H1 and H2 proofs of the first reduction of Problem 137.
The mathematical source is P. Erdős and J. L. Selfridge, The product of
consecutive integers is never a power, Illinois J. Math. 19 (1975), 292–301.

The common valuation lemma is stated for the half-open interval used in
Problem 137. It gives both the full perfect-power theorem and the odd-prime
case requested by the project.
-/

noncomputable def ErdosSelfridge.firstPrimeAtLeast (k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes k)


open Finset

namespace SylvesterSchur

open scoped Nat.Prime

private theorem lcmUpto_dvd_half_mul_choose (n : ℕ) (hn : 2 ≤ n) :
    Nat.lcmUpto n ∣ Nat.lcmUpto ((n+1)/2) * n.choose (n/2) := by
  let c := (n+1)/2
  have hkn : n/2 ≤ n := by omega
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero (Nat.lcmUpto_ne_zero _) (Nat.choose_ne_zero hkn))]
  intro p hp
  rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero _) (Nat.choose_ne_zero hkn), Finsupp.add_apply,
    Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp]
  change Nat.log p n ≤ Nat.log p c + (n.choose (n/2)).factorization p
  by_cases hl : Nat.log p n ≤ Nat.log p c
  · omega
  let j := Nat.log p c + 1
  have hcp : c < p^j := Nat.lt_pow_succ_log_self hp.one_lt c
  have hp_le : p^j ≤ n := Nat.pow_le_of_le_log (by omega) (by dsimp [j]; omega)
  have hlarge : n < p^(j+1) := by
    calc
      n ≤ 2*c := by dsimp [c]; omega
      _ < 2*p^j := Nat.mul_lt_mul_of_pos_left hcp (by decide)
      _ ≤ p^(j+1) := by rw [pow_succ, mul_comm 2]; exact Nat.mul_le_mul_left _ hp.two_le
  have hj : Nat.log p n < j+1 := Nat.log_lt_of_lt_pow (by omega) hlarge
  have hf : 0 < (n.choose (n/2)).factorization p := by
    rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
    apply Finset.card_pos.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩, ?_⟩⟩
    rw [Nat.mod_eq_of_lt (by dsimp [c] at hcp; omega : n/2 < p^j),
      Nat.mod_eq_of_lt (by dsimp [c] at hcp; omega : n - n/2 < p^j)]
    omega
  dsimp [j] at hj
  omega

theorem lcmUpto_le_four_pow (n : ℕ) : Nat.lcmUpto n ≤ 4^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · interval_cases n <;> simp [Nat.lcmUpto]
    have hdiv := lcmUpto_dvd_half_mul_choose n (by omega)
    have hc : (n+1)/2 < n := by omega
    have hchoose : n.choose (n/2) ≤ 4^(n/2) := by
      obtain hn | hn : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
      · conv_lhs => lhs; rw [hn]
        simpa only [Nat.centralBinom] using (Nat.centralBinom_le_four_pow (n/2))
      · conv_lhs => lhs; rw [hn]
        exact Nat.choose_middle_le_pow (n/2)
    calc
      Nat.lcmUpto n ≤ Nat.lcmUpto ((n+1)/2) * n.choose (n/2) :=
        Nat.le_of_dvd (mul_pos (Nat.lcmUpto_pos _) (Nat.choose_pos (by omega))) hdiv
      _ ≤ 4^((n+1)/2) * 4^(n/2) := Nat.mul_le_mul (ih _ hc) hchoose
      _ = 4^n := by rw [← pow_add]; congr 1; omega

private theorem upper_choose_of_factor_bound {n k K : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ K) :
    n.choose k ≤ 4^(K + 2*n.sqrt) := by
  let L := Nat.lcmUpto n.sqrt
  have hL : L ≠ 0 := Nat.lcmUpto_ne_zero _
  have hM : primorial K ≠ 0 := (primorial_pos K).ne'
  have hdiv : n.choose k ∣ primorial K * L^2 := by
    rw [← Nat.factorization_prime_le_iff_dvd (Nat.choose_ne_zero hkn)
      (mul_ne_zero hM (pow_ne_zero _ hL))]
    intro p hp
    by_cases hz : (n.choose k).factorization p = 0
    · simp [hz]
    have hFac : p ∈ (n.choose k).primeFactors := by rwa [← Nat.support_factorization, Finsupp.mem_support_iff]
    have hpM : p ∣ primorial K := by
      apply Nat.dvd_of_mem_primeFactors
      rw [primeFactors_primorial, Nat.mem_primesLE]
      exact ⟨hK p hFac, hp⟩
    have h1 := hp.factorization_pos_of_dvd hM hpM
    have hs : n.sqrt+1 ≤ p^(Nat.log p n.sqrt+1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have hp_bound : n < p^(2*(Nat.log p n.sqrt+1)) := by
      calc
        n < (n.sqrt+1)^2 := Nat.lt_succ_sqrt' n
        _ ≤ (p^(Nat.log p n.sqrt+1))^2 := Nat.pow_le_pow_left hs _
        _ = _ := by rw [← pow_mul, Nat.mul_comm]
    have hlog := Nat.log_lt_of_lt_pow hn.ne' hp_bound
    have hf : (n.choose k).factorization p ≤ Nat.log p n := Nat.factorization_choose_le_log
    rw [Nat.factorization_mul hM (pow_ne_zero _ hL), Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, nsmul_eq_mul, show L = Nat.lcmUpto n.sqrt from rfl, Nat.factorization_lcmUpto _ hp]
    omega
  calc
    n.choose k ≤ primorial K * L^2 :=
      Nat.le_of_dvd (mul_pos (primorial_pos K) (pow_pos (Nat.lcmUpto_pos _) _)) hdiv
    _ ≤ 4^K * (4^n.sqrt)^2 := Nat.mul_le_mul (primorial_le_four_pow K)
      (Nat.pow_le_pow_left (lcmUpto_le_four_pow _) _)
    _ = 4^(K + 2*n.sqrt) := by rw [← pow_mul, ← pow_add, Nat.mul_comm n.sqrt]

private theorem upper_choose_of_prime_count {n k : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ k) :
    n.choose k ≤ n^(Nat.primeCounting k) := by
  calc
    n.choose k = ∏ p ∈ (n.choose k).primeFactors, p^(n.choose k).factorization p :=
      by
        rw [← Nat.prod_factorization_eq_prod_primeFactors]
        exact (Nat.prod_factorization_pow_eq_self (Nat.choose_ne_zero hkn)).symm
    _ ≤ ∏ _p ∈ (n.choose k).primeFactors, n :=
      Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le hn
    _ ≤ n^(Nat.primeCounting k) := by
      rw [Finset.prod_const, ← Nat.primesLE_card_eq_primeCounting]
      apply pow_right_mono₀ (by omega : 1 ≤ n)
      apply Finset.card_le_card
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨hK p hp, Nat.prime_of_mem_primeFactors hp⟩

/-- Comparison of binomial coefficients when their top arguments are in a given ratio. -/
private theorem choose_ratio {m n k a b : ℕ} (hm : k ≤ m)
    (hmn : m ≤ n) (hab : b ≤ a) (h : a*m ≤ b*n) :
    a^k*m.choose k ≤ b^k*n.choose k := by
  have hprod :
      (∏ i ∈ range k, a*(m-i)) ≤ ∏ i ∈ range k, b*(n-i) := by
    apply Finset.prod_le_prod'
    intro i hi
    have him : i ≤ m := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hm
    have hin := him.trans hmn
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    have hsub : b*i ≤ a*i := Nat.mul_le_mul_right _ hab
    omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hprod
  apply (Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos k))
  simpa only [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hprod

private theorem choose_lower (n k : ℕ) (hkn : k ≤ n) :
    n^k ≤ k^k*n.choose k := by
  simpa using choose_ratio (m := k) (n := n) (k := k) (a := n) (b := k)
    le_rfl hkn hkn (Nat.mul_comm n k).le

private theorem divisor_from_choose {n k p : ℕ} (hp : p.Prime) (hd : p ∣ n.choose k) :
    ∃ i ∈ Finset.range k, p ∣ n-i := by
  have hd' : p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hd _
  rw [Nat.descFactorial_eq_prod_range] at hd'
  exact (hp.prime.dvd_finsetProd_iff _).mp hd'

end SylvesterSchur

namespace SylvesterSchur

open scoped Nat.Prime

private theorem three_prime_count_lt {k : ℕ} (hk : 2048 ≤ k) :
    3*Nat.primeCounting k < k := by
  have h := Nat.primeCounting_add_le (a := 30) (k := 30) (by decide) (by decide) (k-30)
  rw [Nat.add_sub_of_le (by omega : 30 ≤ k),
    show Nat.primeCounting 30 = 10 by decide, show Nat.totient 30 = 8 by decide] at h
  omega

private theorem forty_succ_le_two_pow (a : ℕ) (ha : 10 ≤ a) : 40*(a+1) ≤ 2^a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    rw [pow_succ]
    omega

private theorem self_le_two_pow_div {k : ℕ} (hk : 2048 ≤ k) : k ≤ 2^(k/40) :=
  (show k ≤ 40*(k/40+1) by omega).trans (forty_succ_le_two_pow _ (by omega))

private theorem pow_near_ratio (k : ℕ) : 4^k*2^(k/4) ≤ 5^k := by
  let q := k/4
  let r := k%4
  have hk : k = 4*q+r := by dsimp [q,r]; omega
  have hL : 4^k*2^(k/4) = (4^4*2)^q * 4^r := by
    change 4^k*2^q = _
    rw [hk, pow_add, pow_mul, mul_pow]
    ring
  have hR : 5^k = (5^4)^q * 5^r := by rw [hk, pow_add, pow_mul]
  rw [hL, hR]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left (by decide) _)

private theorem four_pow_split (a b : ℕ) :
    4^(a+2*b) = 4^a*2^(4*b) := by
  rw [pow_add, show (4:ℕ)^(2*b) = 2^(4*b) by
    rw [show (4:ℕ) = 2^2 by decide, ← pow_mul]
    congr 1
    omega]

private theorem six_sqrt_le {n k : ℕ} (hk : 2048 ≤ k) (h : n^2 ≤ k^3) :
    6*n.sqrt ≤ k := by
  have hsq := Nat.pow_le_pow_left (Nat.sqrt_le' n) 2
  rw [← pow_mul] at hsq
  have he : 1296*k^3 ≤ k^4 := by
    rw [show k^4 = k*k^3 by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  have hh : (6*n.sqrt)^4 ≤ k^4 := by
    rw [mul_pow, show (6:ℕ)^4=1296 by decide]
    exact (Nat.mul_le_mul_left _ (hsq.trans h)).trans he
  exact le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (Nat.zero_le _) hh

private theorem scaled_sqrt_le {n k a b : ℕ} (hab : a^2*b ≤ k) (hn : n ≤ b*k) :
    a*n.sqrt ≤ k := by
  have h : (a*n.sqrt)^2 ≤ k^2 := by
    rw [mul_pow, pow_two k]
    calc
      a^2*n.sqrt^2 ≤ a^2*n := Nat.mul_le_mul_left _ (Nat.sqrt_le' n)
      _ ≤ a^2*(b*k) := Nat.mul_le_mul_left _ hn
      _ = (a^2*b)*k := by ring
      _ ≤ k*k := Nat.mul_le_mul_right _ hab
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le _) h

private theorem prime_cutoff {n k : ℕ} (hk : 2048 ≤ k)
    (hkn : 2*k ≤ n) (hK : ∀ p ∈ (n.choose k).primeFactors, p ≤ k) :
    ∀ p ∈ (n.choose k).primeFactors, p ≤ n/3 := by
  intro p hp
  by_contra! h
  have hn : n < 3*p := by omega
  have hne : p ≠ 2 := by omega
  have hf := Nat.factorization_choose_of_lt_three_mul hne (hK p hp)
    (show p ≤ n-k by have := hK _ hp; omega) hn
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
  exact hp hf

private theorem large_k_choose_has_factor {n k : ℕ} (hk : 2048 ≤ k) (hkn : 2*k ≤ n) :
    ∃ p ∈ (n.choose k).primeFactors, k < p := by
  by_contra! hK
  have hn : 0 < n := by omega
  have hkN : k ≤ n := by omega
  have hc := Nat.four_pow_lt_mul_centralBinom k (by omega)
  change 4^k < k*(2*k).choose k at hc
  have hu := upper_choose_of_factor_bound hn hkN hK
  have hkp := self_le_two_pow_div hk
  by_cases hWide : k^3 ≤ n^2
  · let a := Nat.primeCounting k
    have hπ : 3*a < k := three_prime_count_lt hk
    have h₁ : n^(a*3) < n^k := pow_lt_pow_right₀ (by omega : 1 < n) (by omega)
    have h₂ : k^(k*3) ≤ n^(k*2) := by
      rw [Nat.mul_comm k 3, Nat.mul_comm k 2, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left hWide _
    have hU : n.choose k ≤ n^a := upper_choose_of_prime_count hn hkN hK
    have hl : n^k ≤ n^a*k^k := calc
      n^k ≤ k^k*n.choose k := choose_lower _ _ hkN
      _ ≤ k^k*n^a := Nat.mul_le_mul_left _ hU
      _ = n^a*k^k := Nat.mul_comm _ _
    have hbad := Nat.pow_le_pow_left hl 3
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hbad
    have hlt : n^(a*3)*k^(k*3) < n^(k*3) := by
      calc
        n^(a*3)*k^(k*3) ≤ n^(a*3)*n^(k*2) := Nat.mul_le_mul_left _ h₂
        _ < n^k*n^(k*2) := Nat.mul_lt_mul_of_pos_right h₁ (by positivity)
        _ = n^(k*3) := by rw [← pow_add]; congr 1; omega
    exact (not_lt_of_ge hbad) hlt
  by_cases hFar : 4*k ≤ n
  · have hcmp : 2^k*(2*k).choose k ≤ n.choose k := by
      simpa using choose_ratio (m := 2*k) (n := n) (k := k) (a := 2) (b := 1)
        (by omega) (by omega) (by decide) (by omega)
    have hl : 4^k*2^k < k*n.choose k := calc
      4^k*2^k < (k*(2*k).choose k)*2^k := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = k*(2^k*(2*k).choose k) := by ring
      _ ≤ k*n.choose k := Nat.mul_le_mul_left _ hcmp
    have hs := six_sqrt_le hk (le_of_not_ge hWide)
    have hus : k*n.choose k ≤ 4^k*2^k := calc
      k*n.choose k ≤ 2^(k/40)*4^(k+2*n.sqrt) := Nat.mul_le_mul hkp hu
      _ = 4^k*2^(k/40+4*n.sqrt) := by rw [four_pow_split, pow_add]; ring
      _ ≤ 4^k*2^k := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
    exact (not_lt_of_ge hus) hl
  by_cases hNear : 5*k ≤ 2*n
  · have hcm : 5^k*(2*k).choose k ≤ 4^k*n.choose k :=
      choose_ratio (by omega) hkn (by decide) (by omega)
    have hl : 5^k < k*n.choose k := by
      apply Nat.lt_of_mul_lt_mul_left (a := 4^k)
      calc
        4^k*5^k < (k*(2*k).choose k)*5^k := Nat.mul_lt_mul_of_pos_right hc (by positivity)
        _ = k*(5^k*(2*k).choose k) := by ring
        _ ≤ k*(4^k*n.choose k) := Nat.mul_le_mul_left _ hcm
        _ = 4^k*(k*n.choose k) := by ring
    have hs : 20*n.sqrt ≤ k := scaled_sqrt_le (a := 20) (b := 4) (by omega) (by omega)
    have hus : k*n.choose k ≤ 5^k := calc
      k*n.choose k ≤ 2^(k/40)*4^(k+2*n.sqrt) := Nat.mul_le_mul hkp hu
      _ = 4^k*2^(k/40+4*n.sqrt) := by rw [four_pow_split, pow_add]; ring
      _ ≤ 4^k*2^(k/4) := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
      _ ≤ 5^k := pow_near_ratio k
    exact (not_lt_of_ge hus) hl
  have hs : 24*n.sqrt ≤ k := scaled_sqrt_le (a := 24) (b := 3) (by omega) (by omega)
  have hUpper := upper_choose_of_factor_bound hn hkN (prime_cutoff hk hkn hK)
  have hLower : 4^k < k*n.choose k :=
    hc.trans_le (Nat.mul_le_mul_left _ (Nat.choose_le_choose k hkn))
  have hus : k*n.choose k ≤ 4^k := calc
    k*n.choose k ≤ 2^(k/40)*4^(n/3+2*n.sqrt) := Nat.mul_le_mul hkp hUpper
    _ = 2^(k/40+2*(n/3+2*n.sqrt)) := by rw [show (4:ℕ)=2^2 by decide, ← pow_mul, ← pow_add]
    _ ≤ 2^(2*k) := pow_right_mono₀ (by decide) (by omega)
    _ = 4^k := by rw [pow_mul]; rfl
  exact (not_lt_of_ge hus) hLower

end SylvesterSchur

namespace SylvesterSchur

open scoped Nat.Prime

private def countUpper (b : ℕ) : ℕ :=
  if b ≤ 210 then Nat.primeCounting b
  else min (10+8*((b-30)/30+1)) (46+48*((b-210)/210+1))

set_option maxRecDepth 10000 in
private theorem prime_count_le_count_upper (b : ℕ) : Nat.primeCounting b ≤ countUpper b := by
  unfold countUpper
  split_ifs with h
  · exact le_rfl
  have h30 := Nat.primeCounting_add_le (a := 30) (k := 30) (by decide) (by decide) (b-30)
  have h210 := Nat.primeCounting_add_le (a := 210) (k := 210) (by decide) (by decide) (b-210)
  rw [Nat.add_sub_of_le (by omega : 30 ≤ b),
    show Nat.primeCounting 30 = 10 by decide, show Nat.totient 30 = 8 by decide] at h30
  rw [Nat.add_sub_of_le (by omega : 210 ≤ b),
    show Nat.primeCounting 210 = 46 by decide, show Nat.totient 210 = 48 by decide] at h210
  exact le_min h30 h210

/-- Dyadic endpoint bounds for intervals of small k. -/
private def CountBounds (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 2048 ≤ a
  | (b,t)::l => (16*b)^8 ≤ 2^t ∧ t*countUpper b < 32*a ∧ CountBounds (b+1) l

private theorem endpoint_power_bound {a b t : ℕ} (h₁ : (16*b)^8 ≤ 2^t)
    (h₂ : t*countUpper b < 32*a) : (16*b)^(countUpper b) < 16^a := by
  by_contra! hn
  have hpow := Nat.pow_le_pow_left hn 8
  have hlt : ((16*b)^(countUpper b))^8 < (16^a)^8 := by
    calc
      ((16*b)^countUpper b)^8 = ((16*b)^8)^countUpper b := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (countUpper b)]
      _ ≤ (2^t)^countUpper b := Nat.pow_le_pow_left h₁ _
      _ = 2^(t*countUpper b) := by rw [pow_mul]
      _ < 2^(32*a) := pow_lt_pow_right₀ (by decide) h₂
      _ = (16^a)^8 := by
        rw [show (16:ℕ)=2^4 by decide, ← pow_mul, ← pow_mul]
        congr 1
        omega
  exact (not_lt_of_ge hpow) hlt

private theorem count_bound_of_list (l : List (ℕ × ℕ)) {a k : ℕ} (ha : a ≤ k)
    (hk : k < 2048) (hkp : 0 < k) (hl : CountBounds a l) :
    (16*k)^(Nat.primeCounting k) < 16^k := by
  induction l generalizing a with
  | nil =>
    change 2048 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,t⟩ := z
    rcases hl with ⟨hb, ht, hl⟩
    by_cases hkb : k ≤ b
    · calc
        (16*k)^(Nat.primeCounting k) ≤ (16*b)^(Nat.primeCounting k) :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hkb) _
        _ ≤ (16*b)^countUpper b := pow_right_mono₀ (by omega)
          ((Nat.monotone_primeCounting hkb).trans (prime_count_le_count_upper b))
        _ < 16^a := endpoint_power_bound hb ht
        _ ≤ 16^k := pow_right_mono₀ (by decide) ha
    · exact ih (by omega) hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem count_table :
    CountBounds 1 [(1, 32), (2, 40), (3, 45), (4, 48), (6, 53), (7, 55), (10, 59),
   (12, 61), (16, 64), (20, 67), (28, 71), (40, 75), (58, 79), (82, 83),
   (126, 88), (192, 93), (210, 94), (239, 96), (269, 97), (299, 98), (419, 102),
   (469, 103), (558, 105), (629, 107), (689, 108), (839, 110), (1024, 112), (1217, 114),
   (1448, 116), (1679, 118), (1889, 120), (2047, 120)] := by
  simp only [CountBounds]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem small_k_wide_choose_has_factor {n k : ℕ} (hk : 0 < k) (hsmall : k < 2048)
    (hn : 16*k ≤ n) : ∃ p ∈ (n.choose k).primeFactors, k < p := by
  by_contra! hK
  let r := Nat.primeCounting k
  have hu : n.choose k ≤ n^r := upper_choose_of_prime_count (by omega) (by omega) hK
  have ht : (16*k)^r < 16^k := count_bound_of_list _ hk hsmall hk count_table
  have hr : r ≤ k := by
    by_contra! h
    have hle : 16^k ≤ (16*k)^r := (Nat.pow_le_pow_left (by omega) _).trans
      (pow_right_mono₀ (by omega) h.le)
    exact (not_lt_of_ge hle) ht
  have hf : k^k < (16*k)^(k-r) := by
    apply Nat.lt_of_mul_lt_mul_left (a := (16*k)^r)
    calc
      (16*k)^r*k^k < 16^k*k^k := Nat.mul_lt_mul_of_pos_right ht (by positivity)
      _ = (16*k)^r*(16*k)^(k-r) := by rw [← mul_pow, ← pow_add, Nat.add_sub_of_le hr]
  have hf' := hf.trans_le (Nat.pow_le_pow_left hn (k-r))
  have hlt : n^r*k^k < n^k := calc
    n^r*k^k < n^r*n^(k-r) := Nat.mul_lt_mul_of_pos_left hf' (pow_pos (by omega : 0 < n) _)
    _ = n^k := by rw [← pow_add, Nat.add_sub_of_le hr]
  have hle : n^k ≤ n^r*k^k := (choose_lower n k (by omega)).trans
    ((Nat.mul_le_mul_left _ hu).trans_eq (Nat.mul_comm _ _))
  exact (not_lt_of_ge hle) hlt

/-- A chain of prime witnesses with overlapping intervals under the comparison 15 n < 16 p. -/
private def PrimeChain (N p : ℕ) : List ℕ → Prop
  | [] => p.Prime ∧ 15*N < 16*p
  | q::l => p.Prime ∧ 15*(q-1) < 16*p ∧ PrimeChain N q l

private theorem prime_from_chain (l : List ℕ) {N p n : ℕ} (hpn : p ≤ n) (hnN : n ≤ N)
    (h : PrimeChain N p l) : ∃ q ≤ n, q.Prime ∧ 15*n < 16*q := by
  induction l generalizing p with
  | nil => exact ⟨p,hpn,h.1,by have := h.2; omega⟩
  | cons q l ih =>
    rcases h with ⟨hp,hq,hl⟩
    by_cases hqn : q ≤ n
    · exact ih hqn hl
    · exact ⟨p,hpn,hp,by omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem prime_chain_table :
    PrimeChain 32767 127
  [131, 139, 149, 157, 167, 179, 191, 199, 211, 223, 233, 241,
   257, 271, 283, 293, 313, 331, 353, 373, 397, 421, 449, 479,
   509, 541, 577, 613, 653, 691, 733, 773, 823, 877, 929, 991,
   1051, 1117, 1187, 1259, 1327, 1409, 1499, 1597, 1699, 1811, 1931, 2053,
   2179, 2311, 2459, 2621, 2791, 2971, 3169, 3373, 3593, 3833, 4079, 4349,
   4639, 4943, 5273, 5623, 5987, 6379, 6803, 7253, 7727, 8243, 8783, 9349,
   9973, 10631, 11329, 12073, 12853, 13709, 14621, 15583, 16619, 17713, 18869, 20123,
   21433, 22861, 24379, 26003, 27737, 29587, 31547] := by
  simp only [PrimeChain]
  repeat' apply And.intro
  all_goals norm_num1

/-- Each entry covers all widths from the current start up to one below its prime. -/
private def WindowProof (n a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => n < 2*a
  | (i,p)::l => i < a ∧ p.Prime ∧ p ∣ n-i ∧ WindowProof n p l

private theorem window_of_certificate (l : List (ℕ × ℕ)) {n a k : ℕ}
    (hak : a ≤ k) (hnk : 2*k ≤ n) (hl : WindowProof n a l) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  induction l generalizing a with
  | nil =>
    change n < 2*a at hl
    omega
  | cons z l ih =>
    obtain ⟨i,p⟩ := z
    rcases hl with ⟨hi,hp,hd,ht⟩
    by_cases hkp : k < p
    · exact ⟨i, Finset.mem_range.mpr (hi.trans_le hak), p, hkp, hp, hd⟩
    · exact ih (by omega) ht

private def WindowTable (a : ℕ) : List (List (ℕ × ℕ)) → Prop
  | [] => 127 ≤ a
  | l::ls => WindowProof a 1 l ∧ WindowTable (a+1) ls

private theorem window_from_table (l : List (List (ℕ × ℕ))) {a n k : ℕ}
    (han : a ≤ n) (hn : n < 127) (hk : 0 < k) (hnk : 2*k ≤ n)
    (hl : WindowTable a l) : ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  induction l generalizing a with
  | nil =>
    change 127 ≤ a at hl
    omega
  | cons l ls ih =>
    rcases hl with ⟨hw, ht⟩
    by_cases he : n = a
    · subst n
      exact window_of_certificate l hk hnk hw
    · exact ih (by omega) ht

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem small_window_table :
    WindowTable 0
  [[], [], [(0, 2)], [(0, 3)], [(0, 2), (1, 3)],
   [(0, 5)], [(0, 3), (1, 5)], [(0, 7)], [(0, 2), (1, 7)], [(0, 3), (2, 7)],
   [(0, 5), (3, 7)], [(0, 11)], [(0, 3), (1, 11)], [(0, 13)], [(0, 7), (1, 13)],
   [(0, 5), (2, 13)], [(0, 2), (1, 5), (3, 13)], [(0, 17)], [(0, 3), (1, 17)], [(0, 19)],
   [(0, 5), (1, 19)], [(0, 7), (2, 19)], [(0, 11), (3, 19)], [(0, 23)], [(0, 3), (1, 23)],
   [(0, 5), (2, 23)], [(0, 13), (3, 23)], [(0, 3), (1, 13), (4, 23)], [(0, 7), (5, 23)], [(0, 29)],
   [(0, 5), (1, 29)], [(0, 31)], [(0, 2), (1, 31)], [(0, 11), (2, 31)], [(0, 17), (3, 31)],
   [(0, 7), (4, 31)], [(0, 3), (2, 17), (5, 31)], [(0, 37)], [(0, 19), (1, 37)], [(0, 13), (2, 37)],
   [(0, 5), (3, 37)], [(0, 41)], [(0, 7), (1, 41)], [(0, 43)], [(0, 11), (1, 43)],
   [(0, 5), (2, 43)], [(0, 23), (3, 43)], [(0, 47)], [(0, 3), (1, 47)], [(0, 7), (2, 47)],
   [(0, 5), (3, 47)], [(0, 17), (4, 47)], [(0, 13), (5, 47)], [(0, 53)], [(0, 3), (1, 53)],
   [(0, 11), (2, 53)], [(0, 7), (3, 53)], [(0, 19), (4, 53)], [(0, 29), (5, 53)], [(0, 59)],
   [(0, 5), (1, 59)], [(0, 61)], [(0, 31), (1, 61)], [(0, 7), (2, 61)], [(0, 2), (1, 7), (3, 61)],
   [(0, 13), (4, 61)], [(0, 11), (5, 61)], [(0, 67)], [(0, 17), (1, 67)], [(0, 23), (2, 67)],
   [(0, 7), (3, 67)], [(0, 71)], [(0, 3), (1, 71)], [(0, 73)], [(0, 37), (1, 73)],
   [(0, 5), (2, 73)], [(0, 19), (3, 73)], [(0, 11), (4, 73)], [(0, 13), (5, 73)], [(0, 79)],
   [(0, 5), (1, 79)], [(0, 3), (2, 79)], [(0, 41), (3, 79)], [(0, 83)], [(0, 7), (1, 83)],
   [(0, 17), (2, 83)], [(0, 43), (3, 83)], [(0, 29), (4, 83)], [(0, 11), (5, 83)], [(0, 89)],
   [(0, 5), (1, 89)], [(0, 13), (2, 89)], [(0, 23), (3, 89)], [(0, 31), (4, 89)], [(0, 47), (5, 89)],
   [(0, 19), (6, 89)], [(0, 3), (2, 47), (7, 89)], [(0, 97)], [(0, 7), (1, 97)], [(0, 11), (2, 97)],
   [(0, 5), (3, 97)], [(0, 101)], [(0, 17), (1, 101)], [(0, 103)], [(0, 13), (1, 103)],
   [(0, 7), (2, 103)], [(0, 53), (3, 103)], [(0, 107)], [(0, 3), (1, 107)], [(0, 109)],
   [(0, 11), (1, 109)], [(0, 37), (2, 109)], [(0, 7), (3, 109)], [(0, 113)], [(0, 19), (1, 113)],
   [(0, 23), (2, 113)], [(0, 29), (3, 113)], [(0, 13), (4, 113)], [(0, 59), (5, 113)], [(0, 17), (6, 113)],
   [(0, 5), (2, 59), (7, 113)], [(0, 11), (8, 113)], [(0, 61), (9, 113)], [(0, 41), (10, 113)], [(0, 31), (11, 113)],
   [(0, 5), (3, 61), (12, 113)], [(0, 7), (4, 61), (13, 113)]] := by
  simp only [WindowTable, WindowProof]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem small_k_close_window {n k : ℕ} (hk : 0 < k) (hsmall : k < 2048)
    (hkn : 2*k ≤ n) (hn : n < 16*k) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  by_cases ht : 127 ≤ n
  · obtain ⟨p,hpn,hp,hp'⟩ := prime_from_chain _ ht (by omega) prime_chain_table
    have hi : n-p < k := by omega
    refine ⟨n-p, Finset.mem_range.mpr hi, p, by omega, hp, ?_⟩
    have he : n-(n-p)=p := by omega
    rw [he]
  exact window_from_table _ (Nat.zero_le _) (by omega) hk hkn small_window_table

private theorem top_window {n k : ℕ} (hk : 0 < k) (hkn : 2*k ≤ n) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
  have bridge (h : ∃ p ∈ (n.choose k).primeFactors, k < p) :
      ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ n-i := by
    obtain ⟨p,hp,hpk⟩ := h
    have hprime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨i,hi,hd⟩ := divisor_from_choose hprime (Nat.dvd_of_mem_primeFactors hp)
    exact ⟨i,hi,p,hpk,hprime,hd⟩
  by_cases hlarge : 2048 ≤ k
  · exact bridge (large_k_choose_has_factor hlarge hkn)
  by_cases hwide : 16*k ≤ n
  · exact bridge (small_k_wide_choose_has_factor hk (by omega) hwide)
  · exact small_k_close_window hk (by omega) hkn (by omega)

/-- A block of k consecutive integers starting above k has a prime divisor greater than k. -/
theorem exists_large_prime {m k : ℕ} (hm : k < m) (hk : 0 < k) :
    ∃ i ∈ Finset.range k, ∃ p > k, p.Prime ∧ p ∣ m+i := by
  obtain ⟨j,hj,p,hpk,hp,hd⟩ := top_window (n := m+k-1) hk (by omega)
  have hj' := Finset.mem_range.mp hj
  refine ⟨k-1-j, Finset.mem_range.mpr (by omega), p, hpk, hp, ?_⟩
  have he : m+k-1-j = m+(k-1-j) := by omega
  exact he ▸ hd

end SylvesterSchur

namespace ErdosSelfridge

private theorem nextPrime_spec (k : ℕ) :
    k ≤ ErdosSelfridge.firstPrimeAtLeast k ∧ (ErdosSelfridge.firstPrimeAtLeast k).Prime := by
  exact Nat.find_spec (Nat.exists_infinite_primes k)

private theorem interval_factorization_of_unique {n k p m : ℕ}
    (hm : m ∈ Icc (n + 1) (n + k))
    (hunique : ∀ j ∈ Icc (n + 1) (n + k), j ≠ m → ¬ p ∣ j) :
    (∏ j ∈ Icc (n + 1) (n + k), j).factorization p = m.factorization p := by
  rw [Nat.factorization_prod_apply (fun j hj => by
    have := (mem_Icc.mp hj).1
    omega)]
  exact sum_eq_single_of_mem m hm (fun j hj hjm =>
    Nat.factorization_eq_zero_of_not_dvd (hunique j hj hjm))

theorem short_interval (k l n : ℕ) (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) (hn : n ≤ k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  obtain ⟨q, hq, hqlo, hqhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n + k) / 2) (by omega)
  have hpExists : ∃ p, k ≤ p ∧ p.Prime ∧ n + k < 2 * p ∧ p ≤ n + k := by
    by_cases hqk : k ≤ q
    · exact ⟨q, hqk, hq, by omega, by omega⟩
    · exact ⟨ErdosSelfridge.firstPrimeAtLeast k, (nextPrime_spec k).1, (nextPrime_spec k).2,
        by have := (nextPrime_spec k).1; omega, hend⟩
  obtain ⟨p, hpk, hp, hpbig, hpend⟩ := hpExists
  have hpmem : p ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, hpend⟩
  refine ⟨p, hpk, hp, ?_⟩
  rw [interval_factorization_of_unique hpmem, hp.factorization_self]
  · exact fun h => by have := Nat.le_of_dvd (by decide : 0 < 1) h; omega
  · intro j hj hjp hdvd
    rcases hdvd with ⟨a, ha⟩
    have hjlo := (mem_Icc.mp hj).1
    have hjhi := (mem_Icc.mp hj).2
    have haPos : 0 < a := by
      by_contra! h
      have : a = 0 := by omega
      simp [this] at ha
      omega
    have haOne : a = 1 := by
      by_contra h
      have htwo : 2 ≤ a := by omega
      have := Nat.mul_le_mul_left p htwo
      omega
    exact hjp (by simpa [haOne] using ha)

theorem long_prime_occurs_once {n k p m : ℕ} (hpk : k ≤ p)
    (hm : m ∈ Icc (n + 1) (n + k)) (hpm : p ∣ m) :
    (∏ j ∈ Icc (n + 1) (n + k), j).factorization p = m.factorization p := by
  apply interval_factorization_of_unique hm
  intro j hj hjm hpj
  have hlo := (mem_Icc.mp hm).1
  have hhi := (mem_Icc.mp hm).2
  have hjlo := (mem_Icc.mp hj).1
  have hjhi := (mem_Icc.mp hj).2
  rcases lt_or_gt_of_ne hjm with hlt | hlt
  · have hdiv := Nat.dvd_sub hpm hpj
    have := Nat.le_of_dvd (show 0 < m - j by omega) hdiv
    omega
  · have hdiv := Nat.dvd_sub hpj hpm
    have := Nat.le_of_dvd (show 0 < j - m by omega) hdiv
    omega

private theorem factorization_le_gap {p m j : ℕ}
    (hp : p.Prime) (hjm : j.factorization p ≤ m.factorization p)
    (hne : j ≠ m) :
    j.factorization p ≤ (max j m - min j m).factorization p := by
  rw [← Nat.factorization_pow_self hp (n := j.factorization p)]
  have hjd : p ^ j.factorization p ∣ j := Nat.ordProj_dvd j p
  have hmd : p ^ j.factorization p ∣ m := dvd_trans (pow_dvd_pow p hjm)
    (Nat.ordProj_dvd m p)
  have hgap : (p ^ j.factorization p) ∣ max j m - min j m := by
    rcases le_total j m with h | h
    · simpa [max_eq_right h, min_eq_left h] using Nat.dvd_sub hmd hjd
    · simpa [max_eq_left h, min_eq_right h] using Nat.dvd_sub hjd hmd
  exact ((Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (by omega)).2 hgap) p

private theorem prod_erased_gaps {n k m : ℕ}
    (hm : m ∈ Icc (n + 1) (n + k)) :
    (∏ j ∈ (Icc (n + 1) (n + k)).erase m, (max j m - min j m)) =
      (m - (n + 1)).factorial * (n + k - m).factorial := by
  have hlow := (mem_Icc.mp hm).1
  have hhigh := (mem_Icc.mp hm).2
  have hpartition :
      (Icc (n + 1) (n + k)).erase m = Ico (n + 1) m ∪ Icc (m + 1) (n + k) := by
    ext j
    simp only [mem_erase, mem_Icc, mem_union, mem_Ico]
    omega
  have hdisjoint : Disjoint (Ico (n + 1) m) (Icc (m + 1) (n + k)) := by
    rw [disjoint_left]
    intro j hj hj'
    have := (mem_Ico.mp hj).2
    have := (mem_Icc.mp hj').1
    omega
  have hleft :
      (∏ j ∈ Ico (n + 1) m, (max j m - min j m)) = (m - (n + 1)).factorial := by
    rw [← prod_range_add_one_eq_factorial]
    apply prod_bij' (fun j _ => m - j - 1) (fun i _ => m - (i + 1))
    · intro j hj
      have := mem_Ico.mp hj
      exact mem_range.mpr (by omega)
    · intro i hi
      have := mem_range.mp hi
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro j hj
      have := mem_Ico.mp hj
      omega
    · intro i hi
      have := mem_range.mp hi
      omega
    · intro j hj
      have := (mem_Ico.mp hj).2
      rw [max_eq_right (by omega), min_eq_left (by omega)]
      omega
  have hright :
      (∏ j ∈ Icc (m + 1) (n + k), (max j m - min j m)) = (n + k - m).factorial := by
    rw [← prod_range_add_one_eq_factorial]
    apply prod_bij' (fun j _ => j - (m + 1)) (fun i _ => m + 1 + i)
    · intro j hj
      have := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro i hi
      have := mem_range.mp hi
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j hj
      have := mem_Icc.mp hj
      omega
    · intro i hi
      omega
    · intro j hj
      have := (mem_Icc.mp hj).1
      rw [max_eq_left (by omega), min_eq_right (by omega)]
      omega
  rw [hpartition, prod_union hdisjoint, hleft, hright]


private theorem factorization_after_max_removal_le {n k p m : ℕ} {a : ℕ → ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hm : m ∈ Icc (n + 1) (n + k))
    (hmmax : ∀ j ∈ Icc (n + 1) (n + k), j.factorization p ≤ m.factorization p)
    (hS : S ⊆ (Icc (n + 1) (n + k)).erase m)
    (ha : ∀ j ∈ S, a j ∣ j) :
    (∏ j ∈ S, a j).factorization p ≤ (k - 1).factorial.factorization p := by
  let I := (Icc (n + 1) (n + k)).erase m
  let gap (j : ℕ) := max j m - min j m
  have hj0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (mem_erase.mp (hS hj)).2).1
    omega
  have ha0 (j : ℕ) (hj : j ∈ S) : a j ≠ 0 := by
    intro h
    have hd := ha j hj
    rw [h, zero_dvd_iff] at hd
    exact hj0 j hj hd
  have hgap0 (j : ℕ) (hj : j ∈ I) : gap j ≠ 0 := by
    have := (mem_erase.mp hj).1
    dsimp [gap]
    omega
  have hF : (∏ j ∈ I, gap j) ∣ (k - 1).factorial := by
    dsimp [I, gap]
    rw [prod_erased_gaps hm]
    have he : m - (n + 1) + (n + k - m) = k - 1 := by
      have := mem_Icc.mp hm
      omega
    rw [← he]
    exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have hle : (∏ j ∈ S, a j).factorization p ≤ (∏ j ∈ I, gap j).factorization p := by
    rw [Nat.factorization_prod_apply ha0, Nat.factorization_prod_apply hgap0]
    calc
      ∑ j ∈ S, (a j).factorization p ≤ ∑ j ∈ S, (gap j).factorization p := by
        apply sum_le_sum
        intro j hj
        have h := mem_erase.mp (hS hj)
        exact (((Nat.factorization_le_iff_dvd (ha0 j hj) (hj0 j hj)).2 (ha j hj)) p).trans
          (factorization_le_gap hp (hmmax j h.2) h.1)
      _ ≤ ∑ j ∈ I, (gap j).factorization p := sum_le_sum_of_subset hS
  exact hle.trans (((Nat.factorization_le_iff_dvd
    (prod_ne_zero_iff.mpr hgap0) (Nat.factorial_ne_zero _)).2 hF) p)

theorem small_prime_deletion (n k : ℕ) (hk : 0 < k) (a : ℕ → ℕ)
    (ha : ∀ j ∈ Icc (n + 1) (n + k), a j ∣ j)
    (hsupport : ∀ j ∈ Icc (n + 1) (n + k), ∀ p ≥ k, (a j).factorization p = 0) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - ((range k).filter Nat.Prime).card ≤ S.card ∧
        (∏ j ∈ S, a j) ∣ (k - 1).factorial := by
  classical
  let I := Icc (n + 1) (n + k)
  let P := (range k).filter Nat.Prime
  have hI : I.Nonempty := ⟨n + 1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hmax (p : ℕ) : ∃ m ∈ I, ∀ j ∈ I, j.factorization p ≤ m.factorization p :=
    exists_max_image I (fun j => j.factorization p) hI
  choose m hm hmmax using hmax
  let D := P.image m
  let S := I \ D
  have hSI : S ⊆ I := sdiff_subset
  have hcardI : I.card = k := by
    simp [I, Nat.card_Icc]
  have hsize : k - P.card ≤ S.card := by
    have h := le_card_sdiff D I
    rw [hcardI] at h
    exact (Nat.sub_le_sub_left card_image_le k).trans h
  refine ⟨S, hSI, hsize, ?_⟩
  have hj0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have ha0 (j : ℕ) (hj : j ∈ S) : a j ≠ 0 := by
    intro hz
    have hd := ha j (hSI hj)
    rw [hz, zero_dvd_iff] at hd
    exact hj0 j (hSI hj) hd
  have hprod0 : (∏ j ∈ S, a j) ≠ 0 := prod_ne_zero_iff.mpr ha0
  apply (Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p < k
    · have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hp⟩
      have hD : m p ∈ D := mem_image_of_mem m hpP
      have hSerase : S ⊆ I.erase (m p) := by
        intro j hj
        have hj' := mem_sdiff.mp hj
        exact mem_erase.mpr ⟨fun he => hj'.2 (he ▸ hD), hj'.1⟩
      exact factorization_after_max_removal_le hp (hm p) (hmmax p) hSerase
        (fun j hj => ha j (hSI hj))
    · rw [Nat.factorization_prod_apply ha0, sum_eq_zero]
      · exact Nat.zero_le _
      · exact fun j hj => hsupport j (hSI hj) p (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private noncomputable def powerFreeExponents (l m : ℕ) : ℕ →₀ ℕ :=
  m.factorization.mapRange (· % l) (Nat.zero_mod l)

private noncomputable def rootExponents (l m : ℕ) : ℕ →₀ ℕ :=
  m.factorization.mapRange (· / l) (Nat.zero_div l)

private theorem powerFreeExponents_le (l m : ℕ) :
    powerFreeExponents l m ≤ m.factorization := by
  intro p
  exact Nat.mod_le _ _

private theorem rootExponents_le (l m : ℕ) :
    rootExponents l m ≤ m.factorization := by
  intro p
  exact Nat.div_le_self _ _

private noncomputable def powerFreePart (l m : ℕ) : ℕ :=
  (powerFreeExponents l m).prod (· ^ ·)

private noncomputable def powerRoot (l m : ℕ) : ℕ :=
  (rootExponents l m).prod (· ^ ·)

private theorem powerFreePart_dvd (l m : ℕ) : powerFreePart l m ∣ m :=
  Nat.prod_pow_dvd_of_le_factorization (powerFreeExponents_le l m)

private theorem powerRoot_dvd (l m : ℕ) : powerRoot l m ∣ m :=
  Nat.prod_pow_dvd_of_le_factorization (rootExponents_le l m)

private theorem powerFreePart_factorization (l m p : ℕ) :
    (powerFreePart l m).factorization p = m.factorization p % l := by
  change ((powerFreeExponents l m).prod (· ^ ·)).factorization p =
    (powerFreeExponents l m) p
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (powerFreeExponents_le l m)]

private theorem powerRoot_factorization (l m p : ℕ) :
    (powerRoot l m).factorization p = m.factorization p / l := by
  change ((rootExponents l m).prod (· ^ ·)).factorization p = (rootExponents l m) p
  rw [Nat.factorization_prod_pow_eq_self_of_le_factorization (rootExponents_le l m)]

private theorem powerFreePart_mul_powerRoot (l m : ℕ) (hm : m ≠ 0) :
    powerFreePart l m * powerRoot l m ^ l = m := by
  have ha : powerFreePart l m ≠ 0 :=
    fun h => hm (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l m))
  have hx : powerRoot l m ≠ 0 :=
    fun h => hm (zero_dvd_iff.mp (h ▸ powerRoot_dvd l m))
  have hfac : (powerFreePart l m * powerRoot l m ^ l).factorization = m.factorization := by
    rw [Nat.factorization_mul ha (pow_ne_zero _ hx), Nat.factorization_pow]
    ext p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      powerFreePart_factorization, powerRoot_factorization]
    exact Nat.mod_add_div _ _
  have hpos : powerFreePart l m * powerRoot l m ^ l ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero _ hx)
  have h1 := (Nat.factorization_le_iff_dvd hpos hm).1 hfac.le
  have h2 := (Nat.factorization_le_iff_dvd hm hpos).1 hfac.ge
  exact Nat.dvd_antisymm h1 h2

theorem powerFreePart_of_failed_large_prime (n k l : ℕ)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p)
    {m : ℕ} (hm : m ∈ Icc (n + 1) (n + k)) {p : ℕ} (hpk : k ≤ p) :
    (powerFreePart l m).factorization p = 0 := by
  rw [powerFreePart_factorization]
  by_cases hp : p.Prime
  · by_cases hpm : p ∣ m
    · exact Nat.mod_eq_zero_of_dvd (long_prime_occurs_once hpk hm hpm ▸ hf p hpk hp)
    · simp [Nat.factorization_eq_zero_of_not_dvd hpm]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem reduce_to_small_prime_parts (n k l : ℕ) (hk : 0 < k)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - ((range k).filter Nat.Prime).card ≤ S.card ∧
      (∏ j ∈ S, powerFreePart l j) ∣ (k - 1).factorial ∧
      ∀ j ∈ Icc (n + 1) (n + k), powerFreePart l j * powerRoot l j ^ l = j := by
  obtain ⟨S, hS, hcard, hd⟩ := small_prime_deletion n k hk (powerFreePart l)
    (fun j _ => powerFreePart_dvd l j) (fun _ hj _ hp => powerFreePart_of_failed_large_prime n k l hf hj hp)
  exact ⟨S, hS, hcard, hd, fun j hj => powerFreePart_mul_powerRoot l j (by
    have := (mem_Icc.mp hj).1
    omega)⟩

theorem modulus_growth_of_large_prime {n k l p m : ℕ}
    (hk : 0 < k) (hl : 2 ≤ l) (hkp : k < p) (hp : p.Prime)
    (hm : m ∈ Icc (n + 1) (n + k)) (hpm : p ∣ m)
    (hdiv : l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    k ^ l < n := by
  have hm0 : m ≠ 0 := by
    have := (mem_Icc.mp hm).1
    omega
  have hv : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpm
  rw [long_prime_occurs_once hkp.le hm hpm] at hdiv
  have hle : l ≤ m.factorization p := Nat.le_of_dvd hv hdiv
  have hpow : p ^ l ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0)
    (dvd_trans (pow_dvd_pow p hle) (Nat.ordProj_dvd m p))
  have hl1 : l - 1 + 1 = l := by omega
  have hk1 : k ≤ k ^ (l - 1) := by
    calc
      k = k ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hk (by omega)
  have hh : k ^ l + k < p ^ l := by
    conv_lhs => rw [← hl1, pow_succ]
    conv_rhs => rw [← hl1, pow_succ]
    have hphase : k ^ (l - 1) * (k + 1) < p ^ (l - 1) * p :=
      Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_left hkp (by omega)) (by omega) hp.pos
    rw [Nat.mul_succ] at hphase
    omega
  have := (mem_Icc.mp hm).2
  omega

private theorem square_le_three_pow (t : ℕ) : t ^ 2 ≤ 3 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    by_cases h : 2 ≤ t
    · have ht : t ≤ t * t := by
        have := Nat.mul_le_mul_left t (show 1 ≤ t by omega)
        simpa using this
      rw [pow_succ]
      calc
        (t + 1) ^ 2 ≤ 3 * t ^ 2 := by nlinarith
        _ ≤ 3 ^ t * 3 := by omega
    · interval_cases t <;> norm_num

private theorem interval_pow_width {n k l r : ℕ} (hk : 3 ≤ k)
    (hn : k ^ l < n) (hr : 0 < r) (hrl : r < l) :
    ((n : ℝ) + k) ^ r - (n : ℝ) ^ r ≤ (l : ℝ) * k * (n : ℝ) ^ (r - 1) := by
  have hn0 : 0 < n := by omega
  have hnl : l - 1 + 1 = l := by omega
  have ht : l * (r - 1) ≤ k ^ (l - 1) := by
    calc
      l * (r - 1) ≤ (l - 1) ^ 2 := by
        have h₁ : l * (r - 1) ≤ l * (l - 2) :=
          Nat.mul_le_mul_left _ (by omega)
        have h₂ : l - 2 + 1 = l - 1 := by omega
        have h₃ : l - 1 + 1 = l := by omega
        nlinarith
      _ ≤ 3 ^ (l - 1) := square_le_three_pow _
      _ ≤ k ^ (l - 1) := Nat.pow_le_pow_left hk _
  have htn : l * (r - 1) * k ≤ n := by
    have h := Nat.mul_le_mul_right k ht
    rw [← pow_succ, hnl] at h
    exact h.trans hn.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hkR : 0 ≤ (k : ℝ) := by positivity
  have hlR : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hsum : 0 < (n : ℝ) + k := add_pos_of_pos_of_nonneg hnR hkR
  have hfrac : 0 ≤ (n : ℝ) / ((n : ℝ) + k) := by positivity
  have hbern := one_add_mul_sub_le_pow (a := (n : ℝ) / ((n : ℝ) + k))
    (by linarith : -1 ≤ (n : ℝ) / ((n : ℝ) + k)) (r - 1)
  have hmod : (r : ℝ) / l ≤ 1 + ((r - 1 : ℕ) : ℝ) *
      ((n : ℝ) / ((n : ℝ) + k) - 1) := by
    have htnR : (l : ℝ) * ((r - 1 : ℕ) : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast htn
    have hrR : (r : ℝ) + 1 ≤ l := by exact_mod_cast (show r + 1 ≤ l by omega)
    have h₁ : (r : ℝ) / l ≤ 1 - 1 / (l : ℝ) := by
      rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hlR]
      simpa using hrR
    refine h₁.trans ?_
    have habs : (n : ℝ) / ((n : ℝ) + k) - 1 =
        -(k : ℝ) / ((n : ℝ) + k) := by field_simp; ring
    rw [habs]
    have h₂ : ((r - 1 : ℕ) : ℝ) * (k : ℝ) / ((n : ℝ) + k) ≤ 1 / (l : ℝ) := by
      rw [div_le_div_iff₀ hsum hlR, one_mul]
      have h := htnR.trans (show (n : ℝ) ≤ n + k by linarith)
      convert h using 1; ring
    rw [neg_div, mul_neg, ← mul_div_assoc, ← sub_eq_add_neg]
    linarith
  have hcoeff : (r : ℝ) * ((n : ℝ) + k) ^ (r - 1) ≤ l * (n : ℝ) ^ (r - 1) := by
    have h := hmod.trans hbern
    rw [div_pow, div_le_div_iff₀ hlR (pow_pos hsum _)] at h
    simpa [mul_comm] using h
  have hwidth := abs_pow_sub_pow_le (a := (n : ℝ) + k) (b := (n : ℝ)) (n := r)
  have hpow : (n : ℝ) ^ r ≤ ((n : ℝ) + k) ^ r := by gcongr; linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hpow), add_sub_cancel_left, abs_of_nonneg hkR,
    abs_of_pos hsum, abs_of_pos hnR, max_eq_left (by linarith)] at hwidth
  calc
    ((n : ℝ) + k) ^ r - (n : ℝ) ^ r ≤
        (k : ℝ) * r * ((n : ℝ) + k) ^ (r - 1) := hwidth
    _ ≤ _ := by
      simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hcoeff hkR

theorem close_powers_same_part {n k l r a u v : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (ha : 0 < a)
    (hu : n ^ r < a * u ^ l) (hv : a * v ^ l ≤ (n + k) ^ r) :
    v ≤ u := by
  by_contra! huv
  have hn0 : 0 < n := by omega
  have hnl : l - 1 + 1 = l := by omega
  have hnr : r - 1 + 1 = r := by omega
  have hpower : k * n ^ (r - 1) < a * u ^ (l - 1) := by
    by_contra! h
    have hraised := Nat.pow_le_pow_left h l
    rw [Nat.mul_pow, Nat.mul_pow, ← pow_mul, Nat.mul_comm (l - 1) l, pow_mul] at hraised
    have hAC : a * (a * u ^ l) ^ (l - 1) = a ^ l * (u ^ l) ^ (l - 1) := by
      rw [Nat.mul_pow, ← mul_assoc, ← pow_succ', hnl]
    rw [← hAC, ← pow_mul] at hraised
    have hKey : (r - 1) * l + (l - r) = r * (l - 1) := by
      have h1 : (r - 1) * l + l = r * l := by
        rw [← Nat.succ_mul]
        change (r - 1 + 1) * l = r * l
        rw [hnr]
      have h2 : r * (l - 1) + r = r * l := by
        rw [← Nat.mul_succ]
        change r * (l - 1 + 1) = r * l
        rw [hnl]
      omega
    have hh : k ^ l * n ^ ((r - 1) * l) < (n ^ r) ^ (l - 1) := by
      rw [← pow_mul, ← hKey, pow_add, mul_comm (n ^ ((r - 1) * l))]
      have hL : k ^ l < n ^ (l - r) := hn.trans_le (by
        conv_lhs => rw [← pow_one n]
        exact Nat.pow_le_pow_right hn0 (by omega))
      exact Nat.mul_lt_mul_of_pos_right hL (pow_pos hn0 _)
    have hlt := Nat.pow_le_pow_left hu.le (l - 1)
    have hle := Nat.le_mul_of_pos_left ((a * u ^ l) ^ (l - 1)) ha
    omega
  have hkR : (k : ℝ) * (n : ℝ) ^ (r - 1) < (a : ℝ) * (u : ℝ) ^ (l - 1) := by
    exact_mod_cast hpower
  have huR : (n : ℝ) ^ r < (a : ℝ) * (u : ℝ) ^ l := by exact_mod_cast hu
  have hvR : (a : ℝ) * (v : ℝ) ^ l ≤ ((n : ℝ) + k) ^ r := by exact_mod_cast hv
  have hvuR : (u : ℝ) + 1 ≤ v := by exact_mod_cast (show u + 1 ≤ v by omega)
  have hpow : (u : ℝ) ^ l + (l : ℝ) * (u : ℝ) ^ (l - 1) ≤ (v : ℝ) ^ l := by
    calc
      _ ≤ ((u : ℝ) + 1) ^ l := by
        simpa [mul_comm, mul_assoc, mul_left_comm] using
          (pow_add_mul_le_add_pow (a := (u : ℝ)) (b := 1) (by positivity) (by positivity) l)
      _ ≤ _ := by gcongr
  have hAl := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (a : ℝ) by positivity)
  have hLt := mul_lt_mul_of_pos_left hkR (show 0 < (l : ℝ) by
    exact_mod_cast (show 0 < l by omega))
  have hB := interval_pow_width hk hn hr hrl
  linarith [show (a : ℝ) * ((u : ℝ) ^ l + (l : ℝ) * (u : ℝ) ^ (l - 1)) =
      a * (u : ℝ) ^ l + (l : ℝ) * (a * (u : ℝ) ^ (l - 1)) by ring]

theorem eq_of_close_equal_residues {n k l r A B : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l)
    (hAl : n ^ r < A) (hAh : A ≤ (n + k) ^ r)
    (hBl : n ^ r < B) (hBh : B ≤ (n + k) ^ r)
    (hres : ∀ p, A.factorization p % l = B.factorization p % l) : A = B := by
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have he : powerFreeExponents l A = powerFreeExponents l B := by
    ext p
    exact hres p
  have he' : powerFreePart l A = powerFreePart l B := congrArg (fun f : ℕ →₀ ℕ => f.prod (· ^ ·)) he
  have hAa := powerFreePart_mul_powerRoot l A hA0
  have hBa := powerFreePart_mul_powerRoot l B hB0
  rw [← he'] at hBa
  have ha : 0 < powerFreePart l A := Nat.pos_of_ne_zero (fun h =>
    hA0 (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l A)))
  have h₁ := close_powers_same_part hk hn hr hrl ha (hAa ▸ hAl) (hBa ▸ hBh)
  have h₂ := close_powers_same_part hk hn hr hrl ha (hBa ▸ hBl) (hAa ▸ hAh)
  calc
    A = powerFreePart l A * powerRoot l A ^ l := hAa.symm
    _ = powerFreePart l A * powerRoot l B ^ l := by rw [le_antisymm h₂ h₁]
    _ = B := hBa

private theorem gcd_dvd_prod_gcd (x : ℕ) (Y : Multiset ℕ) :
    Nat.gcd x Y.prod ∣ (Y.map (Nat.gcd x)).prod := by
  induction Y using Multiset.induction_on with
  | empty => simp
  | cons y Y ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact dvd_trans (gcd_mul_dvd_mul_gcd x y Y.prod) (Nat.mul_dvd_mul_left _ ih)

private theorem multiset_prod_dvd_of_mem {j : ℕ} {S : Multiset ℕ} (hj : j ∈ S) :
    j ∣ S.prod := by
  rw [← Multiset.cons_erase hj, Multiset.prod_cons]
  exact Nat.dvd_mul_right _ _

private theorem gcd_le_interval_length {n k x y : ℕ}
    (hx : x ∈ Icc (n + 1) (n + k)) (hy : y ∈ Icc (n + 1) (n + k))
    (hxy : y ≠ x) : Nat.gcd x y ≤ k := by
  have hx' := mem_Icc.mp hx
  have hy' := mem_Icc.mp hy
  rcases lt_or_gt_of_ne hxy with h | h
  · exact (Nat.le_of_dvd (by omega : 0 < x - y)
      (Nat.dvd_sub (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))).trans (by omega)
  · exact (Nat.le_of_dvd (by omega : 0 < y - x)
      (Nat.dvd_sub (Nat.gcd_dvd_right x y) (Nat.gcd_dvd_left x y))).trans (by omega)

private theorem le_pow_card_of_product_subset {S : Multiset ℕ} {q : ℕ}
    (h : ∀ i ∈ S, i ≤ q) : S.prod ≤ q ^ S.card := by
  have h' := Multiset.prod_le_prod_map (fun _ : ℕ => q) h
  simpa only [Multiset.map_const', Multiset.prod_replicate] using h'

private theorem pow_card_le_of_product_subset {S : Multiset ℕ} {q : ℕ}
    (h : ∀ i ∈ S, q ≤ i) : q ^ S.card ≤ S.prod := by
  have h' := Multiset.prod_map_le_prod (fun _ : ℕ => q) h
  simpa only [Multiset.map_const', Multiset.prod_replicate] using h'

private theorem eq_of_equal_products {n k l r : ℕ} (hk : 0 < k) (hn : k ^ l < n)
    (hrl : r < l) (S T : Multiset ℕ) (hS : S.card = r) (hT : T.card = r)
    (hSI : ∀ x ∈ S, x ∈ Icc (n + 1) (n + k))
    (hTI : ∀ x ∈ T, x ∈ Icc (n + 1) (n + k))
    (hprod : S.prod = T.prod) : S = T := by
  classical
  have hdir (U V : Multiset ℕ) (hU : ∀ x ∈ U, x ∈ Icc (n + 1) (n + k))
      (hV : ∀ x ∈ V, x ∈ Icc (n + 1) (n + k)) (hVr : V.card = r)
      (hUV : U.prod = V.prod) : U ≤ V := by
    rw [Multiset.le_iff_count]
    intro x
    by_contra! hbad
    let U' := U - V
    let V' := V - U
    have hx : x ∈ U' := Multiset.count_pos.mp (by
      change 0 < (U - V).count x
      rw [Multiset.count_sub]
      omega)
    have hxnot : x ∉ V' := Multiset.count_eq_zero.mp (by
      change (V - U).count x = 0
      rw [Multiset.count_sub]
      omega)
    have hxI := hU x (Multiset.mem_of_le (Multiset.sub_le_self _ _) hx)
    have ht (y : ℕ) (hy : y ∈ V') : y ∈ Icc (n + 1) (n + k) :=
      hV y (Multiset.mem_of_le (Multiset.sub_le_self _ _) hy)
    have h0 : (U ∩ V).prod ≠ 0 := Multiset.prod_ne_zero (by
      intro hz
      have := (mem_Icc.mp (hU 0 ((Multiset.mem_inter.mp hz).1))).1
      omega)
    have hUV' : U'.prod = V'.prod := by
      have hL := congrArg Multiset.prod (Multiset.sub_add_inter U V)
      have hR := congrArg Multiset.prod (Multiset.sub_add_inter V U)
      simp only [Multiset.prod_add] at hL hR
      rw [Multiset.inter_comm V U] at hR
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (hL.trans (hUV.trans hR.symm))
    have hdiv : x ∣ V'.prod := hUV' ▸ multiset_prod_dvd_of_mem hx
    have hgcd : x ∣ (V'.map (Nat.gcd x)).prod := by
      have hg := gcd_dvd_prod_gcd x V'
      rw [Nat.gcd_eq_left hdiv] at hg
      exact hg
    have hpos : 0 < (V'.map (Nat.gcd x)).prod := Nat.pos_of_ne_zero
      (Multiset.prod_ne_zero (by
        intro hz
        obtain ⟨y, _, hy⟩ := Multiset.mem_map.mp hz
        exact (Nat.gcd_pos_of_pos_left y (by have := (mem_Icc.mp hxI).1; omega)).ne' hy))
    have hle : (V'.map (Nat.gcd x)).prod ≤ k ^ V'.card := by
      rw [← Multiset.card_map (Nat.gcd x) V']
      apply le_pow_card_of_product_subset
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      exact gcd_le_interval_length hxI (ht y hy) (fun h => hxnot (h ▸ hy))
    have hv' : V'.card ≤ l := (Multiset.card_le_card (Multiset.sub_le_self _ _)).trans
      (by omega)
    have hPx := ((Nat.le_of_dvd hpos hgcd).trans hle).trans (Nat.pow_le_pow_right hk hv')
    have := (mem_Icc.mp hxI).1
    omega
  exact le_antisymm (hdir S T hSI hTI hT hprod) (hdir T S hTI hSI hS hprod.symm)

theorem interval_products_residue_injective {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S T : Multiset ℕ) (hS : S.card = r) (hT : T.card = r)
    (hSI : ∀ x ∈ S, x ∈ Icc (n + 1) (n + k))
    (hTI : ∀ x ∈ T, x ∈ Icc (n + 1) (n + k))
    (hres : ∀ p, S.prod.factorization p % l = T.prod.factorization p % l) : S = T := by
  have hbounds (U : Multiset ℕ) (hU : U.card = r)
      (hUI : ∀ x ∈ U, x ∈ Icc (n + 1) (n + k)) :
      n ^ r < U.prod ∧ U.prod ≤ (n + k) ^ r := by
    have hlo := pow_card_le_of_product_subset (S := U) (q := n + 1) (fun x hx => (mem_Icc.mp (hUI x hx)).1)
    have hhi := le_pow_card_of_product_subset (S := U) (q := n + k) (fun x hx => (mem_Icc.mp (hUI x hx)).2)
    rw [hU] at hlo hhi
    exact ⟨(Nat.pow_lt_pow_left (by omega) (by omega)).trans_le hlo, hhi⟩
  obtain ⟨hSl, hSh⟩ := hbounds S hS hSI
  obtain ⟨hTl, hTh⟩ := hbounds T hT hTI
  exact eq_of_equal_products (by omega) hn hrl S T hS hT hSI hTI
    (eq_of_close_equal_residues hk hn hr hrl hSl hSh hTl hTh hres)

private theorem three_factor_has_large_prime {n : ℕ} (hn : 3 < n) :
    ∃ p m, 3 < p ∧ p.Prime ∧ m ∈ Icc (n + 1) (n + 3) ∧ p ∣ m := by
  by_contra! h
  have hsingle (m : ℕ) (hm : m ∈ Icc (n + 1) (n + 3)) (hm₂ : ¬2 ∣ m) :
      m = 3 ^ m.factorization 3 := by
    apply Nat.eq_pow_of_factorization_eq_single (by have := (mem_Icc.mp hm).1; omega)
    ext p
    by_cases hp : p = 3
    · simp [hp]
    · rw [Finsupp.single_eq_of_ne hp]
      by_cases hprime : p.Prime
      · have hp₂ := hprime.two_le
        by_cases htwo : p = 2
        · subst p
          exact Nat.factorization_eq_zero_of_not_dvd hm₂
        · exact Nat.factorization_eq_zero_of_not_dvd (h p m (by omega) hprime hm)
      · exact Nat.factorization_eq_zero_of_not_prime m hprime
  by_cases he : n % 2 = 0
  · have h1 := hsingle (n + 1) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have h3 := hsingle (n + 3) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have hdiv (i : ℕ) (hi : 1 < 3 ^ i) : 3 ∣ 3 ^ i := by
      cases i with
      | zero => simp at hi
      | succ i => rw [pow_succ]; exact Nat.dvd_mul_left _ _
    have hd1 : 3 ∣ n + 1 := h1 ▸ hdiv _ (by omega)
    have hd3 : 3 ∣ n + 3 := h3 ▸ hdiv _ (by omega)
    have hd := Nat.dvd_sub hd3 hd1
    omega
  · have h2 := hsingle (n + 2) (mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
    have hval : (n + 2).factorization 3 ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h2
      omega
    have hd2 : 3 ∣ n + 2 := Nat.dvd_of_factorization_pos hval
    let m := if 4 ∣ n + 1 then n + 3 else n + 1
    have hm : m ∈ Icc (n + 1) (n + 3) := by
      unfold m
      split <;> simp
    have hm₂ : 2 ∣ m := by
      unfold m
      split <;> omega
    have hm₄ : ¬4 ∣ m := by
      unfold m
      split <;> omega
    have hm₃ : ¬3 ∣ m := by
      unfold m
      split <;> omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (n := m / 2) (by
      have := (mem_Icc.mp hm).1
      omega)
    have hd : q ∣ m := dvd_trans hqdvd (Nat.div_dvd_of_dvd hm₂)
    have hq₂ : q ≠ 2 := by
      intro heq
      subst q
      have := Nat.mul_dvd_mul_left 2 hqdvd
      rw [Nat.mul_div_cancel' hm₂] at this
      exact hm₄ this
    have hq₃ : q ≠ 3 := fun e => hm₃ (e ▸ hd)
    have hqge := hq.two_le
    exact h q m (by omega) hq hm hd

private theorem valuation_eq_one_of_two_dvd {m : ℕ}
    (hm : m ≠ 0) (h₂ : 2 ∣ m) (h₄ : ¬4 ∣ m) : m.factorization 2 = 1 := by
  have hlo := Nat.prime_two.factorization_pos_of_dvd hm h₂
  have hhi : ¬ 2 ≤ m.factorization 2 := fun h =>
    h₄ ((Nat.prime_two.pow_dvd_iff_le_factorization hm).2 h)
  omega

theorem three_factors (l n : ℕ) (hl : 2 ≤ l) :
    ∃ p, 3 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 3), m) p) := by
  have hend : ErdosSelfridge.firstPrimeAtLeast 3 ≤ n + 3 :=
    (Nat.find_min' (Nat.exists_infinite_primes 3) ⟨le_rfl, Nat.prime_three⟩).trans (by omega)
  by_cases hn : n ≤ 3
  · exact short_interval 3 l n (by decide) hl hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ := three_factor_has_large_prime (by omega : 3 < n)
  have hgrowth := modulus_growth_of_large_prime (by decide : 0 < 3) hl hpk hp hm hd (h p (by omega) hp)
  have hrest {m : ℕ} (hm : m ∈ Icc (n + 1) (n + 3)) {q : ℕ} (hq : q ≠ 2) :
      m.factorization q % l = 0 := by
    by_cases hqprime : q.Prime
    · have hqlo := hqprime.two_le
      exact powerFreePart_factorization l m q ▸ powerFreePart_of_failed_large_prime n 3 l h hm (by omega)
    · simp [Nat.factorization_eq_zero_of_not_prime m hqprime]
  by_cases he : n % 2 = 0
  · have h₁ : n + 1 ∈ Icc (n + 1) (n + 3) := mem_Icc.mpr ⟨by omega, by omega⟩
    have h₃ : n + 3 ∈ Icc (n + 1) (n + 3) := mem_Icc.mpr ⟨by omega, by omega⟩
    have hres (q : ℕ) : (n + 1).factorization q % l = (n + 3).factorization q % l := by
      by_cases hq : q = 2
      · subst q
        simp [Nat.factorization_eq_zero_of_not_dvd (show ¬2 ∣ n + 1 by omega),
          Nat.factorization_eq_zero_of_not_dvd (show ¬2 ∣ n + 3 by omega)]
      · rw [hrest h₁ hq, hrest h₃ hq]
    have heq := eq_of_close_equal_residues (by decide : 3 ≤ 3) hgrowth
      (by decide : 0 < 1) (by omega : 1 < l)
      (A := n + 1) (B := n + 3) (by simp) (by simp) (by simp) (by simp) hres
    omega
  let x := n + 2
  let y := if 4 ∣ n + 1 then n + 3 else n + 1
  let z := if 4 ∣ n + 1 then n + 1 else n + 3
  have hxl : n + 1 ≤ x := by dsimp [x]; omega
  have hxh : x ≤ n + 3 := by dsimp [x]; omega
  have hyl : n + 1 ≤ y := by unfold y; split <;> omega
  have hyh : y ≤ n + 3 := by unfold y; split <;> omega
  have hzl : n + 1 ≤ z := by unfold z; split <;> omega
  have hzh : z ≤ n + 3 := by unfold z; split <;> omega
  have hyz : y ≠ z := by unfold y z; split <;> omega
  have hxy : x ≠ y := by unfold x y; split <;> omega
  have hxz : x ≠ z := by unfold x z; split <;> omega
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have hxval : x.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    dsimp [x]
    omega)
  have hyval : y.factorization 2 = 1 := valuation_eq_one_of_two_dvd hy0
    (by unfold y; split <;> omega) (by unfold y; split <;> omega)
  let t := z.factorization 2 % l
  have htl : t < l := Nat.mod_lt _ (by omega)
  have ht (q : ℕ) : (y ^ t).factorization q % l =
      (x ^ (t - 1) * z).factorization q % l := by
    by_cases hq : q = 2
    · subst q
      rw [Nat.factorization_mul (pow_ne_zero _ hx0) hz0, Nat.factorization_pow, Nat.factorization_pow]
      simp [hxval, hyval, t]
    · rw [Nat.factorization_mul (pow_ne_zero _ hx0) hz0, Nat.factorization_pow, Nat.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
      rw [Nat.mul_mod _ (y.factorization q), Nat.add_mod, Nat.mul_mod _ (x.factorization q)]
      simp [hrest (mem_Icc.mpr ⟨hyl, hyh⟩) hq, hrest (mem_Icc.mpr ⟨hxl, hxh⟩) hq,
        hrest (mem_Icc.mpr ⟨hzl, hzh⟩) hq]
  by_cases ht0 : t = 0
  · have hh (q : ℕ) : x.factorization q % l = z.factorization q % l := by
      by_cases hq : q = 2
      · subst q
        simpa [hxval, t] using ht0.symm
      · rw [hrest (mem_Icc.mpr ⟨hxl, hxh⟩) hq, hrest (mem_Icc.mpr ⟨hzl, hzh⟩) hq]
    exact hxz (eq_of_close_equal_residues (by decide : 3 ≤ 3) hgrowth
      (by decide : 0 < 1) (by omega : 1 < l)
      (A := x) (B := z) (by simp; omega) (by simpa using hxh)
      (by simp; omega) (by simpa using hzh) hh)
  let S := Multiset.replicate t y
  let T := z ::ₘ Multiset.replicate (t - 1) x
  have hS : S.card = t := by simp [S]
  have hT : T.card = t := by simp [T]; omega
  have hSI (j : ℕ) (hj : j ∈ S) : j ∈ Icc (n + 1) (n + 3) := by
    have hj' := Multiset.eq_of_mem_replicate hj
    exact hj' ▸ mem_Icc.mpr ⟨hyl, hyh⟩
  have hTI (j : ℕ) (hj : j ∈ T) : j ∈ Icc (n + 1) (n + 3) := by
    rcases Multiset.mem_cons.mp hj with h | h
    · exact h ▸ mem_Icc.mpr ⟨hzl, hzh⟩
    · exact (Multiset.eq_of_mem_replicate h) ▸ mem_Icc.mpr ⟨hxl, hxh⟩
  have heq := interval_products_residue_injective (by decide : 3 ≤ 3) hgrowth
    (by omega : 0 < t) htl S T hS hT hSI hTI
    (by simpa [S, T, Multiset.prod_replicate, mul_comm] using ht)
  have hmem : z ∈ S := heq ▸ Multiset.mem_cons_self z _
  exact hyz (Multiset.eq_of_mem_replicate hmem).symm


private theorem multiset_factorization_mod_eq_zero (l p : ℕ) (S : Multiset ℕ)
    (h0 : ∀ j ∈ S, j ≠ 0) (h : ∀ j ∈ S, j.factorization p % l = 0) :
    S.prod.factorization p % l = 0 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons j S ih =>
    have hS : S.prod ≠ 0 := Multiset.prod_ne_zero (fun hz => h0 0 (Multiset.mem_cons_of_mem hz) rfl)
    rw [Multiset.prod_cons, Nat.factorization_mul (h0 j (Multiset.mem_cons_self _ _)) hS,
      Finsupp.add_apply, Nat.add_mod, h j (Multiset.mem_cons_self _ _),
      ih (fun q hq => h0 q (Multiset.mem_cons_of_mem hq))
        (fun q hq => h q (Multiset.mem_cons_of_mem hq))]
    simp

theorem counting_obstruction {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S P : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hP : ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0) :
    (S.card + r - 1).choose r ≤ l ^ P.card := by
  classical
  let T := Sym (↑S) r
  let product (x : T) := ((Sym.map (Subtype.val : (↑S) → ℕ) x : Sym ℕ r) : Multiset ℕ)
  have hprodMem (x : T) {j : ℕ} (hj : j ∈ product x) : j ∈ S := by
    change j ∈ (x : Multiset S).map Subtype.val at hj
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hj
    exact v.property
  let f (x : T) (p : P) : Fin l :=
    ⟨(product x).prod.factorization p % l, Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hEQ : product x = product y := by
      apply interval_products_residue_injective hk hn hr hrl _ _ Sym.card_coe Sym.card_coe
        (fun _ hj => hSI (hprodMem x hj)) (fun _ hj => hSI (hprodMem y hj))
      intro p
      by_cases hp : p ∈ P
      · exact congrArg Fin.val (congrFun hxy (⟨p, hp⟩ : P))
      · have h0 (z : T) : (product z).prod.factorization p % l = 0 :=
          multiset_factorization_mod_eq_zero l p (product z)
            (fun j hj => by
              have := (mem_Icc.mp (hSI (hprodMem z hj))).1
              omega)
            (fun j hj => hP j (hprodMem z hj) p hp)
        rw [h0 x, h0 y]
    apply Sym.map_injective Subtype.val_injective r
    exact Subtype.ext hEQ
  have h := Fintype.card_le_of_injective f hinj
  simpa [T, Sym.card_sym_eq_choose, Fintype.card_fun] using h

theorem prime_counting_bound_of_failure {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    (k + r - 1).choose r ≤ l ^ ((range k).filter Nat.Prime).card := by
  have hcard : (Icc (n + 1) (n + k)).card = k := by
    simp [Nat.card_Icc]
  conv_lhs => rw [← hcard]
  apply counting_obstruction hk hn hr hrl (Icc (n + 1) (n + k)) ((range k).filter Nat.Prime)
    Subset.rfl
  intro j hj p hp
  by_cases hpPrime : p.Prime
  · have hpk : k ≤ p := by
      by_contra! hlt
      exact hp (mem_filter.mpr ⟨mem_range.mpr hlt, hpPrime⟩)
    rw [← powerFreePart_factorization]
    exact powerFreePart_of_failed_large_prime n k l hf hj hpk
  · simp [Nat.factorization_eq_zero_of_not_prime _ hpPrime]


private theorem small_width_large_prime {n k : ℕ} (hk : 3 ≤ k) (hK : k ≤ 5)
    (hn : k < n) :
    ∃ p m, k < p ∧ p.Prime ∧ m ∈ Icc (n + 1) (n + k) ∧ p ∣ m := by
  by_cases h : k ≤ 4
  · obtain ⟨p, m, hp3, hp, hm, hd⟩ := three_factor_has_large_prime (by omega : 3 < n)
    have hpne : p ≠ 4 := fun he => (by decide : ¬Nat.Prime 4) (he ▸ hp)
    have hm' := mem_Icc.mp hm
    exact ⟨p, m, by omega, hp, mem_Icc.mpr ⟨hm'.1, by omega⟩, hd⟩
  have k5 : k = 5 := by omega
  subst k
  have hc : ∀ a : Fin 60, ∃ i : Fin 5,
    ¬3 ∣ a.val + i.val + 1 ∧ ¬4 ∣ a.val + i.val + 1 ∧ ¬5 ∣ a.val + i.val + 1 := by decide
  obtain ⟨i, hi₃, hi₄, hi₅⟩ := hc ⟨n % 60, Nat.mod_lt _ (by decide)⟩
  change ¬3 ∣ n % 60 + i.val + 1 at hi₃
  change ¬4 ∣ n % 60 + i.val + 1 at hi₄
  change ¬5 ∣ n % 60 + i.val + 1 at hi₅
  let m := n + i.val + 1
  have hm₃ : ¬3 ∣ m := by dsimp [m]; omega
  have hm₄ : ¬4 ∣ m := by dsimp [m]; omega
  have hm₅ : ¬5 ∣ m := by dsimp [m]; omega
  have hmlo : n + 1 ≤ m := by dsimp [m]; omega
  have hmhi : m ≤ n + 5 := by dsimp [m]; omega
  have hmI : m ∈ Icc (n + 1) (n + 5) := mem_Icc.mpr ⟨hmlo, hmhi⟩
  let q := if 2 ∣ m then m / 2 else m
  have hq : q ∣ m := by
    unfold q
    split
    · exact Nat.div_dvd_of_dvd (by assumption)
    · exact dvd_rfl
  have hq1 : q ≠ 1 := by unfold q; split <;> omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq1
  have hpm : p ∣ m := dvd_trans hpd hq
  have hp2 : p ≠ 2 := by
    intro htwo
    subst p
    unfold q at hpd
    split at hpd
    · have h := Nat.mul_dvd_mul_left 2 hpd
      rw [Nat.mul_div_cancel' (show 2 ∣ m by assumption)] at h
      exact hm₄ h
    · contradiction
  have hp3 : p ≠ 3 := fun h => hm₃ (h ▸ hpm)
  have hp5 : p ≠ 5 := fun h => hm₅ (h ▸ hpm)
  have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
  have := hp.two_le
  exact ⟨p, m, by omega, hp, hmI, hpm⟩

private theorem choose_three_gt_sq {l : ℕ} (hl : 3 ≤ l) :
    l ^ 2 < (l + 2).choose (l - 1) := by
  have hs : l + 2 - 3 = l - 1 := by omega
  rw [← hs, Nat.choose_symm (by omega : 3 ≤ l + 2)]
  have he := Nat.choose_mul_factorial_mul_factorial (n := l + 2) (k := 3) (by omega)
  have hfac : (l + 2).factorial = (l + 2) * (l + 1) * l * (l - 1).factorial := by
    have hpred : l = (l - 1).succ := by omega
    have hf : l.factorial = l * (l - 1).factorial := by
      conv_lhs => rw [hpred, Nat.factorial_succ]
      rw [show l - 1 + 1 = l by omega]
    calc
      (l + 2).factorial = (l + 2) * ((l + 1) * l.factorial) := by
        simp only [Nat.factorial_succ]
      _ = _ := by rw [hf]; ac_rfl
  rw [hs, hfac, Nat.mul_left_inj (Nat.factorial_ne_zero _)] at he
  have hpoly : 6 * l ^ 2 < (l + 2) * (l + 1) * l := by
    have h₁ : 6 * l < (l + 2) * (l + 1) := by nlinarith
    have h₂ := Nat.mul_lt_mul_of_pos_right h₁ (by omega : 0 < l)
    simpa [pow_two, mul_assoc] using h₂
  norm_num [Nat.factorial] at he
  have h' : 6 * l ^ 2 < 6 * (l + 2).choose 3 := by omega
  omega

theorem four_or_five_factors_of_exponent_ge_three (k l n : ℕ) (hk : 4 ≤ k) (hK : k ≤ 5)
    (hl : 3 ≤ l) (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  by_cases hn : n ≤ k
  · exact short_interval k l n (by omega) (by omega) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ := small_width_large_prime (by omega) hK (by omega : k < n)
  have hgrowth := modulus_growth_of_large_prime (by omega) (by omega) hpk hp hm hd (h p hpk.le hp)
  have hcount := prime_counting_bound_of_failure (by omega) hgrowth
    (r := l - 1) (by omega) (by omega) h
  have hpc : ((range k).filter Nat.Prime).card = 2 := by interval_cases k <;> decide
  rw [hpc] at hcount
  have hcho : (l + 2).choose (l - 1) ≤ (k + (l - 1) - 1).choose (l - 1) :=
    Nat.choose_le_choose _ (by omega)
  exact (not_lt_of_ge hcount) ((choose_three_gt_sq hl).trans_le hcho)

theorem five_factors (l n : ℕ) (hl : 2 ≤ l) (hend : ErdosSelfridge.firstPrimeAtLeast 5 ≤ n + 5) :
    ∃ p, 5 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 5), m) p) := by
  by_cases hl3 : 3 ≤ l
  · exact four_or_five_factors_of_exponent_ge_three 5 l n (by decide) (by decide) hl3 hend
  have hl2 : l = 2 := by omega
  subst l
  by_cases hn : n ≤ 5
  · exact short_interval 5 2 n (by decide) (by decide) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ :=
    small_width_large_prime (by decide : 3 ≤ 5) (by decide) (by omega : 5 < n)
  have hgrowth := modulus_growth_of_large_prime (by decide) (by decide) hpk hp hm hd (h p hpk.le hp)
  have hcount := prime_counting_bound_of_failure (by decide) hgrowth
    (r := 1) (by decide) (by decide) h
  have hf : ((range 5).filter Nat.Prime).card = 2 := by decide
  rw [hf] at hcount
  norm_num at hcount


private theorem not_square_four_factors (n b : ℕ) :
    (∏ j ∈ Icc (n + 1) (n + 4), j) ≠ b ^ 2 := by
  intro hb
  let A := n ^ 2 + 5 * n + 5
  have hd : (∏ j ∈ Icc (n + 1) (n + 4), j) + 1 = A ^ 2 := by
    have h4 := prod_Icc_succ_top (a := n + 1) (b := n + 3) (by omega) (fun j => j)
    have h3 := prod_Icc_succ_top (a := n + 1) (b := n + 2) (by omega) (fun j => j)
    have h2 := prod_Icc_succ_top (a := n + 1) (b := n + 1) (by omega) (fun j => j)
    change (∏ j ∈ Icc (n + 1) (n + 4), j) = _ at h4
    change (∏ j ∈ Icc (n + 1) (n + 3), j) = _ at h3
    change (∏ j ∈ Icc (n + 1) (n + 2), j) = _ at h2
    rw [h4, h3, h2, Icc_self, prod_singleton]
    dsimp [A]
    ring
  rw [hb] at hd
  have hlt : b < A := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have hb0 : b ≠ 0 := by
    intro hz
    apply (prod_ne_zero_iff.mpr (fun j hj => by have := (mem_Icc.mp hj).1; omega) :
        (∏ j ∈ Icc (n + 1) (n + 4), j) ≠ 0)
    simp [hb, hz]
  have hineq := Nat.pow_le_pow_left (show b + 1 ≤ A by omega) 2
  nlinarith only [hineq, hd, show 0 < b by omega]

theorem four_factors (l n : ℕ) (hl : 2 ≤ l) (hend : ErdosSelfridge.firstPrimeAtLeast 4 ≤ n + 4) :
    ∃ p, 4 ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + 4), m) p) := by
  by_cases hl3 : 3 ≤ l
  · exact four_or_five_factors_of_exponent_ge_three 4 l n (by decide) (by decide) hl3 hend
  have hl2 : l = 2 := by omega
  subst l
  by_cases hn : n ≤ 4
  · exact short_interval 4 2 n (by decide) (by decide) hend hn
  by_contra! h
  obtain ⟨p, m, hpk, hp, hm, hd⟩ :=
    small_width_large_prime (by decide : 3 ≤ 4) (by decide) (by omega : 4 < n)
  have hlarge := modulus_growth_of_large_prime (by decide) (by decide) hpk hp hm hd (h p hpk.le hp)
  let I := Icc (n + 1) (n + 4)
  let f (j : I) : Fin 2 × Fin 2 :=
    (⟨(j : ℕ).factorization 2 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨(j : ℕ).factorization 3 % 2, Nat.mod_lt _ (by decide)⟩)
  have hj0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hout (j : ℕ) (hj : j ∈ I) (p : ℕ) (h₂ : p ≠ 2) (h₃ : p ≠ 3) :
      j.factorization p % 2 = 0 := by
    by_cases hp : p.Prime
    · have := hp.two_le
      rw [← powerFreePart_factorization]
      exact powerFreePart_of_failed_large_prime n 4 2 h hj (by omega)
    · simp [Nat.factorization_eq_zero_of_not_prime j hp]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hlo (a : I) : n < (a : ℕ) := by have := (mem_Icc.mp a.property).1; omega
    have hhi (a : I) : (a : ℕ) ≤ n + 4 := (mem_Icc.mp a.property).2
    apply eq_of_close_equal_residues
      (k := 4) (r := 1) (by decide) hlarge (by decide) (by decide)
      (by simpa using hlo a) (by simpa using hhi a)
      (by simpa using hlo b) (by simpa using hhi b)
    intro p
    by_cases h₂ : p = 2
    · subst p
      exact congrArg (fun z : Fin 2 × Fin 2 => z.1.val) hab
    · by_cases h₃ : p = 3
      · subst p
        exact congrArg (fun z : Fin 2 × Fin 2 => z.2.val) hab
      · rw [hout _ a.property _ h₂ h₃, hout _ b.property _ h₂ h₃]
  have hcard : Fintype.card I = Fintype.card (Fin 2 × Fin 2) := by
    simp [I, Nat.card_Icc]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)
  have sumFirst : (∑ j ∈ I, j.factorization 2 % 2) = 2 := by
    rw [← sum_coe_sort I]
    change (∑ j : I, (e j).1.val) = 2
    rw [Fintype.sum_equiv e _ (fun z => z.1.val) (fun _ => rfl)]
    decide
  have sumSecond : (∑ j ∈ I, j.factorization 3 % 2) = 2 := by
    rw [← sum_coe_sort I]
    change (∑ j : I, (e j).2.val) = 2
    rw [Fintype.sum_equiv e _ (fun z => z.2.val) (fun _ => rfl)]
    decide
  let A := ∏ j ∈ I, j
  have A0 : A ≠ 0 := prod_ne_zero_iff.mpr hj0
  have hmod (p : ℕ) : A.factorization p % 2 = 0 := by
    rw [show A.factorization p = ∑ j ∈ I, j.factorization p from Nat.factorization_prod_apply hj0]
    have hh : (∑ j ∈ I, j.factorization p) ≡ ∑ j ∈ I, j.factorization p % 2 [MOD 2] := by
      apply Nat.ModEq.sum
      intro j _
      simp [Nat.ModEq]
    change _ % 2 = _ % 2 at hh
    rw [hh]
    by_cases h₂ : p = 2
    · simp [h₂, sumFirst]
    · by_cases h₃ : p = 3
      · simp [h₃, sumSecond]
      · rw [sum_eq_zero (fun j hj => hout j hj p h₂ h₃), Nat.zero_mod]
  have hExp : powerFreeExponents 2 A = 0 := by
    ext p
    exact hmod p
  have hFree : powerFreePart 2 A = 1 := by
    simp [powerFreePart, hExp]
  have hPow := powerFreePart_mul_powerRoot 2 A A0
  rw [hFree, one_mul] at hPow
  exact not_square_four_factors n (powerRoot 2 A) hPow.symm


private theorem powerFreePart_nonzero {l m : ℕ} (hm : m ≠ 0) :
    powerFreePart l m ≠ 0 :=
  fun h => hm (zero_dvd_iff.mp (h ▸ powerFreePart_dvd l m))

private theorem powerFreePart_mul_residue {l x y p : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (powerFreePart l x * powerFreePart l y).factorization p % l =
      (x * y).factorization p % l := by
  rw [Nat.factorization_mul (powerFreePart_nonzero hx) (powerFreePart_nonzero hy),
    Nat.factorization_mul hx hy]
  simp only [Finsupp.add_apply, powerFreePart_factorization]
  exact (Nat.add_mod _ _ _).symm


theorem full_product_powerFreePart_dvd_factorial_mul_primorial_pow (n k l : ℕ)
    (hk : 0 < k) (hl : 0 < l)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart l j) ∣
      (k - 1).factorial * ∏ p ∈ (range k).filter Nat.Prime, p ^ (l - 1) := by
  classical
  let I := Icc (n + 1) (n + k)
  let P := (range k).filter Nat.Prime
  have hI : I.Nonempty := ⟨n + 1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have h0 (j : ℕ) (hj : j ∈ I) : powerFreePart l j ≠ 0 := by
    apply powerFreePart_nonzero
    have := (mem_Icc.mp hj).1
    omega
  have hP0 (q : ℕ) (hq : q ∈ P) : q ^ (l - 1) ≠ 0 :=
    pow_ne_zero _ (mem_filter.mp hq).2.ne_zero
  have hR0 : (∏ q ∈ P, q ^ (l - 1)) ≠ 0 := prod_ne_zero_iff.mpr hP0
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr h0)
    (mul_ne_zero (Nat.factorial_ne_zero _) hR0)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p < k
    · have hp' : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hp⟩
      obtain ⟨m, hm, hmmax⟩ := exists_max_image I (fun j => j.factorization p) hI
      have hF := factorization_after_max_removal_le hp hm hmmax
        (S := I.erase m) Subset.rfl (fun j _ => powerFreePart_dvd l j)
      have hF0 (j : ℕ) (hj : j ∈ I.erase m) : powerFreePart l j ≠ 0 :=
        h0 j (mem_of_mem_erase hj)
      rw [Nat.factorization_prod_apply hF0] at hF
      have hR : (∏ q ∈ P, q ^ (l - 1)).factorization p = l - 1 := by
        rw [Nat.factorization_prod_apply hP0]
        calc
          _ = (p ^ (l - 1)).factorization p := by
            apply sum_eq_single_of_mem p hp'
            intro q hq hqp
            rw [(mem_filter.mp hq).2.factorization_pow, Finsupp.single_eq_of_ne hqp.symm]
          _ = _ := Nat.factorization_pow_self hp
      change (∏ j ∈ I, powerFreePart l j).factorization p ≤
        ((k - 1).factorial * ∏ q ∈ P, q ^ (l - 1)).factorization p
      rw [Nat.factorization_prod_apply h0, Nat.factorization_mul (Nat.factorial_ne_zero _) hR0,
        Finsupp.add_apply, hR]
      rw [← sum_erase_add _ _ hm]
      have h := Nat.mod_lt (m.factorization p) hl
      rw [powerFreePart_factorization]
      omega
    · change (∏ j ∈ I, powerFreePart l j).factorization p ≤ _
      rw [Nat.factorization_prod_apply h0, sum_eq_zero]
      · exact Nat.zero_le _
      · exact fun j hj => powerFreePart_of_failed_large_prime n k l hf hj (by omega)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _


private theorem scaled_prod_ge_of_card_below (A : Finset ℕ) (D a b : ℕ) (ha : 0 < a)
    (hA : ∀ j ∈ A, 0 < j)
    (hcount : ∀ x, a * (A.filter (· ≤ x)).card ≤ b * x + D) :
    a ^ (A.card - D) * (A.card - D).factorial ≤ b ^ (A.card - D) * A.prod id := by
  classical
  let e := A.orderEmbOfFin rfl
  have ranked (i : Fin A.card) : a * (i.val + 1) ≤ b * e i + D := by
    let f : Fin (i.val + 1) ↪ ℕ :=
      ⟨fun j => e ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        fun j z h => Fin.ext (congrArg (fun z : Fin A.card => z.val) (e.injective h))⟩
    have hsub : Finset.univ.map f ⊆ A.filter (· ≤ e i) := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := mem_map.mp ha
      apply mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl _, e.monotone (by
        change j.val ≤ i.val
        omega)⟩
    have h := card_le_card hsub
    simp only [card_map, card_univ, Fintype.card_fin] at h
    exact (Nat.mul_le_mul_left _ h).trans (hcount _)
  let m := A.card - D
  let g : Fin m ↪ ℕ :=
    ⟨fun j => e ⟨D + j.val, by have := j.isLt; dsimp [m] at this; omega⟩,
      fun j z h => Fin.ext (by
        have h' := congrArg Fin.val (e.injective h)
        change D + j.val = D + z.val at h'
        omega)⟩
  have hmono (i : Fin m) : a * (i.val + 1) ≤ b * g i := by
    have h := ranked ⟨D + i.val, by have := i.isLt; dsimp [m] at this; omega⟩
    change a * (D + i.val + 1) ≤ b * g i + D at h
    rw [show a * (D + i.val + 1) = a * D + a * (i.val + 1) by ring] at h
    have hD : D ≤ a * D := Nat.le_mul_of_pos_left _ ha
    omega
  have hA' : Finset.univ.map g ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl _
  have hmul : (∏ i : Fin m, a * (i.val + 1)) = a ^ m * m.factorial := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), prod_range_add_one_eq_factorial]
  change a ^ m * m.factorial ≤ b ^ m * A.prod id
  rw [← hmul]
  calc
    (∏ i : Fin m, a * (i.val + 1)) ≤ ∏ i : Fin m, b * g i :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hmono i)
    _ = b ^ m * (Finset.univ.map g).prod id := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_map]
      rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (prod_le_prod_of_subset_of_one_le' hA' (fun _ hj _ => hA _ hj))

private theorem powerFreePart_injOn_interval {n k l : ℕ} (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hS : S ⊆ Icc (n + 1) (n + k)) :
    Set.InjOn (powerFreePart l) S := by
  intro x hx y hy hxy
  have hxl := (mem_Icc.mp (hS hx)).1
  have hxh := (mem_Icc.mp (hS hx)).2
  have hyl := (mem_Icc.mp (hS hy)).1
  have hyh := (mem_Icc.mp (hS hy)).2
  apply eq_of_close_equal_residues (r := 1) hk hn (by decide) (by omega)
    (by simpa using hxl) (by simpa using hxh) (by simpa using hyl) (by simpa using hyh)
  intro p
  rw [← powerFreePart_factorization, ← powerFreePart_factorization, hxy]


private def intervalMultipleCount (n k d : ℕ) : ℕ :=
  ((Icc (n + 1) (n + k)).filter (d ∣ ·)).card

private theorem intervalMultipleCount_bounds (n k d : ℕ) (hd : 0 < d) :
    k / d ≤ intervalMultipleCount n k d ∧ intervalMultipleCount n k d ≤ k / d + 1 := by
  have hI : Icc (n + 1) (n + k) = Ioc 0 (n + k) \ Ioc 0 n := by
    ext j
    simp only [mem_Icc, mem_sdiff, mem_Ioc]
    omega
  have hs : ((Ioc 0 n).filter (d ∣ ·)) ⊆ (Ioc 0 (n + k)).filter (d ∣ ·) := by
    intro j hj
    have h := mem_filter.mp hj
    have h' := mem_Ioc.mp h.1
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h'.1, by omega⟩, h.2⟩
  have hfilter : (Icc (n + 1) (n + k)).filter (d ∣ ·) =
      ((Ioc 0 (n + k)).filter (d ∣ ·)) \ ((Ioc 0 n).filter (d ∣ ·)) := by
    rw [hI]
    ext j
    simp only [mem_filter, mem_sdiff]
    tauto
  unfold intervalMultipleCount
  rw [hfilter, card_sdiff_of_subset hs, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div, Nat.add_div hd, Nat.add_assoc, Nat.add_sub_cancel_left]
  constructor
  · exact Nat.le_add_right _ _
  · apply Nat.add_le_add_left
    split <;> decide

private theorem sum_le_factorial_factorization {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    (∑ i ∈ Ico 1 b, a / p ^ i) ≤ a.factorial.factorization p := by
  let B := max b (Nat.log p a + 1)
  have hB : Nat.log p a < B := Nat.lt_of_succ_le (le_max_right _ _)
  rw [Nat.factorization_factorial hp hB]
  exact sum_le_sum_of_subset (Ico_subset_Ico_right (le_max_left _ _))

private theorem squareFreePart_factorization_plus_two_le {n k p : ℕ} (hp : p.Prime) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j).factorization p + k / p ^ 2 ≤
      k / p + k / p ^ 3 + 2 := by
  let I := Icc (n + 1) (n + k)
  have h0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hP (j : ℕ) (hj : j ∈ I) : powerFreePart 2 j ≠ 0 := powerFreePart_nonzero (h0 j hj)
  have hpoint (j : ℕ) (hj : j ∈ I) :
      j.factorization p % 2 + (if p ^ 2 ∣ j then 1 else 0) ≤
        (if p ∣ j then 1 else 0) + (if p ^ 3 ∣ j then 1 else 0) := by
    have hp1 : p ∣ j ↔ 1 ≤ j.factorization p := by
      simpa only [pow_one] using (hp.pow_dvd_iff_le_factorization (h0 j hj) (k := 1))
    simp only [hp1, hp.pow_dvd_iff_le_factorization (h0 j hj)]
    split <;> split <;> split <;> omega
  have h := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_boole] at h
  change (∑ j ∈ I, j.factorization p % 2) + intervalMultipleCount n k (p ^ 2) ≤
      intervalMultipleCount n k p + intervalMultipleCount n k (p ^ 3) at h
  change (∏ j ∈ I, powerFreePart 2 j).factorization p + k / p ^ 2 ≤ _
  rw [Nat.factorization_prod_apply hP]
  simp only [powerFreePart_factorization]
  have h1 := (intervalMultipleCount_bounds n k p hp.pos).2
  have h2 := (intervalMultipleCount_bounds n k (p ^ 2) (pow_pos hp.pos _)).1
  have h3 := (intervalMultipleCount_bounds n k (p ^ 3) (pow_pos hp.pos _)).2
  omega

private theorem squareFreePart_two_factorization_plus_two_four_le (n k : ℕ) :
    (∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j).factorization 2 + k / 4 + k / 16 ≤
      k / 2 + k / 8 + k / 32 + 3 := by
  let I := Icc (n + 1) (n + k)
  have h0 (j : ℕ) (hj : j ∈ I) : j ≠ 0 := by
    have := (mem_Icc.mp hj).1
    omega
  have hP (j : ℕ) (hj : j ∈ I) : powerFreePart 2 j ≠ 0 := powerFreePart_nonzero (h0 j hj)
  have hcond (j : ℕ) (hj : j ∈ I) (i : ℕ) : 2 ^ i ∣ j ↔ i ≤ j.factorization 2 :=
    Nat.prime_two.pow_dvd_iff_le_factorization (h0 j hj)
  have hpoint (j : ℕ) (hj : j ∈ I) :
      j.factorization 2 % 2 + (if 4 ∣ j then 1 else 0) + (if 16 ∣ j then 1 else 0) ≤
        (if 2 ∣ j then 1 else 0) + (if 8 ∣ j then 1 else 0) + (if 32 ∣ j then 1 else 0) := by
    have h1 := hcond j hj 1
    have h2 := hcond j hj 2
    have h3 := hcond j hj 3
    have h4 := hcond j hj 4
    have h5 := hcond j hj 5
    norm_num at h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5]
    split <;> split <;> split <;> split <;> split <;> omega
  have h := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_boole] at h
  change (∑ j ∈ I, j.factorization 2 % 2) + intervalMultipleCount n k 4 +
      intervalMultipleCount n k 16 ≤
        intervalMultipleCount n k 2 + intervalMultipleCount n k 8 +
          intervalMultipleCount n k 32 at h
  change (∏ j ∈ I, powerFreePart 2 j).factorization 2 + k / 4 + k / 16 ≤ _
  rw [Nat.factorization_prod_apply hP]
  simp only [powerFreePart_factorization]
  have h1 := (intervalMultipleCount_bounds n k 2 (by decide)).2
  have h2 := (intervalMultipleCount_bounds n k 4 (by decide)).1
  have h3 := (intervalMultipleCount_bounds n k 8 (by decide)).2
  have h4 := (intervalMultipleCount_bounds n k 16 (by decide)).1
  have h5 := (intervalMultipleCount_bounds n k 32 (by decide)).2
  omega


private theorem squarefree_count_le (x : ℕ) :
    3 * ((Icc 1 x).filter Squarefree).card ≤ 2 * x + 6 := by
  classical
  let I := Ioc 0 x
  let D₄ := I.filter (4 ∣ ·)
  let D₉ := I.filter (9 ∣ ·)
  let F := I.filter Squarefree
  have h4 : D₄.card = x / 4 := Nat.Ioc_filter_dvd_card_eq_div _ _
  have h9 : D₉.card = x / 9 := Nat.Ioc_filter_dvd_card_eq_div _ _
  have hI : Icc 1 x = I := by
    ext j
    simp only [I, mem_Icc, mem_Ioc]
    omega
  have hcap : D₄ ∩ D₉ = I.filter (36 ∣ ·) := by
    ext j
    simp only [D₄, D₉, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hj, h4⟩, _, h9⟩
      exact ⟨hj, (show Nat.lcm 4 9 = 36 by decide) ▸ Nat.lcm_dvd h4 h9⟩
    · rintro ⟨hj, hd⟩
      exact ⟨⟨hj, dvd_trans (by decide : 4 ∣ 36) hd⟩,
        hj, dvd_trans (by decide : 9 ∣ 36) hd⟩
  have hsum := card_union_add_card_inter D₄ D₉
  rw [h4, h9, hcap, Nat.Ioc_filter_dvd_card_eq_div] at hsum
  have hs : Disjoint F (D₄ ∪ D₉) := by
    rw [disjoint_left]
    intro j hj hm
    have hF := (mem_filter.mp hj).2
    rcases mem_union.mp hm with hm | hm
    · have h := (Nat.prime_two.pow_dvd_iff_le_factorization hF.ne_zero (k := 2)).1
        (mem_filter.mp hm).2
      have := hF.natFactorization_le_one 2
      omega
    · have h := ((show Nat.Prime 3 by decide).pow_dvd_iff_le_factorization
        hF.ne_zero (k := 2)).1 (mem_filter.mp hm).2
      have := hF.natFactorization_le_one 3
      omega
  have hsub : F ∪ (D₄ ∪ D₉) ⊆ I := by
    exact union_subset (filter_subset _ _) (union_subset (filter_subset _ _) (filter_subset _ _))
  have hBound := card_le_card hsub
  rw [card_union_of_disjoint hs, Nat.card_Ioc, Nat.sub_zero] at hBound
  rw [hI]
  change 3 * F.card ≤ 2 * x + 6
  omega

private theorem squareFreePart_prod_lower_bound {n k : ℕ} (hk : 3 ≤ k) (hn : k ^ 2 < n) :
    3 ^ (k - 6) * (k - 6).factorial ≤
      2 ^ (k - 6) * ∏ j ∈ Icc (n + 1) (n + k), powerFreePart 2 j := by
  classical
  let I := Icc (n + 1) (n + k)
  let f := powerFreePart 2
  let A := I.image f
  have hI : I.card = k := by simp [I, Nat.card_Icc]
  have hi : Set.InjOn f I := powerFreePart_injOn_interval hk (by decide) hn I Subset.rfl
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a ∧ Squarefree a := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    have hjpos := (mem_Icc.mp hj).1
    have h0 := powerFreePart_nonzero (l := 2) (m := j) (by omega)
    refine ⟨Nat.pos_of_ne_zero h0, Nat.squarefree_of_factorization_le_one h0 ?_⟩
    intro p
    rw [powerFreePart_factorization]
    omega
  have hcount (x : ℕ) : 3 * (A.filter (· ≤ x)).card ≤ 2 * x + 6 := by
    have hs : A.filter (· ≤ x) ⊆ (Icc 1 x).filter Squarefree := by
      intro j hj
      obtain ⟨hj, hle⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hA j hj).1, hle⟩, (hA j hj).2⟩
    exact (Nat.mul_le_mul_left _ (card_le_card hs)).trans (squarefree_count_le x)
  have h := scaled_prod_ge_of_card_below A 6 3 2 (by decide) (fun a ha => (hA a ha).1) hcount
  simpa only [A, card_image_of_injOn hi, hI, prod_image hi, id_eq] using h


private def squareSavingPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

private def squareSaving (p : ℕ) : ℕ :=
  match p with
  | 2 => 650
  | 3 => 239
  | 5 => 81
  | 7 => 41
  | 11 => 16
  | 13 => 11
  | _ => 0


private theorem squareSavingPrime {p : ℕ} (hp : p ∈ squareSavingPrimes) : p.Prime := by
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide


private theorem real_nat_div_bounds (x d : ℕ) (hd : 0 < d) :
    (x : ℝ) / d - 1 ≤ ((x / d : ℕ) : ℝ) ∧ ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h : (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast Nat.div_add_mod x d
  have hm : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt x hd
  have hm0 : 0 ≤ ((x % d : ℕ) : ℝ) := by positivity
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ hdR]
    linarith only [h, hm, add_mul (((x / d : ℕ) : ℝ)) 1 (d : ℝ),
      mul_comm (d : ℝ) (((x / d : ℕ) : ℝ)), one_mul (d : ℝ)]
  · rw [le_div_iff₀ hdR]
    linarith only [h, hm0, mul_comm (d : ℝ) (((x / d : ℕ) : ℝ))]


private theorem offDiag_eq_of_valuation_differences {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hSI : S ⊆ Icc (n + 1) (n + k))
    (x y : S.offDiag)
    (hDiff : ∀ p : ℕ, (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l) =
      (y.val.1.factorization p : ZMod l) - (y.val.2.factorization p : ZMod l)) :
    x = y := by
  have h0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  rcases x with ⟨⟨a, b⟩, hab⟩
  rcases y with ⟨⟨c, d⟩, hcd⟩
  have ⟨ha, hb, hne⟩ := mem_offDiag.mp hab
  have ⟨hc, hd, _⟩ := mem_offDiag.mp hcd
  have hFac (p : ℕ) : (a * d).factorization p % l = (c * b).factorization p % l := by
    rw [Nat.factorization_mul (h0 a ha) (h0 d hd), Nat.factorization_mul (h0 c hc) (h0 b hb)]
    simp only [Finsupp.add_apply]
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    push_cast
    exact sub_eq_sub_iff_add_eq_add.mp (hDiff p)
  have het := interval_products_residue_injective (r := 2) hk hn (by decide) (by omega)
    (a ::ₘ d ::ₘ 0) (c ::ₘ b ::ₘ 0) (by simp) (by simp)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI ha
        · exact hSI hd)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hc
        · exact hSI hb)
    (by simpa using hFac)
  have ham : a ∈ (c ::ₘ b ::ₘ 0 : Multiset ℕ) := het ▸ Multiset.mem_cons_self _ _
  have hae : a = c := (by simpa using ham : a = c ∨ a = b).resolve_right hne
  subst c
  have hedb : d = b := by simpa using het
  subst d
  rfl

private theorem natCast_eq_zero_zmod_of_mod_eq_zero {v l : ℕ} (h : v % l = 0) :
    (v : ZMod l) = 0 := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff']
  simpa using h

theorem ordered_pair_counting_obstruction {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S P : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hP : ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0) :
    S.card * (S.card - 1) ≤ l ^ P.card := by
  classical
  let _ : NeZero l := ⟨by omega⟩
  let f (x : S.offDiag) (p : P) : ZMod l :=
    (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l)
  have inj : Function.Injective f := by
    intro x y hxy
    apply offDiag_eq_of_valuation_differences hk hl hn S hSI x y
    intro p
    by_cases hp : p ∈ P
    · exact congrFun hxy (⟨p, hp⟩ : P)
    · have hx := mem_offDiag.mp x.property
      have hy := mem_offDiag.mp y.property
      rw [natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hx.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hx.2.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hy.1 p hp),
        natCast_eq_zero_zmod_of_mod_eq_zero (hP _ hy.2.1 p hp)]
  have h := Fintype.card_le_of_injective f inj
  simpa [Fintype.card_fun, ZMod.card, offDiag_card, Nat.mul_sub_left_distrib] using h

private def unretainedPrimes (k : ℕ) (P : Finset ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime) \ P

private def sieveUpperCount (k : ℕ) (P : Finset ℕ) : ℕ :=
  ∑ p ∈ unretainedPrimes k P, (k / p + 1)

private theorem sieveUpperCount_mono (P : Finset ℕ) : Monotone (sieveUpperCount · P) := by
  intro a b hab
  unfold sieveUpperCount
  have hs : unretainedPrimes a P ⊆ unretainedPrimes b P := by
    intro p hp
    have hp' := mem_sdiff.mp hp
    have hp'' := mem_filter.mp hp'.1
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr
      ((mem_range.mp hp''.1).trans_le hab), hp''.2⟩, hp'.2⟩
  calc
    _ ≤ ∑ p ∈ unretainedPrimes a P, (b / p + 1) :=
      sum_le_sum (fun p _ => Nat.add_le_add_right (Nat.div_le_div_right hab) _)
    _ ≤ _ := sum_le_sum_of_subset hs

private theorem small_prime_sieve {n k l : ℕ} (P : Finset ℕ)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - sieveUpperCount k P ≤ S.card ∧
      ∀ j ∈ S, ∀ p ∉ P, j.factorization p % l = 0 := by
  classical
  let I := Icc (n + 1) (n + k)
  let Q := unretainedPrimes k P
  let D := Q.biUnion (fun p => I.filter (p ∣ ·))
  let S := I \ D
  have hDI : D ⊆ I := by
    intro j hj
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hp).1
  have hD : D.card ≤ sieveUpperCount k P := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro p hp
    have hp' := (mem_filter.mp (mem_sdiff.mp hp).1).2
    exact (intervalMultipleCount_bounds n k p hp'.pos).2
  have hcard : I.card = k := by simp [I, Nat.card_Icc]
  refine ⟨S, sdiff_subset, ?_, ?_⟩
  · change k - _ ≤ (I \ D).card
    rw [card_sdiff_of_subset hDI, hcard]
    exact Nat.sub_le_sub_left hD _
  intro j hj p hp
  have hj' := mem_sdiff.mp hj
  by_cases hprime : p.Prime
  · by_cases hpk : p < k
    · have hpQ : p ∈ Q := mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpk, hprime⟩, hp⟩
      have hdvd : ¬ p ∣ j := fun h => hj'.2 (mem_biUnion.mpr
        ⟨p, hpQ, mem_filter.mpr ⟨hj'.1, h⟩⟩)
      simp [Nat.factorization_eq_zero_of_not_dvd hdvd]
    · rw [← powerFreePart_factorization]
      exact powerFreePart_of_failed_large_prime n k l hf hj'.1 (by omega)
  · simp [Nat.factorization_eq_zero_of_not_prime j hprime]


private theorem power_ratio_from_five {f m l : ℕ} (hl : 5 ≤ l)
    (hBase : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    (l + 1) ^ m * l ≤ (l + (f - 1)) * l ^ m := by
  have lpos : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have l5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  let u : ℝ := ((f - 1 : ℕ) : ℝ)
  let t : ℝ := 5 / l
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_iff₀ lpos).2 (by simpa using l5)
  have hrate : 5 * ((6 / 5 : ℝ) ^ m - 1) ≤ u := by
    have hB : 5 * (6 : ℝ) ^ m ≤ (u + 5) * (5 : ℝ) ^ m := by
      dsimp [u]
      exact_mod_cast hBase
    have hg : 0 < (5 : ℝ) ^ m := pow_pos (by norm_num) m
    apply (mul_le_mul_iff_left₀ hg).1
    calc
      5 * ((6 / 5 : ℝ) ^ m - 1) * (5 : ℝ) ^ m =
          5 * (6 : ℝ) ^ m - 5 * (5 : ℝ) ^ m := by
        rw [div_pow]
        field_simp
      _ ≤ u * (5 : ℝ) ^ m := by
        rw [add_mul] at hB
        linarith only [hB]
  have hc := (convexOn_pow (𝕜 := ℝ) m).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (6 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
    (sub_nonneg.mpr ht1) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_one, one_pow] at hc
  have hmix : 1 - t + t * (6 / 5 : ℝ) = ((l : ℝ) + 1) / (l : ℝ) := by
    dsimp [t]
    field_simp; ring
  rw [hmix] at hc
  have hf : (((l : ℝ) + 1) / (l : ℝ)) ^ m ≤ ((l : ℝ) + u) / (l : ℝ) := by
    apply hc.trans
    calc
      1 - t + t * (6 / 5 : ℝ) ^ m = ((l : ℝ) + 5 * ((6 / 5 : ℝ) ^ m - 1)) / (l : ℝ) := by
        dsimp [t]
        field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hrate]) lpos.le
  rw [div_pow, div_le_div_iff₀ (pow_pos lpos _) lpos] at hf
  dsimp [u] at hf
  exact_mod_cast hf

private theorem choose_gt_pow_from_five {f m l : ℕ} (hf : 2 ≤ f) (hl : 5 ≤ l)
    (hBase : 5 ^ m < (f + 3).choose (f - 1))
    (hRatio : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    l ^ m < (f + l - 2).choose (f - 1) := by
  induction l, hl using Nat.le_induction with
  | base => simpa only [show f + 5 - 2 = f + 3 by omega] using hBase
  | succ l hld ih =>
    have hr := power_ratio_from_five hld hRatio
    have h1 : f + l - 2 + 1 = f + (l + 1) - 2 := by omega
    have h2 : f + l - 2 + 1 - (f - 1) = l := by omega
    have h3 : l + (f - 1) = f + l - 2 + 1 := by omega
    rw [h3, h1] at hr
    have he := Nat.choose_mul_succ_eq (f + l - 2) (f - 1)
    rw [h2] at he
    have hp : 0 < f + l - 2 + 1 := by omega
    have hi : l ^ m * (f + l - 2 + 1) <
        (f + l - 2).choose (f - 1) * (f + l - 2 + 1) :=
      Nat.mul_lt_mul_of_pos_right ih hp
    rw [mul_comm (l ^ m)] at hi
    rw [he, h1] at hi
    exact Nat.lt_of_mul_lt_mul_right (hr.trans_lt hi)


private def sievePrimeSet (m : ℕ) : Finset ℕ :=
  ([2, 3, 5, 7, 11, 13, 17, 19].take m).toFinset

private structure SieveSeed (f m : ℕ) : Prop where
  card_eq : (sievePrimeSet m).card = m
  width : 2 ≤ f
  cube : 3 ^ m < f * (f - 1)
  fifth : 5 ^ m < (f + 3).choose 4
  ratio : 5 * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m


private theorem fifthCertificate {f m : ℕ} (h : 5 ^ m < f.ascFactorial 4 / (4 : ℕ).factorial) :
    5 ^ m < (f + 3).choose 4 := by
  rw [show f + 3 = f + 4 - 1 by omega, Nat.choose_eq_asc_factorial_div_factorial' f 4]
  exact h

private theorem sieveSeed2 : SieveSeed 4 2 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed3 : SieveSeed 6 3 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed4 : SieveSeed 10 4 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed5 : SieveSeed 17 5 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed6 : SieveSeed 28 6 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed7 : SieveSeed 48 7 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩
private theorem sieveSeed8 : SieveSeed 82 8 := ⟨by decide, by decide, by decide, fifthCertificate (by decide), by decide⟩

private inductive SieveCover : ℕ → ℕ → Prop
  | done (a : ℕ) : SieveCover a a
  | more {a b c f m : ℕ} (seed : SieveSeed f m) (hab : a < b)
      (cover : f + sieveUpperCount (b - 1) (sievePrimeSet m) ≤ a)
      (rest : SieveCover b c) : SieveCover a c


private def avoidsDivisors (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | d, fuel + 1 =>
    if n < d * d then true else decide (n % d ≠ 0) && avoidsDivisors n (d + 1) fuel

private theorem avoidsDivisors_eq_true (n d fuel : ℕ) :
    avoidsDivisors n d fuel = true ↔
      ∀ q, d ≤ q → q < d + fuel → q * q ≤ n → ¬q ∣ n := by
  induction fuel generalizing d with
  | zero =>
    simp only [avoidsDivisors, Nat.add_zero, true_iff]
    omega
  | succ fuel ih =>
    rw [avoidsDivisors]
    split
    next h =>
      simp only [true_iff]
      intro q hd _ hq
      have hmul := Nat.mul_le_mul hd hd
      omega
    next h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih, Nat.dvd_iff_mod_eq_zero]
      constructor
      · rintro ⟨hfirst, hrest⟩ q hd hq hqn
        by_cases heq : q = d
        · simpa only [heq] using hfirst
        · exact hrest q (by omega) (by omega) hqn
      · intro htrial
        exact ⟨htrial d le_rfl (by omega) (by omega), fun q hq hupper hqn =>
          htrial q (by omega) (by omega) hqn⟩

private def primeTest (p : ℕ) : Bool :=
  decide (2 ≤ p) && avoidsDivisors p 2 p

private theorem primeTest_eq_true {p : ℕ} : primeTest p = true ↔ p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, avoidsDivisors_eq_true, Nat.le_sqrt]
  apply and_congr_right'
  constructor
  · intro h q hq hqp
    have hle := Nat.le_mul_self q
    exact h q hq (by omega) hqp
  · intro h q hq _ hqp
    exact h q hq hqp

set_option maxRecDepth 4096 in
private def sievePrimeList : List ℕ := [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
    367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
    509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593,
    599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
    751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
    829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911,
    919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997
  ]

set_option maxRecDepth 4096 in
private def sievePrimeTable : Finset ℕ := ⟨sievePrimeList, by decide +kernel⟩

set_option maxRecDepth 8192 in
private theorem sievePrimeList_eq : ((List.range 1001).filter primeTest) = sievePrimeList := by
  decide +kernel

private theorem sievePrimeTable_eq : (range 1001).filter Nat.Prime = sievePrimeTable := by
  ext p
  change p ∈ (range 1001).filter Nat.Prime ↔ p ∈ (sievePrimeList : Multiset ℕ)
  rw [Multiset.mem_coe, ← sievePrimeList_eq]
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_filter, List.mem_range, primeTest_eq_true]

private theorem sieveUpperCount_use_table {k : ℕ} (hk : k ≤ 1001) (P : Finset ℕ) :
    sieveUpperCount k P = ∑ p ∈ (sievePrimeTable.filter (· < k)) \ P, (k / p + 1) := by
  have h : (range k).filter Nat.Prime = sievePrimeTable.filter (· < k) := by
    rw [← sievePrimeTable_eq]
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hpk, hp⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, hpk⟩
    · rintro ⟨⟨_, hp⟩, hpk⟩
      exact ⟨hpk, hp⟩
  simp only [sieveUpperCount, unretainedPrimes, h]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem sieveCover_to_thousand : SieveCover 6 1001 := by
  refine .more (b := 8) sieveSeed2 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 12) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 14) sieveSeed2 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 18) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 22) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 30) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 38) sieveSeed3 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 48) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 60) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 74) sieveSeed4 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 90) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 108) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 130) sieveSeed5 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 155) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 184) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 217) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 254) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 294) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 338) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 387) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 438) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 493) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 554) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 618) sieveSeed7 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 684) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 758) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 834) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 915) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 998) sieveSeed8 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  refine .more (b := 1001) sieveSeed6 (by decide) (by rw [sieveUpperCount_use_table (by decide)]; decide) ?_
  exact .done _

private theorem sieveCover_point {a b : ℕ} (h : SieveCover a b) :
    ∀ k, a ≤ k → k < b →
      ∃ f m, SieveSeed f m ∧ f + sieveUpperCount k (sievePrimeSet m) ≤ k := by
  induction h with
  | done a => intro k hlo hhi; omega
  | @more a b c f m hseed hab hv hrest ih =>
    intro k hk hc
    by_cases hkb : b ≤ k
    · exact ih k hkb hc
    · refine ⟨f, m, hseed, (Nat.add_le_add_left ?_ _).trans (hv.trans hk)⟩
      exact sieveUpperCount_mono (sievePrimeSet m) (by omega)

theorem width_up_to_thousand_for_exponent_three_or_five_le {n k l : ℕ}
    (hk : 6 ≤ k) (hK : k ≤ 1000) (hl : l = 3 ∨ 5 ≤ l)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  have hl3 : 3 ≤ l := by omega
  by_cases hn : n ≤ k
  · exact short_interval k l n (by omega) (by omega) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : (n + 1) + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by omega : 2 ≤ l) hpk hp hm hd (hf p hpk.le hp)
  obtain ⟨f, m, seed, hkf⟩ := sieveCover_point sieveCover_to_thousand k hk (by omega)
  obtain ⟨S, hSI, hsize, hs⟩ := small_prime_sieve (sievePrimeSet m) hf
  have hfs : f ≤ S.card := by omega
  rcases hl with rfl | hl
  · have h := ordered_pair_counting_obstruction (by omega) (by decide) hgt S (sievePrimeSet m) hSI hs
    rw [seed.card_eq] at h
    exact (not_lt_of_ge ((Nat.mul_le_mul hfs (Nat.sub_le_sub_right hfs 1)).trans h)) seed.cube
  · have h := counting_obstruction (by omega) hgt (r := l - 1)
      (by omega) (by omega) S (sievePrimeSet m) hSI hs
    rw [seed.card_eq] at h
    have hchoose := Nat.choose_le_choose (l - 1) (show f + (l - 1) - 1 ≤ S.card + (l - 1) - 1 by omega)
    have hs' : f + l - 2 - (f - 1) = l - 1 := by have := seed.width; omega
    have ht : f - 1 ≤ f + l - 2 := by omega
    have heq := Nat.choose_symm ht
    rw [hs'] at heq
    rw [show f + (l - 1) - 1 = f + l - 2 by omega, heq] at hchoose
    have hBase : 5 ^ m < (f + 3).choose (f - 1) := by
      have hs := Nat.choose_symm (by omega : f - 1 ≤ f + 3)
      rw [show f + 3 - (f - 1) = 4 by have := seed.width; omega] at hs
      exact hs ▸ seed.fifth
    exact (not_lt_of_ge (hchoose.trans h))
      (choose_gt_pow_from_five seed.width hl hBase seed.ratio)


private def optionalValuation {Q : Finset ℕ} (t : Option Q) (p : Q) : ℕ :=
  if t = some p then 1 else 0

private theorem sparsePrimeTailTag (S Q : Finset ℕ)
    (hS : ∀ j ∈ S, j ≠ 0) (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    ∃ tag : S → Option Q,
      ∀ (j : S) (p : Q), (j.val).factorization p = optionalValuation (tag j) p := by
  classical
  have hex (j : S) : ∃ t : Option Q,
      ∀ p : Q, j.val.factorization p = optionalValuation t p := by
    by_cases h : ∃ q : Q, (q : ℕ) ∣ j.val
    · obtain ⟨q, hq⟩ := h
      refine ⟨some q, ?_⟩
      intro p
      by_cases hpq : q = p
      · subst p
        simp [optionalValuation]
        have h1 := (hQ q q.property).factorization_pos_of_dvd (hS j j.property) hq
        have h2 : ¬ 2 ≤ j.val.factorization q := by
          intro h
          exact hPair j j.property q q.property q q.property
            (by simpa only [pow_two] using
              ((hQ q q.property).pow_dvd_iff_le_factorization (hS j j.property)).2 h)
        omega
      · have hqd : ¬ (p : ℕ) ∣ j.val := by
          intro hd
          have hne : (q : ℕ) ≠ (p : ℕ) := fun e => hpq (Subtype.ext e)
          have hcop := (Nat.coprime_primes (hQ q q.property) (hQ p p.property)).2 hne
          exact hPair j j.property q q.property p p.property (hcop.mul_dvd_of_dvd_of_dvd hq hd)
        rw [Nat.factorization_eq_zero_of_not_dvd hqd, optionalValuation]
        simp [hpq]
    · refine ⟨none, ?_⟩
      intro p
      have hd : ¬ (p : ℕ) ∣ j.val := fun hp => h ⟨p, hp⟩
      simp [optionalValuation, Nat.factorization_eq_zero_of_not_dvd hd]
  choose t ht using hex
  exact ⟨t, ht⟩

private theorem factorization_multiset_map_prod {α : Type*} (M : Multiset α)
    (f : α → ℕ) (p : ℕ) (h0 : ∀ a ∈ M, f a ≠ 0) :
    (M.map f).prod.factorization p = (M.map (fun a => (f a).factorization p)).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have hM0 : (M.map f).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro hz
      obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hz
      exact h0 x (Multiset.mem_cons_of_mem hx) hx0
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Nat.factorization_mul (h0 a (Multiset.mem_cons_self _ _)) hM0, Finsupp.add_apply,
      ih (fun b hb => h0 b (Multiset.mem_cons_of_mem hb))]

theorem counting_obstruction_with_sparse_tail {n k l r : ℕ} (hk : 3 ≤ k) (hn : k ^ l < n)
    (hr : 0 < r) (hrl : r < l) (S P Q : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hPQ : ∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    (S.card + r - 1).choose r ≤ l ^ P.card * (Q.card + r).choose r := by
  classical
  have hS (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  obtain ⟨tag, htag⟩ := sparsePrimeTailTag S Q hS hQ hPair
  let T := Sym (↑S) r
  let product (z : T) := ((Sym.map (Subtype.val : (↑S) → ℕ) z : Sym ℕ r) : Multiset ℕ)
  have hprodMem (z : T) {j : ℕ} (hj : j ∈ product z) : j ∈ S := by
    change j ∈ (z : Multiset S).map Subtype.val at hj
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hj
    exact v.property
  let code (z : T) : (P → Fin l) × Sym (Option (↑Q)) r :=
    (fun p => ⟨(product z).prod.factorization p % l, Nat.mod_lt _ (by omega)⟩, Sym.map tag z)
  have htail (z : T) (p : Q) : (product z).prod.factorization p =
      (((Sym.map tag z : Sym (Option (↑Q)) r) : Multiset (Option (↑Q))).map
        (fun t => optionalValuation t p)).sum := by
    change (((z : Multiset S).map Subtype.val).prod).factorization p =
      (((z : Multiset S).map tag).map (fun t => optionalValuation t p)).sum
    have hp := factorization_multiset_map_prod (z : Multiset S) (fun j : S => j.val) p
      (fun j _ => hS j j.property)
    rw [hp, Multiset.map_map]
    simp only [Function.comp_def, htag]
  have hinj : Function.Injective code := by
    intro x y hxy
    have hEQ : product x = product y := by
      apply interval_products_residue_injective hk hn hr hrl _ _ Sym.card_coe Sym.card_coe
        (fun _ hj => hSI (hprodMem x hj)) (fun _ hj => hSI (hprodMem y hj))
      intro p
      by_cases hp : p ∈ P
      · exact congrArg Fin.val (congrFun (congrArg Prod.fst hxy) (⟨p, hp⟩ : P))
      by_cases hq : p ∈ Q
      · rw [htail x (⟨p, hq⟩ : Q), htail y (⟨p, hq⟩ : Q)]
        have htag' : Sym.map tag x = Sym.map tag y := congrArg Prod.snd hxy
        rw [htag']
      · have h0 (z : T) : (product z).prod.factorization p % l = 0 :=
          multiset_factorization_mod_eq_zero l p (product z)
            (fun j hj => hS j (hprodMem z hj))
            (fun j hj => hPQ j (hprodMem z hj) p (by simp [hp, hq]))
        rw [h0 x, h0 y]
    apply Sym.map_injective Subtype.val_injective r
    exact Subtype.ext hEQ
  have h := Fintype.card_le_of_injective code hinj
  have he : Q.card + 1 + r - 1 = Q.card + r := by omega
  simpa [T, Sym.card_sym_eq_choose, Fintype.card_fun, he] using h


private theorem factorial_factorization_of_lt_sq {n p : ℕ} (hp : p.Prime)
    (hn : n < p^2) : n.factorial.factorization p = n/p := by
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hn
  rw [Nat.factorization_factorial hp hlog, show Ico 1 2 = {1} by decide, sum_singleton, pow_one]

private theorem prime_dvd_sixth_block_multinomial {m p : ℕ} (hm : 4 ≤ m)
    (hp : p.Prime) (hmp : m < p) (hpm : p ≤ 6*m) :
    p ∣ (6*m).choose (3*m) * (3*m).choose m := by
  let A := (6*m).choose (3*m)
  let B := (3*m).choose m
  have hAn : A ≠ 0 := Nat.choose_ne_zero (by omega)
  have hBn : B ≠ 0 := Nat.choose_ne_zero (by omega)
  have hA : A * (3*m).factorial * (3*m).factorial = (6*m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 6*m) (k := 3*m) (by omega)
    simpa only [A, show 6*m-3*m = 3*m by omega] using h
  have hB : B * m.factorial * (2*m).factorial = (3*m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 3*m) (k := m) (by omega)
    simpa only [B, show 3*m-m = 2*m by omega] using h
  have he : A*B * (3*m).factorial * (2*m).factorial * m.factorial = (6*m).factorial := calc
    A*B * (3*m).factorial * (2*m).factorial * m.factorial =
      A * (3*m).factorial * (B * m.factorial * (2*m).factorial) := by ac_rfl
    _ = (6*m).factorial := by rw [hB, hA]
  have hp2 : 6*m < p^2 := by
    have h := Nat.pow_le_pow_left (by omega : m+1 ≤ p) 2
    nlinarith only [h, show 16 ≤ m^2 by
      exact Nat.pow_le_pow_left hm 2, show 0 ≤ (m-4)^2 by positivity, hm]
  have hfac := congrArg (fun a : ℕ => a.factorization p) he
  rw [Nat.factorization_mul (by positivity : (A*B*(3*m).factorial*(2*m).factorial) ≠ 0)
      (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity : (A*B*(3*m).factorial) ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero hAn hBn) (Nat.factorial_ne_zero _)] at hfac
  simp only [Finsupp.add_apply] at hfac
  rw [factorial_factorization_of_lt_sq hp hp2,
    factorial_factorization_of_lt_sq hp (show 3*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 2*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show m < p^2 by omega),
    Nat.div_eq_of_lt hmp] at hfac
  have hD (j a : ℕ) (hja : 6*m/j = a) : (6*m)/p/j = a/p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j, ← Nat.div_div_eq_div_mul, hja]
  rw [← hD 2 (3*m) (by omega), ← hD 3 (2*m) (by omega)] at hfac
  have hLo : 1 ≤ (6*m)/p := (Nat.one_le_div_iff hp.pos).mpr hpm
  have hHi : (6*m)/p < 6 := (Nat.div_lt_iff_lt_mul hp.pos).mpr
    (Nat.mul_lt_mul_of_pos_left hmp (by decide))
  have hf : 0 < (A*B).factorization p := by omega
  exact Nat.dvd_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hf.ne' : p ∈ (A*B).primeFactors)

private theorem primorial_sixth_le (m : ℕ) (hm : 4 ≤ m) :
    primorial (6*m) ≤ primorial m * 432^m := by
  have hC : (3*m).choose m * 4^m ≤ 27^m := by
    have hs := Finset.single_le_sum (s := range (3*m+1))
      (f := fun j => (1:ℕ)^j * 2^(3*m-j) * (3*m).choose j)
      (fun _ _ => Nat.zero_le _) (a := m) (mem_range.mpr (by omega))
    have ha : (3:ℕ)^(3*m) =
        ∑ j ∈ range (3*m+1), (1:ℕ)^j*2^(3*m-j)*(3*m).choose j := by
      simpa only [show (1:ℕ)+2=3 by decide, Nat.cast_id] using (add_pow (1:ℕ) 2 (3*m))
    rw [← ha] at hs
    simp only [one_pow, one_mul, show 3*m-m = 2*m by omega, pow_mul 2 2,
      show (2:ℕ)^2=4 by decide, pow_mul 3 3, show (3:ℕ)^3=27 by decide] at hs
    simpa only [Nat.mul_comm] using hs
  have hcbin : (6*m).choose (3*m) ≤ 64^m := by
    have h := Nat.centralBinom_le_four_pow (3*m)
    simpa only [Nat.centralBinom, show 2*(3*m)=6*m by ring, pow_mul 4 3,
      show (4:ℕ)^3=64 by decide] using h
  have hbound : (6*m).choose (3*m) * (3*m).choose m ≤ 432^m := calc
    (6*m).choose (3*m) * (3*m).choose m ≤ 64^m * (3*m).choose m :=
      Nat.mul_le_mul_right _ hcbin
    _ = 16^m * ((3*m).choose m * 4^m) := by
      rw [show (64:ℕ)=16*4 by decide, mul_pow]
      ac_rfl
    _ ≤ 16^m * 27^m := Nat.mul_le_mul_left _ hC
    _ = 432^m := by rw [← mul_pow]; rfl
  have hdiv : primorial (6*m) ∣ primorial m * ((6*m).choose (3*m) * (3*m).choose m) := by
    rw [show 6*m = m+(5*m) by omega, primorial_add]
    apply Nat.mul_dvd_mul_left
    refine prod_primes_dvd _ (fun _ h => (mem_filter.mp h).2.prime) ?_
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    obtain ⟨h₁,h₂⟩ := mem_Ico.mp hpI
    simpa only [show m+5*m=6*m by omega] using
      prime_dvd_sixth_block_multinomial hm hpP (by omega) (by omega)
  have hpos := mul_pos (primorial_pos m)
    (mul_pos (Nat.choose_pos (show 3*m ≤ 6*m by omega)) (Nat.choose_pos (show m ≤ 3*m by omega)))
  exact (Nat.le_of_dvd hpos hdiv).trans (Nat.mul_le_mul_left _ hbound)

private def PrimorialCertificate (a : ℕ) : List ℕ → Prop
  | [] => 300 ≤ a
  | b::l => 2^b*primorial b ≤ 7^a ∧ PrimorialCertificate (b+1) l

private theorem primorial_cert_lookup (l : List ℕ) {a n : ℕ}
    (han : a ≤ n) (hn : n < 300) (hl : PrimorialCertificate a l) :
    2^n*primorial n ≤ 7^n := by
  induction l generalizing a with
  | nil =>
    change 300 ≤ a at hl
    omega
  | cons b l ih =>
    rcases hl with ⟨hb,hl⟩
    by_cases hnb : n ≤ b
    · exact le_trans (Nat.mul_le_mul (pow_right_mono₀ (by decide) hnb) (primorial_mono hnb))
        (hb.trans (pow_right_mono₀ (by decide) han))
    · exact ih (by omega) hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem primorial_certificate :
    PrimorialCertificate 0 [0, 1, 3, 6, 10, 16, 22, 30, 40, 52, 66, 82, 102, 127, 156, 191, 232, 278, 299] := by
  simp only [PrimorialCertificate]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem primorial_rounding_bound (m : ℕ) (hm : 50 ≤ m) :
    96768^m*7^5 ≤ 7^(6*m) := by
  have h0 : 96768^50*7^5 ≤ (7:ℕ)^(6*50) := by decide +kernel
  let r := m-50
  have he : 50+r=m := by dsimp [r]; omega
  calc
    96768^m*7^5 = (96768^50*7^5)*96768^r := by
      conv_lhs => lhs; rw [← he, pow_add]
      simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ 7^(6*50)*(7^6)^r := Nat.mul_le_mul h0 (Nat.pow_le_pow_left (by decide) _)
    _ = 7^(6*m) := by rw [← pow_mul, ← pow_add, ← he, mul_add]

/-- The product of the primes up to n is at most (7/2)^n. -/
theorem primorial_le_seven_halves_pow (n : ℕ) : 2^n*primorial n ≤ 7^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 300
    · exact primorial_cert_lookup _ (Nat.zero_le _) hn primorial_certificate
    let m := (n+5)/6
    have hm : 50 ≤ m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hn6 : n ≤ 6*m := by dsimp [m]; omega
    have hshift : 6*m-n ≤ 5 := by dsimp [m]; omega
    have hbound := primorial_sixth_le m (by omega)
    have hC : 96768^m ≤ 7^n := by
      refine (Nat.le_of_mul_le_mul_right ?_ (show 0 < (7:ℕ)^(6*m-n) by positivity))
      calc
        96768^m*7^(6*m-n) ≤ 96768^m*7^5 :=
          Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) hshift)
        _ ≤ 7^(6*m) := primorial_rounding_bound m hm
        _ = 7^n*7^(6*m-n) := by rw [← pow_add, Nat.add_sub_of_le hn6]
    calc
      2^n*primorial n ≤ 2^(6*m)*primorial (6*m) :=
        Nat.mul_le_mul (pow_right_mono₀ (by decide) hn6) (primorial_mono hn6)
      _ ≤ 2^(6*m)*(primorial m*432^m) := Nat.mul_le_mul_left _ hbound
      _ = (2^5*432)^m*(2^m*primorial m) := by
        rw [show 6*m=5*m+m by omega, pow_add, pow_mul, mul_pow]
        ac_rfl
      _ ≤ (2^5*432)^m*7^m := Nat.mul_le_mul_left _ (ih m hmn)
      _ = 96768^m := by rw [← mul_pow]; rfl
      _ ≤ 7^n := hC

private theorem intervalMultipleCount_eq_sub (n k d : ℕ) :
    intervalMultipleCount n k d = (n+k)/d - n/d := by
  have h : (Icc (n+1) (n+k)).filter (d ∣ ·) =
      ((Ioc 0 (n+k)).filter (d ∣ ·)) \ ((Ioc 0 n).filter (d ∣ ·)) := by
    ext j
    simp only [mem_filter, mem_sdiff, mem_Icc, mem_Ioc]
    omega
  unfold intervalMultipleCount
  rw [h, card_sdiff_of_subset, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  intro j hj
  simp only [mem_filter, mem_Ioc] at hj ⊢
  omega

private theorem intervalMultipleCount_ceiling (n k d : ℕ) (hk : 0 < k) (hd : 0 < d) :
    intervalMultipleCount n k d ≤ (k-1)/d+1 := by
  rw [intervalMultipleCount_eq_sub]
  have h : n+k = (n%d+k)+d*(n/d) := by
    have hmod := Nat.div_add_mod n d
    omega
  nth_rw 1 [h]
  rw [Nat.add_mul_div_left _ _ hd, Nat.add_sub_cancel]
  have hlt := Nat.mod_lt n hd
  calc
    (n%d+k)/d ≤ ((k-1)+d)/d := Nat.div_le_div_right (by omega)
    _ = (k-1)/d+1 := by
      conv_lhs => lhs; rw [← Nat.mul_one d]
      rw [Nat.add_mul_div_left _ _ hd]

private theorem square_kernel_squarefree {j : ℕ} (hj : j ≠ 0) :
    Squarefree (powerFreePart 2 j) :=
  Nat.squarefree_of_factorization_le_one (powerFreePart_nonzero hj) fun p => by
    rw [powerFreePart_factorization]
    omega

private theorem square_kernel_primes_of_failure {n k j : ℕ}
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ i ∈ Icc (n+1) (n+k), i).factorization p)
    (hj : j ∈ Icc (n+1) (n+k)) :
    ∀ p ∈ (powerFreePart 2 j).primeFactors, p < k := by
  intro p hp
  by_contra! hpk
  have hz := powerFreePart_of_failed_large_prime n k 2 hf hj hpk
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
  exact hp hz

private theorem count_small_square_kernels {n k m : ℕ} (hk : 3 ≤ k) (hn : k^2 < n)
    (T : Finset ℕ) (hTI : T ⊆ Icc (n+1) (n+k))
    (hs : ∀ j ∈ T, ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ m) :
    T.card ≤ 2^(Nat.primesLE m).card := by
  let A := (Nat.primesLE m).powerset
  let f (j : T) : A :=
    ⟨(powerFreePart 2 j.val).primeFactors, Finset.mem_powerset.mpr (fun p hp =>
      Nat.mem_primesLE.mpr ⟨hs j.val j.property p hp, Nat.prime_of_mem_primeFactors hp⟩)⟩
  have hInj := powerFreePart_injOn_interval hk (by decide : 2 ≤ 2) hn T hTI
  have hF : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply hInj a.property b.property
    have h0 (x : T) : x.val ≠ 0 := by have := (mem_Icc.mp (hTI x.property)).1; omega
    have hpa := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree (h0 a))
    have hpb := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree (h0 b))
    have hEq : (powerFreePart 2 a.val).primeFactors = (powerFreePart 2 b.val).primeFactors :=
      congrArg Subtype.val he
    rw [hEq, hpb] at hpa
    exact hpa.symm
  have h := Fintype.card_le_of_injective f hF
  simpa only [A, Fintype.card_coe, Finset.card_powerset] using h

private def supportPrimesBetween (k m : ℕ) : Finset ℕ :=
  (range k).filter (fun p => m < p ∧ p.Prime)

private def squareKernelCap (k m : ℕ) : ℕ :=
  2^(Nat.primesLE m).card + ∑ p ∈ supportPrimesBetween k m, ((k-1)/p+1)

private theorem squareKernelCap_use_table {k m : ℕ} (hk : k ≤ 1001) (hm : m < 1001) :
    squareKernelCap k m =
      2^(sievePrimeTable.filter (· ≤ m)).card +
        ∑ p ∈ sievePrimeTable.filter (fun p => m < p ∧ p < k), ((k-1)/p+1) := by
  have hM : Nat.primesLE m = sievePrimeTable.filter (· ≤ m) := by
    rw [← sievePrimeTable_eq]
    ext p
    simp only [Nat.mem_primesLE, mem_filter, mem_range]
    constructor
    · rintro ⟨hpm, hp⟩
      exact ⟨⟨hpm.trans_lt hm, hp⟩, hpm⟩
    · rintro ⟨⟨_, hp⟩, hpm⟩
      exact ⟨hpm, hp⟩
  have hK : supportPrimesBetween k m = sievePrimeTable.filter (fun p => m < p ∧ p < k) := by
    rw [supportPrimesBetween, ← sievePrimeTable_eq]
    ext p
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hpk, hmp, hp⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, hmp, hpk⟩
    · rintro ⟨⟨_, hp⟩, hmp, hpk⟩
      exact ⟨hpk, hmp, hp⟩
  rw [squareKernelCap, hM, hK]

private theorem squareKernelCap_monotone (m : ℕ) : Monotone (fun k => squareKernelCap k m) := by
  intro a b hab
  unfold squareKernelCap
  apply Nat.add_le_add_left
  have hsub : supportPrimesBetween a m ⊆ supportPrimesBetween b m :=
    Finset.filter_subset_filter _ (range_mono hab)
  apply (sum_le_sum fun p _ => Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hab 1)) _).trans
  exact sum_le_sum_of_subset hsub

private theorem square_kernel_count_cap_of_failure {n k m : ℕ} (hk : 3 ≤ k) (hn : k^2 < n)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) :
    k ≤ squareKernelCap k m := by
  classical
  let I := Icc (n+1) (n+k)
  let P := supportPrimesBetween k m
  let D := P.biUnion (fun p => I.filter (p ∣ ·))
  let T := I \ D
  have hDI : D ⊆ I := by
    intro j hj
    obtain ⟨p, hp, hjp⟩ := Finset.mem_biUnion.mp hj
    exact (mem_filter.mp hjp).1
  have hTI : T ⊆ I := sdiff_subset
  have hD : D.card ≤ ∑ p ∈ P, ((k-1)/p+1) := by
    apply Finset.card_biUnion_le.trans
    refine sum_le_sum fun p hp => intervalMultipleCount_ceiling n k p (by omega) ?_
    exact ((mem_filter.mp hp).2.2).pos
  have hT : T.card ≤ 2^(Nat.primesLE m).card := by
    apply count_small_square_kernels hk hn T hTI
    intro j hj p hp
    by_contra! hmp
    have hij := hTI hj
    have hpk := square_kernel_primes_of_failure hf hij p hp
    have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr hpk, hmp, Nat.prime_of_mem_primeFactors hp⟩
    have hjD : j ∈ D := Finset.mem_biUnion.mpr
      ⟨p, hpP, mem_filter.mpr ⟨hij, (Nat.dvd_of_mem_primeFactors hp).trans (powerFreePart_dvd 2 j)⟩⟩
    exact (mem_sdiff.mp hj).2 hjD
  have hcard : I.card = k := by simp [I, Nat.card_Icc]
  have hall : T.card = k-D.card := by
    rw [show T = I\D from rfl, card_sdiff_of_subset hDI, hcard]
  have hd : D.card ≤ k := (card_le_card hDI).trans_eq hcard
  unfold squareKernelCap
  change k ≤ 2^(Nat.primesLE m).card + ∑ p ∈ P, ((k-1)/p+1)
  omega

private def SquareWidthCertificate (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 824 ≤ a
  | (b,m)::l => squareKernelCap b m < a ∧ SquareWidthCertificate (b+1) l

private theorem small_square_width_cert_lookup (l : List (ℕ × ℕ)) {a k : ℕ}
    (hk : k < 824) (hak : a ≤ k) (hl : SquareWidthCertificate a l) :
    ∃ m, squareKernelCap k m < k := by
  induction l generalizing a with
  | nil =>
    change 824 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,m⟩ := z
    rcases hl with ⟨hb, hs⟩
    by_cases hkb : k ≤ b
    · exact ⟨m, (squareKernelCap_monotone m hkb).trans_lt (hb.trans_le hak)⟩
    · exact ih (by omega) hs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem small_square_width_cert :
    SquareWidthCertificate 9
    [(10, 3), (11, 3), (13, 3), (14, 3), (15, 3), (17, 3), (19, 3), (20, 3),
     (22, 5), (23, 5), (26, 5), (29, 5), (33, 5), (37, 5), (41, 5), (44, 5),
     (47, 5), (52, 5), (56, 5), (61, 7), (67, 7), (73, 7), (79, 7), (87, 7),
     (95, 7), (103, 7), (111, 7), (119, 7), (130, 7), (139, 7), (149, 7), (158, 7),
     (167, 7), (176, 7), (186, 11), (197, 11), (208, 11), (221, 11), (233, 11), (246, 11),
     (259, 11), (271, 11), (283, 11), (295, 11), (307, 11), (318, 11), (331, 11), (344, 11),
     (356, 11), (368, 11), (379, 11), (390, 11), (401, 11), (411, 11), (416, 11), (426, 13),
     (436, 13), (445, 13), (456, 13), (465, 13), (474, 13), (483, 13), (493, 13), (503, 13),
     (514, 13), (524, 13), (535, 13), (547, 13), (558, 13), (569, 13), (580, 13), (591, 13),
     (601, 13), (611, 13), (619, 13), (629, 13), (639, 13), (647, 13), (655, 13), (662, 13),
     (668, 13), (674, 13), (681, 13), (688, 13), (695, 13), (701, 13), (708, 13), (713, 13),
     (719, 13), (725, 13), (732, 13), (739, 13), (744, 13), (749, 13), (754, 13), (759, 13),
     (763, 13), (767, 13), (772, 13), (776, 13), (779, 13), (782, 13), (786, 13), (789, 13),
     (793, 13), (797, 13), (799, 13), (802, 13), (805, 13), (808, 13), (811, 13), (813, 13),
     (815, 13), (817, 13), (818, 13), (820, 13), (821, 13), (822, 13), (823, 13)] := by
  simp only [SquareWidthCertificate]
  repeat' apply And.intro
  all_goals first | (rw [squareKernelCap_use_table (by decide) (by decide)]; decide +kernel) | decide

theorem square_prime_obstruction_small_generic {n k : ℕ} (hk : 9 ≤ k) (hk' : k < 824)
    (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  obtain ⟨m, hm⟩ := small_square_width_cert_lookup _ hk' hk small_square_width_cert
  exact (not_lt_of_ge (square_kernel_count_cap_of_failure (by omega) hn hf)) hm

private def cleanSquareOffsets (n k : ℕ) : Finset ℕ :=
  (Icc 1 k).filter (fun i => ¬ 5 ∣ n+i ∧ (k = 6 ∨ ¬ 7 ∣ n+i))

private theorem cleanSquareOffsets_mod (n k : ℕ) :
    cleanSquareOffsets (n%35) k = cleanSquareOffsets n k := by
  have h (p i : ℕ) (hp : p ∣ 35) : p ∣ n%35+i ↔ p ∣ n+i := by
    have hmod : n%35 ≡ n [MOD 35] := Nat.mod_modEq n 35
    exact ((hmod.of_dvd hp).add_right i).dvd_iff (dvd_refl p)
  ext i
  simp only [cleanSquareOffsets, mem_filter, h 5 i (by decide), h 7 i (by decide)]

set_option maxRecDepth 10000 in
private theorem cleanSquareOffsets_cert : ∀ r : Fin 35,
    (5 ≤ (cleanSquareOffsets r 6).card ∨ Icc 2 5 ⊆ cleanSquareOffsets r 6) ∧
    (5 ≤ (cleanSquareOffsets r 8).card ∨ Icc 3 6 ⊆ cleanSquareOffsets r 8) := by decide

private theorem cleanSquareOffset_support {n k i : ℕ} (hk : k = 6 ∨ k = 8)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p)
    (hi : i ∈ cleanSquareOffsets n k) :
    ∀ p ∈ (powerFreePart 2 (n+i)).primeFactors, p ≤ 3 := by
  intro p hp
  have hi' := mem_filter.mp hi
  have hiI := mem_Icc.mp hi'.1
  have hnI : n+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hpk := square_kernel_primes_of_failure hf hnI p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := (Nat.dvd_of_mem_primeFactors hp).trans (powerFreePart_dvd 2 (n+i))
  by_contra! hbig
  have hRange : p = 5 ∨ p = 7 := by
    have hp8 : p < 8 := by omega
    interval_cases p <;> norm_num at hprime <;> decide
  rcases hRange with rfl | rfl
  · exact hi'.2.1 hd
  · rcases hi'.2.2 with h6 | h7
    · omega
    · exact h7 hd

private theorem four_consecutive_kernels_cannot_all_be_small {n k d : ℕ}
    (hk : 3 ≤ k) (hn : k^2 < n) (hd : d+4 ≤ k)
    (hSup : ∀ j ∈ Icc (n+d+1) (n+d+4),
      ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ 3) : False := by
  classical
  let J := Icc (n+d+1) (n+d+4)
  let A : Finset ℕ := {1,2,3,6}
  have hJ : J ⊆ Icc (n+1) (n+k) := by
    intro j hj
    have hm := mem_Icc.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hInj := powerFreePart_injOn_interval hk (by decide : 2 ≤ 2) hn J hJ
  have hin : J.image (powerFreePart 2) ⊆ A := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    have h0 : j ≠ 0 := by have := (mem_Icc.mp (hJ hj)).1; omega
    have hK := Nat.prod_primeFactors_of_squarefree (square_kernel_squarefree h0)
    have hsub : (powerFreePart 2 j).primeFactors ⊆ ({2,3} : Finset ℕ) := by
      intro p hp
      have h := hSup j hj p hp
      have hh := (Nat.prime_of_mem_primeFactors hp).two_le
      simp only [mem_insert, mem_singleton]
      omega
    let S := ({2,3} : Finset ℕ).powerset.image (fun s => ∏ p ∈ s, p)
    have hm : powerFreePart 2 j ∈ S :=
      mem_image.mpr ⟨_, Finset.mem_powerset.mpr hsub, hK⟩
    exact (show S = A by decide) ▸ hm
  have hcard : J.card = 4 := by simp [J, Nat.card_Icc] 
  have hEq : J.image (powerFreePart 2) = A := by
    apply Finset.eq_of_subset_of_card_le hin
    rw [Finset.card_image_of_injOn hInj, hcard]
    decide
  have hprod : ∏ j ∈ J, powerFreePart 2 j = (6 : ℕ)^2 := by
    calc
      (∏ j ∈ J, powerFreePart 2 j) = ∏ j ∈ J.image (powerFreePart 2), j := by rw [prod_image hInj]
      _ = (6 : ℕ)^2 := by rw [hEq]; decide
  apply not_square_four_factors (n+d) (6*∏ j ∈ J, powerRoot 2 j)
  change ∏ j ∈ J, j = _
  calc
    ∏ j ∈ J, j = ∏ j ∈ J, (powerFreePart 2 j * (powerRoot 2 j)^2) := by
      apply prod_congr rfl
      intro j hj
      exact (powerFreePart_mul_powerRoot 2 j (by have := (mem_Icc.mp (hJ hj)).1; omega)).symm
    _ = _ := by rw [Finset.prod_mul_distrib, hprod, Finset.prod_pow, mul_pow]

private theorem square_failure_impossible_6_8 {n k : ℕ} (hk : k = 6 ∨ k = 8)
    (hn : k^2 < n) (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) : False := by
  let S := (cleanSquareOffsets n k).image (fun i => n+i)
  have hclean : ∀ j ∈ S, ∀ p ∈ (powerFreePart 2 j).primeFactors, p ≤ 3 := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact cleanSquareOffset_support hk hf hi
  have hSI : S ⊆ Icc (n+1) (n+k) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have hm := mem_Icc.mp (mem_filter.mp hi).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcount := count_small_square_kernels (by omega) hn S hSI hclean
  rw [show (Nat.primesLE 3).card = 2 by decide] at hcount
  norm_num at hcount
  rw [Finset.card_image_of_injective _ (fun i j hi => Nat.add_left_cancel hi)] at hcount
  have hr := cleanSquareOffsets_cert ⟨n%35, Nat.mod_lt _ (by decide)⟩
  change (5 ≤ (cleanSquareOffsets (n%35) 6).card ∨ Icc 2 5 ⊆ cleanSquareOffsets (n%35) 6) ∧
    (5 ≤ (cleanSquareOffsets (n%35) 8).card ∨ Icc 3 6 ⊆ cleanSquareOffsets (n%35) 8) at hr
  rw [cleanSquareOffsets_mod, cleanSquareOffsets_mod] at hr
  have mid (d : ℕ) (hd : d+4 ≤ k) (hIn : Icc (d+1) (d+4) ⊆ cleanSquareOffsets n k) : False := by
    apply four_consecutive_kernels_cannot_all_be_small (by omega) hn hd
    intro j hj
    have hj' := mem_Icc.mp hj
    have hoff : j-n ∈ Icc (d+1) (d+4) := mem_Icc.mpr ⟨by omega, by omega⟩
    have he : n+(j-n)=j := by omega
    have HC := cleanSquareOffset_support hk hf (hIn hoff)
    rwa [he] at HC
  rcases hk with rfl | rfl
  · rcases hr.1 with h | h
    · omega
    · exact mid 1 (by decide) h
  · rcases hr.2 with h | h
    · omega
    · exact mid 2 (by decide) h

theorem square_prime_obstruction_bounded {n k : ℕ}
    (hk : 3 ≤ k) (hu : k < 824) (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n+k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_cases hsmall : k ≤ 5
  · interval_cases k
    · exact three_factors 2 n (by decide)
    · exact four_factors 2 n (by decide) hend
    · exact five_factors 2 n (by decide) hend
  by_cases hn : n ≤ k
  · exact short_interval k 2 n hk (by decide) hend hn
  by_contra! h
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime (by omega : k < n+1)
    (by omega : 0 < k)
  have hi' := mem_range.mp hi
  have hm : (n+1)+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hg := modulus_growth_of_large_prime (by omega) (by decide : 2 ≤ 2) hpk hp hm hd
    (h p hpk.le hp)
  by_cases hbig : 9 ≤ k
  · obtain ⟨q,hq,hq',hqbad⟩ := square_prime_obstruction_small_generic hbig hu hg
    exact hqbad (h q hq hq')
  by_cases hmid : k = 7
  · subst k
    have hc := square_kernel_count_cap_of_failure (m := 3) (by decide) hg h
    have hh : squareKernelCap 7 3 < 7 := by decide
    omega
  exact square_failure_impossible_6_8 (by omega) hg h

private def squarePrimeProduct (e : ℕ → ℕ) : ℕ :=
  ∏ p ∈ squareSavingPrimes, p^(e p)

private theorem squarePrimeProduct_pos (e : ℕ → ℕ) : 0 < squarePrimeProduct e :=
  Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun _p hp => pow_ne_zero _ (squareSavingPrime hp).ne_zero)

private theorem squarePrimeProduct_factorization (e : ℕ → ℕ) (p : ℕ) :
    (squarePrimeProduct e).factorization p = if p ∈ squareSavingPrimes then e p else 0 := by
  classical
  unfold squarePrimeProduct
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (squareSavingPrime hq).ne_zero)]
  by_cases hp : p ∈ squareSavingPrimes
  · rw [if_pos hp]
    have h := sum_eq_single_of_mem p hp (f := fun q => (q^(e q)).factorization p)
      (fun q hq hqp => by rw [(squareSavingPrime hq).factorization_pow, Finsupp.single_eq_of_ne hqp.symm])
    rw [h, Nat.factorization_pow_self (squareSavingPrime hp)]
  · rw [if_neg hp]
    apply sum_eq_zero
    intro q hq
    have hn : p ≠ q := fun h => hp (h ▸ hq)
    rw [(squareSavingPrime hq).factorization_pow, Finsupp.single_eq_of_ne hn]

private theorem squarePrimeProduct_pow (e : ℕ → ℕ) (q : ℕ) :
    squarePrimeProduct (fun p => e p * q) = squarePrimeProduct e ^ q := by
  simp only [squarePrimeProduct, pow_mul, Finset.prod_pow]

private theorem square_product_adjusted_dvd {n k : ℕ} (hk : 3 ≤ k)
    (hf : ∀ p, k ≤ p → p.Prime →
      2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p)
    (e w : ℕ → ℕ)
    (h : ∀ p∈squareSavingPrimes, e p ≠ 0 →
      (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p + e p ≤
        (k-1).factorial.factorization p + w p) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j) * squarePrimeProduct e ∣
      ((k-1).factorial * primorial (k-1)) * squarePrimeProduct w := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let F := (k-1).factorial * primorial (k-1)
  have hA : A ≠ 0 := prod_ne_zero_iff.mpr (fun j hj => powerFreePart_nonzero (by
    have := (mem_Icc.mp hj).1
    omega))
  have hF : F ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (primorial_ne_zero _)
  have hdiv := full_product_powerFreePart_dvd_factorial_mul_primorial_pow n k 2 (by omega) (by decide) hf
  have hbase : A ∣ F := by
    simpa only [A, F, primorial, show k-1+1 = k by omega, show 2-1=1 by decide, pow_one] using hdiv
  apply (Nat.factorization_le_iff_dvd (mul_ne_zero hA (squarePrimeProduct_pos _).ne')
    (mul_ne_zero hF (squarePrimeProduct_pos _).ne')).1
  intro p
  rw [Nat.factorization_mul hA (squarePrimeProduct_pos _).ne', Finsupp.add_apply,
    Nat.factorization_mul hF (squarePrimeProduct_pos _).ne', Finsupp.add_apply,
    squarePrimeProduct_factorization, squarePrimeProduct_factorization]
  have hF0 := (Nat.factorization_le_iff_dvd hA hF).2 hbase p
  by_cases hp : p ∈ squareSavingPrimes
  · rw [if_pos hp, if_pos hp]
    by_cases he : e p = 0
    · simpa only [he, add_zero] using hF0.trans (Nat.le_add_right _ _)
    · have h' := h p hp he
      have hF1 : F.factorization p =
          (k-1).factorial.factorization p + (primorial (k-1)).factorization p := by
        rw [show F = _ from rfl, Nat.factorization_mul (Nat.factorial_ne_zero _) (primorial_ne_zero _),
          Finsupp.add_apply]
      change A.factorization p + e p ≤ _ at h'
      omega
  · simpa only [if_neg hp, add_zero] using hF0

private theorem scaled_square_upper {n k E W : ℕ} (hk : 6 ≤ k) (hn : k^2 < n)
    (h : (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j)*E ∣
      ((k-1).factorial*primorial (k-1))*W) (hw : 0 < W) :
    3^(k-6)*E ≤ 2^(k-6)*k^5*primorial (k-1)*W := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let m := k-6
  have hm : m+5=k-1 := by dsimp [m]; omega
  have hlo : 3^m*m.factorial ≤ 2^m*A :=
    squareFreePart_prod_lower_bound (by omega) hn
  have hJ : A*E ≤ ((k-1).factorial*primorial (k-1))*W :=
    Nat.le_of_dvd (mul_pos (mul_pos (Nat.factorial_pos _) (primorial_pos _)) hw) h
  have hfac : (k-1).factorial ≤ m.factorial*k^5 := by
    have ha := Nat.ascFactorial_le_pow_add m 5
    have hf := Nat.factorial_mul_ascFactorial m 5
    rw [hm] at ha hf
    exact hf.symm.le.trans (Nat.mul_le_mul_left _ (ha.trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)))
  apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos m)
  calc
    m.factorial*(3^m*E) = (3^m*m.factorial)*E := by ac_rfl
    _ ≤ (2^m*A)*E := Nat.mul_le_mul_right _ hlo
    _ = 2^m*(A*E) := by rw [mul_assoc]
    _ ≤ 2^m*(((k-1).factorial*primorial (k-1))*W) := Nat.mul_le_mul_left _ hJ
    _ ≤ 2^m*((m.factorial*k^5*primorial (k-1))*W) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfac))
    _ = _ := by ac_rfl

private def squareRate (p : ℕ) : ℕ := squareSaving p / 10

private theorem square_factorization_additive_saving {n k p : ℕ} (hk : 1 ≤ k)
    (hp : p ∈ squareSavingPrimes) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p +
        squareRate p * (k/100) ≤ (k-1).factorial.factorization p + 15 := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let F := (k-1).factorial
  have hprime := squareSavingPrime hp
  have hK : 0 ≤ (k : ℝ) := by positivity
  have hloNat := sum_le_factorial_factorization hprime (k-1) 9
  have hL : (∑ i ∈ Ico 1 9, (((k : ℝ)-1)/(p : ℝ)^i-1)) ≤ (F.factorization p : ℝ) := by
    calc
      _ ≤ ∑ i ∈ Ico 1 9, ((((k-1 : ℕ)/p^i : ℕ)) : ℝ) := by
        apply sum_le_sum
        intro i _
        have h := (real_nat_div_bounds (k-1) (p^i) (pow_pos hprime.pos i)).1
        simpa only [Nat.cast_sub hk, Nat.cast_one, Nat.cast_pow] using h
      _ ≤ _ := by exact_mod_cast hloNat
  have h3 : (A.factorization p : ℝ) + ((k/p^2 : ℕ) : ℝ) ≤
      ((k/p : ℕ) : ℝ) + ((k/p^3 : ℕ) : ℝ) + 2 := by
    exact_mod_cast squareFreePart_factorization_plus_two_le (n := n) (k := k) hprime
  have hUpper : (A.factorization p : ℝ) ≤ (k : ℝ)/p - (k : ℝ)/(p : ℝ)^2 +
      (k : ℝ)/(p : ℝ)^3 + 3 := by
    have h1 := (real_nat_div_bounds k p hprime.pos).2
    have h2 := (real_nat_div_bounds k (p^2) (pow_pos hprime.pos 2)).1
    have h3' := (real_nat_div_bounds k (p^3) (pow_pos hprime.pos 3)).2
    push_cast at h2 h3'
    linarith only [h1, h2, h3, h3']
  have h2 : (A.factorization 2 : ℝ) + ((k/4 : ℕ) : ℝ) + ((k/16 : ℕ) : ℝ) ≤
      ((k/2 : ℕ) : ℝ) + ((k/8 : ℕ) : ℝ) + ((k/32 : ℕ) : ℝ) + 3 := by
    exact_mod_cast squareFreePart_two_factorization_plus_two_four_le n k
  have hTwo : (A.factorization 2 : ℝ) ≤ (11/32 : ℝ) * (k : ℝ) + 5 := by
    have h₂ := (real_nat_div_bounds k 2 (by decide)).2
    have h₄ := (real_nat_div_bounds k 4 (by decide)).1
    have h₈ := (real_nat_div_bounds k 8 (by decide)).2
    have h₁₆ := (real_nat_div_bounds k 16 (by decide)).1
    have h₃₂ := (real_nat_div_bounds k 32 (by decide)).2
    norm_num at h₂ h₄ h₈ h₁₆ h₃₂
    linarith only [h2, h₂, h₄, h₈, h₁₆, h₃₂]
  have hQ : ((k/100 : ℕ) : ℝ) ≤ (k : ℝ)/100 := (real_nat_div_bounds k 100 (by decide)).2
  rw [show Ico 1 9 = ({1,2,3,4,5,6,7,8} : Finset ℕ) by decide] at hL
  suffices h : (A.factorization p : ℝ) + (squareRate p : ℝ) * ((k/100 : ℕ) : ℝ) ≤
      (F.factorization p : ℝ) + 15 by exact_mod_cast h
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [sum_insert, squareRate, squareSaving] at hL ⊢
    linarith only [hL, hTwo, hQ, hK]
  all_goals
    norm_num [sum_insert, squareRate, squareSaving] at hL hUpper ⊢
    linarith only [hL, hUpper, hQ, hK]

private def squareRateProduct : ℕ := squarePrimeProduct squareRate

private def squareTaxProduct : ℕ := squarePrimeProduct (fun _ => 15)

set_option maxRecDepth 8192 in
private theorem square_pow_rate :
    7^100*2^16 < 3^100*squareRateProduct := by decide +kernel

set_option maxRecDepth 8192 in
private theorem square_pow_tax :
    3^6*squareTaxProduct ≤ 2^233 := by decide

private theorem three_hundred_succ_le_two_pow (q : ℕ) (hq : 13 ≤ q) :
    300*(q+1) ≤ 2^q := by
  induction q, hq using Nat.le_induction with
  | base => decide
  | succ q hq ih =>
    rw [pow_succ]
    omega

private theorem square_fifth_pow_le {k : ℕ} (hk : 4000 ≤ k) :
    k^5 ≤ 2^(2*(k/100)) := by
  let q := k/100
  let t := q/3
  have hq : 40 ≤ q := by dsimp [q]; omega
  have ht : 13 ≤ t := by dsimp [t]; omega
  have hk' : k ≤ 300*(t+1) := by dsimp [q,t] at *; omega
  have h := (Nat.pow_le_pow_left (hk'.trans (three_hundred_succ_le_two_pow _ ht)) 5)
  rw [← pow_mul] at h
  exact h.trans (pow_right_mono₀ (by decide) (show t*5 ≤ 2*q by dsimp [t]; omega))

private theorem square_large_rate_compare {k : ℕ} (hk : 4000 ≤ k) :
    7^k*k^5*(3^6*squareTaxProduct) < 3^k*squareRateProduct^(k/100) := by
  let q := k/100
  let r := k%100
  have hq : 40 ≤ q := by dsimp [q]; omega
  have hr : r ≤ 100 := by dsimp [r]; omega
  have hkq : 100*q+r=k := by dsimp [q,r]; omega
  have hker : 7^r ≤ 3^r*2^200 := calc
    7^r ≤ (3*2^2)^r := Nat.pow_le_pow_left (by decide) _
    _ = 3^r*2^(2*r) := by rw [mul_pow, ← pow_mul]
    _ ≤ 3^r*2^200 := Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
  have hpow : (7^100*2^16)^q < (3^100*squareRateProduct)^q :=
    pow_lt_pow_left₀ square_pow_rate (Nat.zero_le _) (by omega : q ≠ 0)
  have hsplit (a : ℕ) : a^k = (a^100)^q*a^r := by
    rw [← pow_mul, ← pow_add, hkq]
  rw [show k/100=q from rfl]
  calc
    7^k*k^5*(3^6*squareTaxProduct)
      = ((7^100)^q*7^r)*k^5*(3^6*squareTaxProduct) := by
        rw [hsplit 7]
    _ ≤ ((7^100)^q*(3^r*2^200))*2^(2*q)*2^233 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hker)
        (square_fifth_pow_le hk)) square_pow_tax
    _ = (7^100)^q*3^r*2^(433+2*q) := by
      rw [show 433+2*q=200+2*q+233 by omega, pow_add, pow_add]
      ac_rfl
    _ ≤ (7^100)^q*3^r*2^(16*q) :=
      Nat.mul_le_mul_left _ (pow_right_mono₀ (by decide) (by omega))
    _ = 3^r*(7^100*2^16)^q := by rw [mul_pow, ← pow_mul (2:ℕ) 16 q]; ac_rfl
    _ < 3^r*(3^100*squareRateProduct)^q := Nat.mul_lt_mul_of_pos_left hpow (by positivity)
    _ = _ := by rw [mul_pow, hsplit 3]; ring

theorem square_prime_obstruction_from_4000 {n k : ℕ} (hk : 4000 ≤ k) (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  let q := k/100
  have hD := square_product_adjusted_dvd (by omega : 3 ≤ k) hf (fun p => squareRate p*q)
    (fun _ => 15) (fun p hp _ => square_factorization_additive_saving (n := n) (k := k) (by omega) hp)
  rw [squarePrimeProduct_pow] at hD
  have h := scaled_square_upper (by omega) hn hD (squarePrimeProduct_pos _)
  change 3^(k-6)*squareRateProduct^q ≤ 2^(k-6)*k^5*primorial (k-1)*squareTaxProduct at h
  have hprim : 2^(k-6)*primorial (k-1) ≤ 7^k :=
    (Nat.mul_le_mul (pow_right_mono₀ (by decide) (Nat.sub_le _ _))
      (primorial_mono (Nat.sub_le _ _))).trans (primorial_le_seven_halves_pow k)
  have hcontra : 3^k*squareRateProduct^q ≤ 7^k*k^5*(3^6*squareTaxProduct) := calc
    3^k*squareRateProduct^q = (3^(k-6)*squareRateProduct^q)*3^6 := by
      have hsplit : (3:ℕ)^k = 3^(k-6)*3^6 := by
        rw [← pow_add, Nat.sub_add_cancel (show 6 ≤ k by omega)]
      rw [hsplit]
      ac_rfl
    _ ≤ (2^(k-6)*k^5*primorial (k-1)*squareTaxProduct)*3^6 := Nat.mul_le_mul_right _ h
    _ = (2^(k-6)*primorial (k-1))*k^5*(3^6*squareTaxProduct) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hprim)
  exact (not_lt_of_ge hcontra) (square_large_rate_compare hk)

private def squareDivFloorBonus (a p : ℕ) : ℕ :=
  a/p^2 + if p=2 then a/16 else 0

private def squareDivFloorCap (b p : ℕ) : ℕ :=
  b/p + b/p^3 + if p=2 then b/32+3 else 2

private def squareMidSaving (a b p : ℕ) : ℕ :=
  (∑ i ∈ Ico 1 9, (a-1)/p^i) + squareDivFloorBonus a p - squareDivFloorCap b p

private theorem square_mid_save_applies {n k a b p : ℕ} (hak : a ≤ k) (hkb : k ≤ b)
    (hp : p.Prime) (hn : squareMidSaving a b p ≠ 0) :
    (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j).factorization p + squareMidSaving a b p ≤
      (k-1).factorial.factorization p := by
  let A := ∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j
  let L := ∑ i ∈ Ico 1 9, (a-1)/p^i
  have hF : L ≤ (k-1).factorial.factorization p := calc
    L ≤ ∑ i ∈ Ico 1 9, (k-1)/p^i :=
      sum_le_sum fun i _ => Nat.div_le_div_right (Nat.sub_le_sub_right hak 1)
    _ ≤ _ := sum_le_factorial_factorization hp (k-1) 9
  have hc : A.factorization p + squareDivFloorBonus k p ≤ squareDivFloorCap k p := by
    by_cases h2 : p = 2
    · subst p
      simpa only [A, squareDivFloorBonus, squareDivFloorCap, if_pos rfl, show (2:ℕ)^2=4 by decide,
        show (2:ℕ)^3=8 by decide, if_true, Nat.add_assoc] using
        squareFreePart_two_factorization_plus_two_four_le n k
    · simpa only [A, squareDivFloorBonus, squareDivFloorCap, if_neg h2, add_zero] using
        squareFreePart_factorization_plus_two_le (n := n) (k := k) hp
  have ha : squareDivFloorBonus a p ≤ squareDivFloorBonus k p := by
    unfold squareDivFloorBonus
    by_cases h2 : p=2
    · simp only [h2, if_true]
      exact Nat.add_le_add (Nat.div_le_div_right hak) (Nat.div_le_div_right hak)
    · simp only [if_neg h2, add_zero]
      exact Nat.div_le_div_right hak
  have hb : squareDivFloorCap k p ≤ squareDivFloorCap b p := by
    unfold squareDivFloorCap
    apply Nat.add_le_add (Nat.add_le_add (Nat.div_le_div_right hkb) (Nat.div_le_div_right hkb))
    by_cases h2 : p=2
    · simp only [h2, if_true]
      exact Nat.add_le_add_right (Nat.div_le_div_right hkb) _
    · simp only [if_neg h2, le_refl]
  have h := (Nat.add_le_add_left ha (A.factorization p)).trans (hc.trans hb)
  change L + squareDivFloorBonus a p - squareDivFloorCap b p ≠ 0 at hn
  change A.factorization p + (L + squareDivFloorBonus a p - squareDivFloorCap b p) ≤ _
  omega

private def squareDyadicLog (p : ℕ) : ℕ :=
  match p with
  | 2 => 64
  | 3 => 101
  | 5 => 148
  | 7 => 179
  | 11 => 221
  | 13 => 236
  | _ => 0

private theorem squareDyadicLog_correct {p : ℕ} (hp : p ∈ squareSavingPrimes) :
    2^(squareDyadicLog p) ≤ p^64 := by
  simp only [squareSavingPrimes, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem square_dyadic_product_le (e : ℕ → ℕ) :
    2^(∑ p ∈ squareSavingPrimes, squareDyadicLog p*e p) ≤ (squarePrimeProduct e)^64 := by
  rw [← Finset.prod_pow_eq_pow_sum, squarePrimeProduct, ← Finset.prod_pow]
  apply prod_le_prod'
  intro p hp
  calc
    2^(squareDyadicLog p*e p) = (2^(squareDyadicLog p))^(e p) := by rw [pow_mul]
    _ ≤ (p^64)^(e p) := Nat.pow_le_pow_left (squareDyadicLog_correct hp) _
    _ = (p^(e p))^64 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 64]

private def squareMidExponent (a b : ℕ) : ℕ :=
  101*(a-6)+384+∑ p ∈ squareSavingPrimes, squareDyadicLog p * squareMidSaving a b p

private theorem square_mid_strict_comparison {a b t : ℕ} (hpow : b ≤ 2^t)
    (h : 180*b+320*t < squareMidExponent a b) :
    7^b*b^5 < 3^(a-6)*2^6*squarePrimeProduct (squareMidSaving a b) := by
  have hR : (7^b*b^5)^64 ≤ 2^(180*b+320*t) := by
    calc
      (7^b*b^5)^64 = (7^64)^b*b^320 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm b 64]
      _ ≤ (2^180)^b*(2^t)^320 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left hpow _)
      _ = 2^(180*b+320*t) := by rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_comm t 320]
  have hL : 2^(squareMidExponent a b) ≤
      (3^(a-6)*2^6*squarePrimeProduct (squareMidSaving a b))^64 := by
    unfold squareMidExponent
    rw [pow_add, pow_add, mul_pow, mul_pow]
    apply Nat.mul_le_mul ?_ (square_dyadic_product_le _)
    apply Nat.mul_le_mul_right
    calc
      2^(101*(a-6)) = (2^101)^(a-6) := pow_mul _ _ _
      _ ≤ (3^64)^(a-6) := Nat.pow_le_pow_left (by decide) _
      _ = (3^(a-6))^64 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 64]
  have hlt := hR.trans_lt ((pow_lt_pow_right₀ (by decide : 1 < (2:ℕ)) h).trans_le hL)
  by_contra! hh
  exact hlt.not_ge (Nat.pow_le_pow_left hh 64)

private def SquareMidCertificate (a : ℕ) : List (ℕ × ℕ) → Prop
  | [] => 4000 ≤ a
  | (b,t)::l => b ≤ 2^t ∧ 180*b+320*t < squareMidExponent a b ∧ SquareMidCertificate (b+1) l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem square_mid_certificate :
    SquareMidCertificate 824
    [(832, 10), (844, 10), (855, 10), (869, 10), (881, 10), (895, 10), (909, 10), (923, 10),
     (935, 10), (950, 10), (965, 10), (979, 10), (996, 10), (1013, 10), (1028, 11), (1046, 11),
     (1064, 11), (1082, 11), (1102, 11), (1122, 11), (1143, 11), (1164, 11), (1185, 11), (1209, 11),
     (1232, 11), (1259, 11), (1284, 11), (1311, 11), (1337, 11), (1365, 11), (1395, 11), (1427, 11),
     (1458, 11), (1493, 11), (1526, 11), (1562, 11), (1599, 11), (1637, 11), (1676, 11), (1715, 11),
     (1758, 11), (1802, 11), (1847, 11), (1892, 11), (1942, 11), (1992, 11), (2044, 11), (2096, 12),
     (2151, 12), (2207, 12), (2267, 12), (2328, 12), (2392, 12), (2457, 12), (2528, 12), (2599, 12),
     (2673, 12), (2750, 12), (2830, 12), (2912, 12), (2999, 12), (3086, 12), (3177, 12), (3273, 12),
     (3373, 12), (3472, 12), (3577, 12), (3688, 12), (3801, 12), (3919, 12), (3999, 12)] := by
  simp only [SquareMidCertificate]
  repeat' apply And.intro
  all_goals decide +kernel

private theorem square_mid_cert_lookup (l : List (ℕ × ℕ)) {a k : ℕ}
    (ha : a ≤ k) (hk : k < 4000) (hl : SquareMidCertificate a l) :
    ∃ a' b t, a' ≤ k ∧ k ≤ b ∧ b ≤ 2^t ∧ 180*b+320*t < squareMidExponent a' b := by
  induction l generalizing a with
  | nil =>
    change 4000 ≤ a at hl
    omega
  | cons z l ih =>
    obtain ⟨b,t⟩ := z
    rcases hl with ⟨hb, ht, hl⟩
    by_cases hkb : k ≤ b
    · exact ⟨a,b,t,ha,hkb,hb,ht⟩
    · exact ih (by omega) hl

theorem square_prime_obstruction_middle {n k : ℕ} (hk : 824 ≤ k) (hk' : k < 4000)
    (hn : k^2 < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_contra! hf
  obtain ⟨a,b,t,ha,hb,hb',ht⟩ := square_mid_cert_lookup _ hk hk' square_mid_certificate
  let E := squarePrimeProduct (squareMidSaving a b)
  have hdiv : (∏ j ∈ Icc (n+1) (n+k), powerFreePart 2 j)*E ∣
      ((k-1).factorial*primorial (k-1))*1 := by
    have h := square_product_adjusted_dvd (by omega : 3 ≤ k) hf (squareMidSaving a b)
      (fun _ => 0) (fun p hp hn => (square_mid_save_applies ha hb (squareSavingPrime hp) hn).trans
        (Nat.le_add_right _ _))
    simpa only [E, squarePrimeProduct, pow_zero, prod_const_one] using h
  have h := scaled_square_upper (by omega) hn hdiv (by decide)
  rw [mul_one] at h
  have hP : 2^k*primorial (k-1) ≤ 7^b :=
    ((Nat.mul_le_mul_left _ (primorial_mono (Nat.sub_le _ _))).trans
      (primorial_le_seven_halves_pow k)).trans (pow_right_mono₀ (by decide) hb)
  have hu : 3^(a-6)*2^6*E ≤ 7^b*b^5 := calc
    3^(a-6)*2^6*E ≤ (3^(k-6)*E)*2^6 := by
      rw [Nat.mul_right_comm (3^(a-6)) _ E]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (pow_right_mono₀ (by decide) (Nat.sub_le_sub_right ha _)))
    _ ≤ (2^(k-6)*k^5*primorial (k-1))*2^6 := Nat.mul_le_mul_right _ h
    _ = (2^k*primorial (k-1))*k^5 := by
      have hs : (2:ℕ)^k = 2^(k-6)*2^6 := by
        rw [← pow_add, Nat.sub_add_cancel (show 6 ≤ k by omega)]
      rw [hs]
      ring
    _ ≤ 7^b*b^5 := Nat.mul_le_mul hP (Nat.pow_le_pow_left hb _)
  exact (not_lt_of_ge hu) (square_mid_strict_comparison hb' ht)

theorem square_prime_obstruction_all {n k : ℕ} (hk : 3 ≤ k)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n+k) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ (2 ∣ (∏ j ∈ Icc (n+1) (n+k), j).factorization p) := by
  by_cases hbound : k < 824
  · exact square_prime_obstruction_bounded hk hbound hend
  by_cases hn : n ≤ k
  · exact short_interval k 2 n hk (by decide) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n+1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : (n+1)+i ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by decide : 2 ≤ 2) hpk hp hm hd
    (hf p hpk.le hp)
  by_cases hlarge : 4000 ≤ k
  · obtain ⟨q,hq,hq',hbad⟩ := square_prime_obstruction_from_4000 hlarge hgt
    exact hbad (hf q hq hq')
  · obtain ⟨q,hq,hq',hbad⟩ := square_prime_obstruction_middle (by omega) (by omega) hgt
    exact hbad (hf q hq hq')


theorem consecutive_strong_of_even_exponent {n k l : ℕ} (hk : 3 ≤ k) (hl : 2 ∣ l)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  obtain ⟨p, hpk, hp, hnd⟩ := square_prime_obstruction_all hk hend
  exact ⟨p, hpk, hp, fun h => hnd (dvd_trans hl h)⟩

theorem consecutive_strong_through_thousand {n k l : ℕ} (hk : 3 ≤ k) (hu : k ≤ 1000)
    (hl : 2 ≤ l) (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  by_cases he : 2 ∣ l
  · exact consecutive_strong_of_even_exponent hk he hend
  by_cases h₆ : 6 ≤ k
  · exact width_up_to_thousand_for_exponent_three_or_five_le h₆ (by omega) (by omega) hend
  interval_cases k
  · exact three_factors l n hl
  · exact four_factors l n hl hend
  · exact five_factors l n hl hend


theorem ordered_pair_counting_obstruction_with_sparse_tail {n k l : ℕ}
    (hk : 3 ≤ k) (hl : 3 ≤ l) (hn : k ^ l < n) (S P Q : Finset ℕ)
    (hSI : S ⊆ Icc (n + 1) (n + k))
    (hPQ : ∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hPair : ∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) :
    S.card * (S.card - 1) ≤ l ^ P.card * (Q.card + 1) ^ 2 := by
  classical
  let _ : NeZero l := ⟨by omega⟩
  have hS (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by
    have := (mem_Icc.mp (hSI hj)).1
    omega
  obtain ⟨tag, htag⟩ := sparsePrimeTailTag S Q hS hQ hPair
  let left (x : S.offDiag) : S := ⟨x.val.1, (mem_offDiag.mp x.property).1⟩
  let right (x : S.offDiag) : S := ⟨x.val.2, (mem_offDiag.mp x.property).2.1⟩
  let f (x : S.offDiag) : (P → ZMod l) × Option (↑Q) × Option (↑Q) :=
    (fun p => (x.val.1.factorization p : ZMod l) - (x.val.2.factorization p : ZMod l),
      tag (left x), tag (right x))
  have inj : Function.Injective f := by
    intro x y hxy
    apply offDiag_eq_of_valuation_differences hk hl hn S hSI x y
    intro p
    by_cases hp : p ∈ P
    · exact congrFun (congrArg Prod.fst hxy) (⟨p, hp⟩ : P)
    by_cases hq : p ∈ Q
    · let q : Q := ⟨p, hq⟩
      have h₁ : tag (left x) = tag (left y) := congrArg (fun c => c.2.1) hxy
      have h₂ : tag (right x) = tag (right y) := congrArg (fun c => c.2.2) hxy
      change ((left x).val.factorization q : ZMod l) - ((right x).val.factorization q : ZMod l) =
        ((left y).val.factorization q : ZMod l) - ((right y).val.factorization q : ZMod l)
      rw [htag, htag, htag, htag, h₁, h₂]
    · have hpq : p ∉ P ∪ Q := by simp [hp, hq]
      have hx := mem_offDiag.mp x.property
      have hy := mem_offDiag.mp y.property
      rw [natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hx.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hx.2.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hy.1 p hpq),
        natCast_eq_zero_zmod_of_mod_eq_zero (hPQ _ hy.2.1 p hpq)]
  have h := Fintype.card_le_of_injective f inj
  simpa [Fintype.card_fun, ZMod.card, offDiag_card, Nat.mul_sub_left_distrib, pow_two] using h

private def symPairProduct : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨(· * ·), mul_comm⟩

private def pairSieveUpperCount (k : ℕ) (Q : Finset ℕ) : ℕ :=
  ∑ z ∈ Q.sym2, (k / symPairProduct z + 1)

private theorem pairSieveUpperCount_mono (Q : Finset ℕ) : Monotone (pairSieveUpperCount · Q) := by
  intro a b hab
  unfold pairSieveUpperCount
  exact sum_le_sum (fun _ _ => Nat.add_le_add_right (Nat.div_le_div_right hab) _)

private theorem small_prime_sieve_with_sparse_tail {n k l : ℕ} (P Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hf : ∀ p, k ≤ p → p.Prime →
      l ∣ (∏ j ∈ Icc (n + 1) (n + k), j).factorization p) :
    ∃ S ⊆ Icc (n + 1) (n + k),
      k - (sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q) ≤ S.card ∧
      (∀ j ∈ S, ∀ p ∉ P ∪ Q, j.factorization p % l = 0) ∧
      (∀ j ∈ S, ∀ p ∈ Q, ∀ q ∈ Q, ¬ (p * q ∣ j)) := by
  classical
  obtain ⟨T, hTI, hTcard, hTout⟩ := small_prime_sieve (P ∪ Q) hf
  let I := Icc (n + 1) (n + k)
  let D := Q.sym2.biUnion (fun z => I.filter (symPairProduct z ∣ ·))
  let S := T \ D
  have hD : D.card ≤ pairSieveUpperCount k Q := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro z hz
    induction z using Sym2.ind with
    | h p q =>
      have hz' := mk_mem_sym2_iff.mp hz
      have hpos : 0 < p * q := Nat.mul_pos (hQ p hz'.1).pos (hQ q hz'.2).pos
      change intervalMultipleCount n k (p * q) ≤ k / (p * q) + 1
      exact (intervalMultipleCount_bounds n k _ hpos).2
  have hTS : S ⊆ T := sdiff_subset
  have hScard : T.card - D.card ≤ S.card := le_card_sdiff D T
  refine ⟨S, hTS.trans hTI, ?_, ?_, ?_⟩
  · omega
  · exact fun j hj p hp => hTout j (hTS hj) p hp
  · intro j hj p hp q hq hd
    have hbad : j ∈ D := mem_biUnion.mpr
      ⟨s(p, q), mk_mem_sym2_iff.mpr ⟨hp, hq⟩, mem_filter.mpr ⟨hTI (hTS hj), hd⟩⟩
    exact (mem_sdiff.mp hj).2 hbad


private theorem power_ratio_from_five_with_tail {f m q l : ℕ} (hl : 5 ≤ l)
    (hBase : (q + 5) * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    (l + 1) ^ m * (l + q) ≤ (l + (f - 1)) * l ^ m := by
  have lpos : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have l5 : (5 : ℝ) ≤ l := by exact_mod_cast hl
  let t : ℝ := 5 / l
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_iff₀ lpos).2 (by simpa using l5)
  have hc := (convexOn_pow (𝕜 := ℝ) m).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) (show (6 / 5 : ℝ) ∈ Set.Ici 0 by norm_num)
    (sub_nonneg.mpr ht1) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_one, one_pow] at hc
  have hmix : 1 - t + t * (6 / 5 : ℝ) = ((l : ℝ) + 1) / (l : ℝ) := by
    dsimp [t]
    field_simp; ring
  rw [hmix] at hc
  let c : ℝ := (6 / 5 : ℝ) ^ m - 1
  have hc0 : 0 ≤ c := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hconv : (((l : ℝ) + 1) / l) ^ m ≤ 1 + t * c := by
    calc
      _ ≤ 1 - t + t * (6 / 5 : ℝ) ^ m := hc
      _ = _ := by dsimp [c]; ring
  have hrate : ((q : ℝ) + 5) * (6 / 5 : ℝ) ^ m ≤ ((f - 1 : ℕ) : ℝ) + 5 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos (by norm_num) _)]
    exact_mod_cast hBase
  have htc : t * ((l : ℝ) + q) ≤ (q : ℝ) + 5 := by
    calc
      t * ((l : ℝ) + q) = 5 + t * q := by
        dsimp [t]
        field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg q : 0 ≤ (q : ℝ))
        linarith
  have hout :
      (((l : ℝ) + 1) / (l : ℝ)) ^ m * ((l : ℝ) + q) ≤ (l : ℝ) + ((f - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (1 + t * c) * ((l : ℝ) + q) := mul_le_mul_of_nonneg_right hconv (by positivity)
      _ = ((l : ℝ) + q) + (t * ((l : ℝ) + q)) * c := by ring
      _ ≤ ((l : ℝ) + q) + ((q : ℝ) + 5) * c :=
        add_le_add_right (mul_le_mul_of_nonneg_right htc hc0) _
      _ ≤ _ := by
        dsimp [c]
        linarith only [hrate, mul_sub (((q : ℝ) + 5)) ((6 / 5 : ℝ) ^ m) 1,
          mul_one ((q : ℝ) + 5)]
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos lpos _)] at hout
  exact_mod_cast hout

private theorem choose_gt_pow_from_five_with_tail {f m q l : ℕ}
    (hf : 2 ≤ f) (hl : 5 ≤ l)
    (hBase : 5 ^ m * (q + 4).choose q < (f + 3).choose (f - 1))
    (hRatio : (q + 5) * 6 ^ m ≤ (f - 1 + 5) * 5 ^ m) :
    l ^ m * (q + l - 1).choose q < (f + l - 2).choose (f - 1) := by
  induction l, hl using Nat.le_induction with
  | base =>
    simpa only [show f + 5 - 2 = f + 3 by omega, show q + 5 - 1 = q + 4 by omega] using hBase
  | succ l hl ih =>
    have hr := power_ratio_from_five_with_tail hl hRatio
    have hF := Nat.choose_mul_succ_eq (f + l - 2) (f - 1)
    have hQ := Nat.choose_mul_succ_eq (q + l - 1) q
    rw [show f + l - 2 + 1 - (f - 1) = l by omega] at hF
    rw [show q + l - 1 + 1 - q = l by omega] at hQ
    apply Nat.lt_of_mul_lt_mul_right
    calc
      ((l + 1) ^ m * (q + (l + 1) - 1).choose q) * l =
          ((l + 1) ^ m * (l + q)) * (q + l - 1).choose q := by
        rw [mul_assoc, show q + (l + 1) - 1 = q + l - 1 + 1 by omega, ← hQ,
          show q + l - 1 + 1 = l + q by omega]
        ac_rfl
      _ ≤ ((l + (f - 1)) * l ^ m) * (q + l - 1).choose q :=
        Nat.mul_le_mul_right _ hr
      _ = (l ^ m * (q + l - 1).choose q) * (f + l - 2 + 1) := by
        rw [show l + (f - 1) = f + l - 2 + 1 by omega]
        ac_rfl
      _ < (f + l - 2).choose (f - 1) * (f + l - 2 + 1) :=
        Nat.mul_lt_mul_of_pos_right ih (by omega)
      _ = (f + (l + 1) - 2).choose (f - 1) * l := by
        rw [hF, show f + l - 2 + 1 = f + (l + 1) - 2 by omega]


theorem consecutive_strong_of_sparse_sieve_bound {n k l f : ℕ}
    (hk : 3 ≤ k) (hl : l = 3 ∨ 5 ≤ l)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) (P Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime)
    (hwidth : 2 ≤ f)
    (hsieve : f + sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q ≤ k)
    (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
    (hfifth : 5 ^ P.card * (Q.card + 4).choose Q.card < (f + 3).choose (f - 1))
    (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  have hl3 : 3 ≤ l := by omega
  by_cases hn : n ≤ k
  · exact short_interval k l n hk (by omega) hend hn
  by_contra! hf
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : n + 1 + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := modulus_growth_of_large_prime (by omega) (by omega : 2 ≤ l) hpk hp hm hd (hf p hpk.le hp)
  obtain ⟨S, hSI, hS, hSupp, hPair⟩ := small_prime_sieve_with_sparse_tail P Q hQ hf
  have hfs : f ≤ S.card := by omega
  rcases hl with rfl | hl
  · have h := ordered_pair_counting_obstruction_with_sparse_tail hk (by decide)
      hgt S P Q hSI hSupp hQ hPair
    exact (not_lt_of_ge ((Nat.mul_le_mul hfs (Nat.sub_le_sub_right hfs 1)).trans h)) hcube
  · have h := counting_obstruction_with_sparse_tail hk hgt (r := l - 1)
      (by omega) (by omega) S P Q hSI hSupp hQ hPair
    have hfchoose :=
      Nat.choose_le_choose (l - 1) (show f + (l - 1) - 1 ≤ S.card + (l - 1) - 1 by omega)
    have hs1 : f + l - 2 - (f - 1) = l - 1 := by omega
    have hs2 : f - 1 ≤ f + l - 2 := by omega
    have hSym := Nat.choose_symm hs2
    rw [hs1] at hSym
    rw [show f + (l - 1) - 1 = f + l - 2 by omega, hSym] at hfchoose
    have hqChoose : (Q.card + (l - 1)).choose (l - 1) = (Q.card + l - 1).choose Q.card := by
      rw [show Q.card + l - 1 = Q.card + (l - 1) by omega]
      exact (Nat.choose_symm_add (a := Q.card) (b := l - 1)).symm
    rw [hqChoose] at h
    exact (not_lt_of_ge (hfchoose.trans h))
      (choose_gt_pow_from_five_with_tail hwidth hl hfifth hratio)


private inductive SparseSieveCover : ℕ → ℕ → Prop
  | done (a : ℕ) : SparseSieveCover a a
  | more {a b c f : ℕ} (P Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (hab : a < b) (hwidth : 2 ≤ f)
      (hsieve : f + sieveUpperCount (b - 1) (P ∪ Q) + pairSieveUpperCount (b - 1) Q ≤ a)
      (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
      (hfifth : 5 ^ P.card * (Q.card + 4).choose Q.card < (f + 3).choose (f - 1))
      (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card)
      (rest : SparseSieveCover b c) : SparseSieveCover a c

private theorem consecutive_strong_of_sparse_sieve_cover {a b : ℕ} (cover : SparseSieveCover a b) :
    ∀ k l n : ℕ, a ≤ k → k < b → 3 ≤ k → (l = 3 ∨ 5 ≤ l) →
      ErdosSelfridge.firstPrimeAtLeast k ≤ n + k →
        ∃ p, k ≤ p ∧ p.Prime ∧
          ¬ (l ∣ Nat.factorization (∏ j ∈ Icc (n + 1) (n + k), j) p) := by
  induction cover with
  | done a => intro k l n hlow hhigh; omega
  | @more a b c f P Q hQ hab hwidth hsieve hcube hfifth hratio hrest ih =>
    intro k l n hlow hhigh hk hl hend
    by_cases hkb : b ≤ k
    · exact ih k l n hkb hhigh hk hl hend
    have hkb' : k ≤ b - 1 := by omega
    have h' : f + sieveUpperCount k (P ∪ Q) + pairSieveUpperCount k Q ≤ k :=
      (Nat.add_le_add (Nat.add_le_add_left (sieveUpperCount_mono (P ∪ Q) hkb') f)
        (pairSieveUpperCount_mono Q hkb')).trans (hsieve.trans hlow)
    exact consecutive_strong_of_sparse_sieve_bound hk hl hend P Q hQ hwidth h' hcube hfifth hratio

end ErdosSelfridge

namespace ErdosSelfridge

/-- The verified product of the primes up to 500. -/
private def sievePrimorial : ℕ :=
  124846525121166472890127769845656706959834701767553316679575342375728606681436245953703527478773456698735316531921607496638484885416740029028542605893861455745313937474271661656548230159065196413238268640890

private theorem sievePrimorial_eq : sievePrimorial = primorial 500 := by
  decide +kernel

private theorem gcd_sievePrimorial_eq_one {p : ℕ} (hp : 500 < p) (hmax : p ≤ 250000) :
    Nat.gcd p sievePrimorial = 1 ↔ p.Prime := by
  rw [sievePrimorial_eq, ← Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro hc
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, ?_⟩
    intro d hd hds hdvd
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := d) (by omega)
    have hsqrt : p.sqrt < 501 := Nat.sqrt_lt.mpr (hmax.trans_lt (by decide))
    have hqd' := Nat.le_of_dvd (by omega : 0 < d) hqd
    have hdiv := Nat.dvd_gcd (hqd.trans hdvd)
      (hq.dvd_primorial_iff.mpr (show q ≤ 500 by omega))
    rw [Nat.coprime_iff_gcd_eq_one.mp hc] at hdiv
    exact hq.not_dvd_one hdiv
  · intro hPrime
    exact hPrime.coprime_iff_not_dvd.mpr
      (fun hd => (not_le_of_gt hp) (hPrime.dvd_primorial_iff.mp hd))

private theorem smallWheel_dvd_sievePrimorial : 30030 ∣ sievePrimorial := by decide +kernel

private def sievePrimeTest (p : ℕ) : Bool :=
  if 500 < p ∧ p ≤ 250000 then
    decide (Nat.gcd p 30030 = 1) && decide (Nat.gcd p sievePrimorial = 1)
  else primeTest p

private theorem sievePrimeTest_eq_true {p : ℕ} : sievePrimeTest p = true ↔ p.Prime := by
  unfold sievePrimeTest
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [gcd_sievePrimorial_eq_one h.1 h.2]
    constructor
    · exact And.right
    · intro hp
      refine ⟨?_, hp⟩
      have hdiv := Nat.gcd_dvd_gcd_of_dvd_right p smallWheel_dvd_sievePrimorial
      rw [(gcd_sievePrimorial_eq_one h.1 h.2).mpr hp] at hdiv
      exact Nat.dvd_one.mp hdiv
  next _ => exact primeTest_eq_true

private def primesIn (start length : ℕ) : List ℕ :=
  (List.range' start length).filter sievePrimeTest

private theorem mem_primesIn {start length p : ℕ} :
    p ∈ primesIn start length ↔ start ≤ p ∧ p < start + length ∧ p.Prime := by
  simp only [primesIn, List.mem_filter, List.mem_range'_1, sievePrimeTest_eq_true, and_assoc]

private theorem primesIn_nodup (start length : ℕ) : (primesIn start length).Nodup :=
  List.Nodup.filter _ List.nodup_range'

private theorem primesIn_append (start length extra : ℕ) :
    primesIn start (length + extra) = primesIn start length ++ primesIn (start + length) extra := by
  simp only [primesIn, ← List.range'_append_1, List.filter_append]

private inductive VerifiedPrimeBlocks : ℕ → ℕ → List (List ℕ) → Prop
  | done (a : ℕ) : VerifiedPrimeBlocks a a []
  | append {a b c : ℕ} {row : List ℕ} {rows : List (List ℕ)}
      (hab : a ≤ b) (hbc : b ≤ c) (hrow : primesIn a (b - a) = row)
      (rest : VerifiedPrimeBlocks b c rows) : VerifiedPrimeBlocks a c (row :: rows)

private theorem VerifiedPrimeBlocks.flatten {a b : ℕ} {rows : List (List ℕ)}
    (h : VerifiedPrimeBlocks a b rows) : primesIn a (b - a) = rows.flatten := by
  induction h with
  | done a => simp [primesIn]
  | @append a b c row rows hab hbc hrow _ ih =>
    have hadd : b - a + (c - b) = c - a := by omega
    have hstart : a + (b - a) = b := by omega
    simpa only [hadd, hstart, hrow, ih, List.flatten_cons] using
      primesIn_append a (b - a) (c - b)

private def primeBlockRowCost (k cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    if k ≤ p then 0
    else (((p :: ps).filter (fun q => decide (cut < q ∧ q < k))).map (fun q => k / q + 1)).sum

private theorem primeBlockRowCost_eq (k cut : ℕ) {row : List ℕ} (hs : row.Pairwise (· < ·)) :
    primeBlockRowCost k cut row =
      ((row.filter (fun q => decide (cut < q ∧ q < k))).map (fun q => k / q + 1)).sum := by
  cases row with
  | nil => rfl
  | cons p ps =>
    by_cases hkp : k ≤ p
    · have hfilter : (p :: ps).filter (fun q => decide (cut < q ∧ q < k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq htest
        have hpq : p ≤ q := by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact le_rfl
          · exact ((List.pairwise_cons.mp hs).1 q hq).le
        exact (not_lt_of_ge (hkp.trans hpq)) (of_decide_eq_true htest).2
      simp only [primeBlockRowCost, hkp, if_true, hfilter, List.map_nil, List.sum_nil]
    · simp only [primeBlockRowCost, hkp, if_false]

private def primeBlockCost (k cut : ℕ) (blocks : List (List ℕ)) : ℕ :=
  (blocks.map (primeBlockRowCost k cut)).sum

private theorem primeBlockCost_flatten (k cut : ℕ) {a b : ℕ} {blocks : List (List ℕ)}
    (hblocks : VerifiedPrimeBlocks a b blocks) :
    primeBlockCost k cut blocks =
      ((blocks.flatten.filter (fun p => decide (cut < p ∧ p < k))).map (fun p => k / p + 1)).sum := by
  induction hblocks with
  | done a => rfl
  | @append a b c row rows _ _ hrow _ ih =>
    have hs : row.Pairwise (· < ·) := by
      rw [← hrow]
      exact (List.pairwise_lt_range').filter _
    change primeBlockRowCost k cut row + primeBlockCost k cut rows = _
    rw [primeBlockRowCost_eq k cut hs, ih]
    simp only [List.flatten_cons, List.filter_append, List.map_append, List.sum_append]

private theorem sieveUpperCount_eq_blockCost {k cut limit : ℕ} (hk : k ≤ limit)
    {blocks : List (List ℕ)} (hblocks : VerifiedPrimeBlocks 0 limit blocks)
    (P : Finset ℕ) (hP : ∀ p, p ∈ P ↔ p.Prime ∧ p ≤ cut) :
    sieveUpperCount k P = primeBlockCost k cut blocks := by
  rw [primeBlockCost_flatten k cut hblocks]
  have ht : primesIn 0 limit = blocks.flatten := by
    simpa only [Nat.sub_zero] using hblocks.flatten
  rw [← ht]
  let primes := (primesIn 0 limit).filter (fun p => decide (cut < p ∧ p < k))
  have hset : ((range k).filter Nat.Prime) \ P = primes.toFinset := by
    ext p
    simp only [mem_sdiff, mem_filter, mem_range, hP, List.mem_toFinset, primes, List.mem_filter,
      mem_primesIn, Nat.zero_le, Nat.zero_add, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hpk, hp⟩, hpP⟩
      have hpc : ¬p ≤ cut := fun h => hpP ⟨hp, h⟩
      exact ⟨⟨hpk.trans_le hk, hp⟩, by omega, hpk⟩
    · rintro ⟨⟨_, hp⟩, hcp, hpk⟩
      exact ⟨⟨hpk, hp⟩, fun h => by omega⟩
  rw [sieveUpperCount, unretainedPrimes, hset, List.sum_toFinset _ (List.Nodup.filter _ (primesIn_nodup 0 limit))]

private theorem choose_four_symm (n : ℕ) (hn : 1 ≤ n) :
    (n + 3).choose (n - 1) = (n + 3).choose 4 := by
  have h := Nat.choose_symm (n := n + 3) (k := 4) (by omega)
  rw [show n + 3 - 4 = n - 1 by omega] at h
  exact h

private theorem tail_choose_four (n : ℕ) :
    (n + 4).choose n = (n + 4).choose 4 :=
  Nat.choose_symm_add

private theorem sparseSieveRow {limit a b c f cut : ℕ} {blocks : List (List ℕ)}
    {P Q : Finset ℕ} (hblocks : VerifiedPrimeBlocks 0 limit blocks)
    (hretained : P ∪ Q = (primesIn 0 (cut + 1)).toFinset)
    (hlimit : b - 1 ≤ limit) (hab : a < b) (hf : 2 ≤ f)
    (hcost : f + primeBlockCost (b - 1) cut blocks + pairSieveUpperCount (b - 1) Q ≤ a)
    (hcube : 3 ^ P.card * (Q.card + 1) ^ 2 < f * (f - 1))
    (hfifth : 5 ^ P.card * ((Q.card + 4).descFactorial 4 / 24) <
      (f + 3).descFactorial 4 / 24)
    (hratio : (Q.card + 5) * 6 ^ P.card ≤ (f - 1 + 5) * 5 ^ P.card)
    (rest : SparseSieveCover b c) : SparseSieveCover a c := by
  have hret : ∀ p, p ∈ P ∪ Q ↔ p.Prime ∧ p ≤ cut := by
    intro p
    rw [hretained, List.mem_toFinset, mem_primesIn]
    simp only [Nat.zero_le, Nat.zero_add, true_and, Nat.lt_succ_iff, and_comm]
  refine .more P Q (fun p hp => ((hret p).mp (mem_union_right P hp)).1) hab hf ?_ hcube ?_ hratio rest
  · rw [sieveUpperCount_eq_blockCost hlimit hblocks (P ∪ Q) hret]
    exact hcost
  · simpa only [tail_choose_four, choose_four_symm f (by omega : 1 ≤ f),
      Nat.choose_eq_descFactorial_div_factorial, show Nat.factorial 4 = 24 by decide] using hfifth

private def sieveRetainedPrimes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503
]

private def sieveFreePrimes (m : ℕ) : Finset ℕ :=
  (sieveRetainedPrimes.take m).toFinset

private def sieveTailPrimes (m retained : ℕ) : Finset ℕ :=
  ((sieveRetainedPrimes.take retained).drop m).toFinset

/-- Summation over the upper triangle of a duplicate-free list, including its diagonal. -/
private def pairListCost (k : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    (((p :: ps).map (fun q => k / (p * q) + 1)).sum) + pairListCost k ps

private theorem symPairProduct_mk (p q : ℕ) : symPairProduct (Sym2.mk p q) = p * q := rfl

private theorem pairListCost_eq (k : ℕ) (ps : List ℕ) :
    (ps.sym2.map (fun z => k / symPairProduct z + 1)).sum = pairListCost k ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.sym2, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      symPairProduct_mk, pairListCost, ih]

private theorem pairSieveUpperCount_of_list (k : ℕ) {ps : List ℕ} (hs : ps.Nodup) :
    pairSieveUpperCount k ps.toFinset = pairListCost k ps := by
  change (ps.toFinset.val.sym2.map (fun z => k / symPairProduct z + 1)).sum = _
  rw [List.toFinset_val, List.dedup_eq_self.mpr hs, Multiset.sym2_coe, Multiset.map_coe, Multiset.sum_coe]
  exact pairListCost_eq k ps

private theorem sieveRetainedPrimes_nodup : sieveRetainedPrimes.Nodup := by decide +kernel

private theorem sieveTailPairCost (k m retained : ℕ) :
    pairSieveUpperCount k (sieveTailPrimes m retained) =
      pairListCost k ((sieveRetainedPrimes.take retained).drop m) :=
  pairSieveUpperCount_of_list k (sieveRetainedPrimes_nodup.take.drop)

set_option maxRecDepth 4096 in
private def sievePrimesBlock0 : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
  727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
  1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
  1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
  1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
  1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
  1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
  1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
  1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
  1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock1 : List ℕ := [
  2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
  2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251,
  2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
  2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477,
  2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647,
  2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
  2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857,
  2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001,
  3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163,
  3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299,
  3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407,
  3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539,
  3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659,
  3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793,
  3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919,
  3923, 3929, 3931, 3943, 3947, 3967, 3989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock2 : List ℕ := [
  4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111,
  4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243,
  4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391,
  4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519,
  4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657,
  4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799,
  4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951,
  4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077,
  5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227,
  5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387,
  5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501,
  5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647,
  5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779,
  5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879,
  5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock3 : List ℕ := [
  6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131,
  6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269,
  6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373,
  6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553,
  6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691,
  6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829,
  6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967,
  6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109,
  7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247,
  7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451,
  7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559,
  7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687,
  7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841,
  7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock4 : List ℕ := [
  8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147,
  8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287,
  8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431,
  8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599,
  8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719,
  8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849,
  8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007,
  9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157,
  9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293,
  9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431,
  9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551,
  9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721,
  9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851,
  9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock5 : List ℕ := [
  10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141,
  10151, 10159, 10163, 10169, 10177, 10181, 10193, 10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273,
  10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433,
  10453, 10457, 10459, 10463, 10477, 10487, 10499, 10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601,
  10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733,
  10739, 10753, 10771, 10781, 10789, 10799, 10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891,
  10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069,
  11071, 11083, 11087, 11093, 11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213,
  11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369,
  11383, 11393, 11399, 11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519,
  11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699, 11701,
  11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839,
  11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981,
  11987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock6 : List ℕ := [
  12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149,
  12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289,
  12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451,
  12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577,
  12583, 12589, 12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713,
  12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893,
  12899, 12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007,
  13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163,
  13171, 13177, 13183, 13187, 13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327,
  13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477,
  13487, 13499, 13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669,
  13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781,
  13789, 13799, 13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921,
  13931, 13933, 13963, 13967, 13997, 13999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock7 : List ℕ := [
  14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153, 14159, 14173,
  14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369,
  14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519,
  14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653,
  14657, 14669, 14683, 14699, 14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779,
  14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929,
  14939, 14947, 14951, 14957, 14969, 14983, 15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101,
  15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259,
  15263, 15269, 15271, 15277, 15287, 15289, 15299, 15307, 15313, 15319, 15329, 15331, 15349, 15359, 15361, 15373,
  15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527,
  15541, 15551, 15559, 15569, 15581, 15583, 15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667,
  15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803,
  15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889, 15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971,
  15973, 15991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock8 : List ℕ := [
  16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111, 16127, 16139,
  16141, 16183, 16187, 16189, 16193, 16217, 16223, 16229, 16231, 16249, 16253, 16267, 16273, 16301, 16319, 16333,
  16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427, 16433, 16447, 16451, 16453, 16477, 16481,
  16487, 16493, 16519, 16529, 16547, 16553, 16561, 16567, 16573, 16603, 16607, 16619, 16631, 16633, 16649, 16651,
  16657, 16661, 16673, 16691, 16693, 16699, 16703, 16729, 16741, 16747, 16759, 16763, 16787, 16811, 16823, 16829,
  16831, 16843, 16871, 16879, 16883, 16889, 16901, 16903, 16921, 16927, 16931, 16937, 16943, 16963, 16979, 16981,
  16987, 16993, 17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053, 17077, 17093, 17099, 17107, 17117, 17123,
  17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231, 17239, 17257, 17291, 17293, 17299, 17317,
  17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389, 17393, 17401, 17417, 17419, 17431, 17443,
  17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519, 17539, 17551, 17569, 17573, 17579, 17581,
  17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669, 17681, 17683, 17707, 17713, 17729, 17737, 17747, 17749,
  17761, 17783, 17789, 17791, 17807, 17827, 17837, 17839, 17851, 17863, 17881, 17891, 17903, 17909, 17911, 17921,
  17923, 17929, 17939, 17957, 17959, 17971, 17977, 17981, 17987, 17989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock9 : List ℕ := [
  18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077, 18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143,
  18149, 18169, 18181, 18191, 18199, 18211, 18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289,
  18301, 18307, 18311, 18313, 18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439,
  18443, 18451, 18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593,
  18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773, 18787, 18793,
  18797, 18803, 18839, 18859, 18869, 18899, 18911, 18913, 18917, 18919, 18947, 18959, 18973, 18979, 19001, 19009,
  19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121, 19139, 19141, 19157, 19163, 19181, 19183,
  19207, 19211, 19213, 19219, 19231, 19237, 19249, 19259, 19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373,
  19379, 19381, 19387, 19391, 19403, 19417, 19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469,
  19471, 19477, 19483, 19489, 19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603,
  19609, 19661, 19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793,
  19801, 19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937, 19949, 19961,
  19963, 19973, 19979, 19991, 19993, 19997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock10 : List ℕ := [
  20011, 20021, 20023, 20029, 20047, 20051, 20063, 20071, 20089, 20101, 20107, 20113, 20117, 20123, 20129, 20143,
  20147, 20149, 20161, 20173, 20177, 20183, 20201, 20219, 20231, 20233, 20249, 20261, 20269, 20287, 20297, 20323,
  20327, 20333, 20341, 20347, 20353, 20357, 20359, 20369, 20389, 20393, 20399, 20407, 20411, 20431, 20441, 20443,
  20477, 20479, 20483, 20507, 20509, 20521, 20533, 20543, 20549, 20551, 20563, 20593, 20599, 20611, 20627, 20639,
  20641, 20663, 20681, 20693, 20707, 20717, 20719, 20731, 20743, 20747, 20749, 20753, 20759, 20771, 20773, 20789,
  20807, 20809, 20849, 20857, 20873, 20879, 20887, 20897, 20899, 20903, 20921, 20929, 20939, 20947, 20959, 20963,
  20981, 20983, 21001, 21011, 21013, 21017, 21019, 21023, 21031, 21059, 21061, 21067, 21089, 21101, 21107, 21121,
  21139, 21143, 21149, 21157, 21163, 21169, 21179, 21187, 21191, 21193, 21211, 21221, 21227, 21247, 21269, 21277,
  21283, 21313, 21317, 21319, 21323, 21341, 21347, 21377, 21379, 21383, 21391, 21397, 21401, 21407, 21419, 21433,
  21467, 21481, 21487, 21491, 21493, 21499, 21503, 21517, 21521, 21523, 21529, 21557, 21559, 21563, 21569, 21577,
  21587, 21589, 21599, 21601, 21611, 21613, 21617, 21647, 21649, 21661, 21673, 21683, 21701, 21713, 21727, 21737,
  21739, 21751, 21757, 21767, 21773, 21787, 21799, 21803, 21817, 21821, 21839, 21841, 21851, 21859, 21863, 21871,
  21881, 21893, 21911, 21929, 21937, 21943, 21961, 21977, 21991, 21997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock11 : List ℕ := [
  22003, 22013, 22027, 22031, 22037, 22039, 22051, 22063, 22067, 22073, 22079, 22091, 22093, 22109, 22111, 22123,
  22129, 22133, 22147, 22153, 22157, 22159, 22171, 22189, 22193, 22229, 22247, 22259, 22271, 22273, 22277, 22279,
  22283, 22291, 22303, 22307, 22343, 22349, 22367, 22369, 22381, 22391, 22397, 22409, 22433, 22441, 22447, 22453,
  22469, 22481, 22483, 22501, 22511, 22531, 22541, 22543, 22549, 22567, 22571, 22573, 22613, 22619, 22621, 22637,
  22639, 22643, 22651, 22669, 22679, 22691, 22697, 22699, 22709, 22717, 22721, 22727, 22739, 22741, 22751, 22769,
  22777, 22783, 22787, 22807, 22811, 22817, 22853, 22859, 22861, 22871, 22877, 22901, 22907, 22921, 22937, 22943,
  22961, 22963, 22973, 22993, 23003, 23011, 23017, 23021, 23027, 23029, 23039, 23041, 23053, 23057, 23059, 23063,
  23071, 23081, 23087, 23099, 23117, 23131, 23143, 23159, 23167, 23173, 23189, 23197, 23201, 23203, 23209, 23227,
  23251, 23269, 23279, 23291, 23293, 23297, 23311, 23321, 23327, 23333, 23339, 23357, 23369, 23371, 23399, 23417,
  23431, 23447, 23459, 23473, 23497, 23509, 23531, 23537, 23539, 23549, 23557, 23561, 23563, 23567, 23581, 23593,
  23599, 23603, 23609, 23623, 23627, 23629, 23633, 23663, 23669, 23671, 23677, 23687, 23689, 23719, 23741, 23743,
  23747, 23753, 23761, 23767, 23773, 23789, 23801, 23813, 23819, 23827, 23831, 23833, 23857, 23869, 23873, 23879,
  23887, 23893, 23899, 23909, 23911, 23917, 23929, 23957, 23971, 23977, 23981, 23993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock12 : List ℕ := [
  24001, 24007, 24019, 24023, 24029, 24043, 24049, 24061, 24071, 24077, 24083, 24091, 24097, 24103, 24107, 24109,
  24113, 24121, 24133, 24137, 24151, 24169, 24179, 24181, 24197, 24203, 24223, 24229, 24239, 24247, 24251, 24281,
  24317, 24329, 24337, 24359, 24371, 24373, 24379, 24391, 24407, 24413, 24419, 24421, 24439, 24443, 24469, 24473,
  24481, 24499, 24509, 24517, 24527, 24533, 24547, 24551, 24571, 24593, 24611, 24623, 24631, 24659, 24671, 24677,
  24683, 24691, 24697, 24709, 24733, 24749, 24763, 24767, 24781, 24793, 24799, 24809, 24821, 24841, 24847, 24851,
  24859, 24877, 24889, 24907, 24917, 24919, 24923, 24943, 24953, 24967, 24971, 24977, 24979, 24989, 25013, 25031,
  25033, 25037, 25057, 25073, 25087, 25097, 25111, 25117, 25121, 25127, 25147, 25153, 25163, 25169, 25171, 25183,
  25189, 25219, 25229, 25237, 25243, 25247, 25253, 25261, 25301, 25303, 25307, 25309, 25321, 25339, 25343, 25349,
  25357, 25367, 25373, 25391, 25409, 25411, 25423, 25439, 25447, 25453, 25457, 25463, 25469, 25471, 25523, 25537,
  25541, 25561, 25577, 25579, 25583, 25589, 25601, 25603, 25609, 25621, 25633, 25639, 25643, 25657, 25667, 25673,
  25679, 25693, 25703, 25717, 25733, 25741, 25747, 25759, 25763, 25771, 25793, 25799, 25801, 25819, 25841, 25847,
  25849, 25867, 25873, 25889, 25903, 25913, 25919, 25931, 25933, 25939, 25943, 25951, 25969, 25981, 25997, 25999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock13 : List ℕ := [
  26003, 26017, 26021, 26029, 26041, 26053, 26083, 26099, 26107, 26111, 26113, 26119, 26141, 26153, 26161, 26171,
  26177, 26183, 26189, 26203, 26209, 26227, 26237, 26249, 26251, 26261, 26263, 26267, 26293, 26297, 26309, 26317,
  26321, 26339, 26347, 26357, 26371, 26387, 26393, 26399, 26407, 26417, 26423, 26431, 26437, 26449, 26459, 26479,
  26489, 26497, 26501, 26513, 26539, 26557, 26561, 26573, 26591, 26597, 26627, 26633, 26641, 26647, 26669, 26681,
  26683, 26687, 26693, 26699, 26701, 26711, 26713, 26717, 26723, 26729, 26731, 26737, 26759, 26777, 26783, 26801,
  26813, 26821, 26833, 26839, 26849, 26861, 26863, 26879, 26881, 26891, 26893, 26903, 26921, 26927, 26947, 26951,
  26953, 26959, 26981, 26987, 26993, 27011, 27017, 27031, 27043, 27059, 27061, 27067, 27073, 27077, 27091, 27103,
  27107, 27109, 27127, 27143, 27179, 27191, 27197, 27211, 27239, 27241, 27253, 27259, 27271, 27277, 27281, 27283,
  27299, 27329, 27337, 27361, 27367, 27397, 27407, 27409, 27427, 27431, 27437, 27449, 27457, 27479, 27481, 27487,
  27509, 27527, 27529, 27539, 27541, 27551, 27581, 27583, 27611, 27617, 27631, 27647, 27653, 27673, 27689, 27691,
  27697, 27701, 27733, 27737, 27739, 27743, 27749, 27751, 27763, 27767, 27773, 27779, 27791, 27793, 27799, 27803,
  27809, 27817, 27823, 27827, 27847, 27851, 27883, 27893, 27901, 27917, 27919, 27941, 27943, 27947, 27953, 27961,
  27967, 27983, 27997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock14 : List ℕ := [
  28001, 28019, 28027, 28031, 28051, 28057, 28069, 28081, 28087, 28097, 28099, 28109, 28111, 28123, 28151, 28163,
  28181, 28183, 28201, 28211, 28219, 28229, 28277, 28279, 28283, 28289, 28297, 28307, 28309, 28319, 28349, 28351,
  28387, 28393, 28403, 28409, 28411, 28429, 28433, 28439, 28447, 28463, 28477, 28493, 28499, 28513, 28517, 28537,
  28541, 28547, 28549, 28559, 28571, 28573, 28579, 28591, 28597, 28603, 28607, 28619, 28621, 28627, 28631, 28643,
  28649, 28657, 28661, 28663, 28669, 28687, 28697, 28703, 28711, 28723, 28729, 28751, 28753, 28759, 28771, 28789,
  28793, 28807, 28813, 28817, 28837, 28843, 28859, 28867, 28871, 28879, 28901, 28909, 28921, 28927, 28933, 28949,
  28961, 28979, 29009, 29017, 29021, 29023, 29027, 29033, 29059, 29063, 29077, 29101, 29123, 29129, 29131, 29137,
  29147, 29153, 29167, 29173, 29179, 29191, 29201, 29207, 29209, 29221, 29231, 29243, 29251, 29269, 29287, 29297,
  29303, 29311, 29327, 29333, 29339, 29347, 29363, 29383, 29387, 29389, 29399, 29401, 29411, 29423, 29429, 29437,
  29443, 29453, 29473, 29483, 29501, 29527, 29531, 29537, 29567, 29569, 29573, 29581, 29587, 29599, 29611, 29629,
  29633, 29641, 29663, 29669, 29671, 29683, 29717, 29723, 29741, 29753, 29759, 29761, 29789, 29803, 29819, 29833,
  29837, 29851, 29863, 29867, 29873, 29879, 29881, 29917, 29921, 29927, 29947, 29959, 29983, 29989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock15 : List ℕ := [
  30011, 30013, 30029, 30047, 30059, 30071, 30089, 30091, 30097, 30103, 30109, 30113, 30119, 30133, 30137, 30139,
  30161, 30169, 30181, 30187, 30197, 30203, 30211, 30223, 30241, 30253, 30259, 30269, 30271, 30293, 30307, 30313,
  30319, 30323, 30341, 30347, 30367, 30389, 30391, 30403, 30427, 30431, 30449, 30467, 30469, 30491, 30493, 30497,
  30509, 30517, 30529, 30539, 30553, 30557, 30559, 30577, 30593, 30631, 30637, 30643, 30649, 30661, 30671, 30677,
  30689, 30697, 30703, 30707, 30713, 30727, 30757, 30763, 30773, 30781, 30803, 30809, 30817, 30829, 30839, 30841,
  30851, 30853, 30859, 30869, 30871, 30881, 30893, 30911, 30931, 30937, 30941, 30949, 30971, 30977, 30983, 31013,
  31019, 31033, 31039, 31051, 31063, 31069, 31079, 31081, 31091, 31121, 31123, 31139, 31147, 31151, 31153, 31159,
  31177, 31181, 31183, 31189, 31193, 31219, 31223, 31231, 31237, 31247, 31249, 31253, 31259, 31267, 31271, 31277,
  31307, 31319, 31321, 31327, 31333, 31337, 31357, 31379, 31387, 31391, 31393, 31397, 31469, 31477, 31481, 31489,
  31511, 31513, 31517, 31531, 31541, 31543, 31547, 31567, 31573, 31583, 31601, 31607, 31627, 31643, 31649, 31657,
  31663, 31667, 31687, 31699, 31721, 31723, 31727, 31729, 31741, 31751, 31769, 31771, 31793, 31799, 31817, 31847,
  31849, 31859, 31873, 31883, 31891, 31907, 31957, 31963, 31973, 31981, 31991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock16 : List ℕ := [
  32003, 32009, 32027, 32029, 32051, 32057, 32059, 32063, 32069, 32077, 32083, 32089, 32099, 32117, 32119, 32141,
  32143, 32159, 32173, 32183, 32189, 32191, 32203, 32213, 32233, 32237, 32251, 32257, 32261, 32297, 32299, 32303,
  32309, 32321, 32323, 32327, 32341, 32353, 32359, 32363, 32369, 32371, 32377, 32381, 32401, 32411, 32413, 32423,
  32429, 32441, 32443, 32467, 32479, 32491, 32497, 32503, 32507, 32531, 32533, 32537, 32561, 32563, 32569, 32573,
  32579, 32587, 32603, 32609, 32611, 32621, 32633, 32647, 32653, 32687, 32693, 32707, 32713, 32717, 32719, 32749,
  32771, 32779, 32783, 32789, 32797, 32801, 32803, 32831, 32833, 32839, 32843, 32869, 32887, 32909, 32911, 32917,
  32933, 32939, 32941, 32957, 32969, 32971, 32983, 32987, 32993, 32999, 33013, 33023, 33029, 33037, 33049, 33053,
  33071, 33073, 33083, 33091, 33107, 33113, 33119, 33149, 33151, 33161, 33179, 33181, 33191, 33199, 33203, 33211,
  33223, 33247, 33287, 33289, 33301, 33311, 33317, 33329, 33331, 33343, 33347, 33349, 33353, 33359, 33377, 33391,
  33403, 33409, 33413, 33427, 33457, 33461, 33469, 33479, 33487, 33493, 33503, 33521, 33529, 33533, 33547, 33563,
  33569, 33577, 33581, 33587, 33589, 33599, 33601, 33613, 33617, 33619, 33623, 33629, 33637, 33641, 33647, 33679,
  33703, 33713, 33721, 33739, 33749, 33751, 33757, 33767, 33769, 33773, 33791, 33797, 33809, 33811, 33827, 33829,
  33851, 33857, 33863, 33871, 33889, 33893, 33911, 33923, 33931, 33937, 33941, 33961, 33967, 33997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock17 : List ℕ := [
  34019, 34031, 34033, 34039, 34057, 34061, 34123, 34127, 34129, 34141, 34147, 34157, 34159, 34171, 34183, 34211,
  34213, 34217, 34231, 34253, 34259, 34261, 34267, 34273, 34283, 34297, 34301, 34303, 34313, 34319, 34327, 34337,
  34351, 34361, 34367, 34369, 34381, 34403, 34421, 34429, 34439, 34457, 34469, 34471, 34483, 34487, 34499, 34501,
  34511, 34513, 34519, 34537, 34543, 34549, 34583, 34589, 34591, 34603, 34607, 34613, 34631, 34649, 34651, 34667,
  34673, 34679, 34687, 34693, 34703, 34721, 34729, 34739, 34747, 34757, 34759, 34763, 34781, 34807, 34819, 34841,
  34843, 34847, 34849, 34871, 34877, 34883, 34897, 34913, 34919, 34939, 34949, 34961, 34963, 34981, 35023, 35027,
  35051, 35053, 35059, 35069, 35081, 35083, 35089, 35099, 35107, 35111, 35117, 35129, 35141, 35149, 35153, 35159,
  35171, 35201, 35221, 35227, 35251, 35257, 35267, 35279, 35281, 35291, 35311, 35317, 35323, 35327, 35339, 35353,
  35363, 35381, 35393, 35401, 35407, 35419, 35423, 35437, 35447, 35449, 35461, 35491, 35507, 35509, 35521, 35527,
  35531, 35533, 35537, 35543, 35569, 35573, 35591, 35593, 35597, 35603, 35617, 35671, 35677, 35729, 35731, 35747,
  35753, 35759, 35771, 35797, 35801, 35803, 35809, 35831, 35837, 35839, 35851, 35863, 35869, 35879, 35897, 35899,
  35911, 35923, 35933, 35951, 35963, 35969, 35977, 35983, 35993, 35999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock18 : List ℕ := [
  36007, 36011, 36013, 36017, 36037, 36061, 36067, 36073, 36083, 36097, 36107, 36109, 36131, 36137, 36151, 36161,
  36187, 36191, 36209, 36217, 36229, 36241, 36251, 36263, 36269, 36277, 36293, 36299, 36307, 36313, 36319, 36341,
  36343, 36353, 36373, 36383, 36389, 36433, 36451, 36457, 36467, 36469, 36473, 36479, 36493, 36497, 36523, 36527,
  36529, 36541, 36551, 36559, 36563, 36571, 36583, 36587, 36599, 36607, 36629, 36637, 36643, 36653, 36671, 36677,
  36683, 36691, 36697, 36709, 36713, 36721, 36739, 36749, 36761, 36767, 36779, 36781, 36787, 36791, 36793, 36809,
  36821, 36833, 36847, 36857, 36871, 36877, 36887, 36899, 36901, 36913, 36919, 36923, 36929, 36931, 36943, 36947,
  36973, 36979, 36997, 37003, 37013, 37019, 37021, 37039, 37049, 37057, 37061, 37087, 37097, 37117, 37123, 37139,
  37159, 37171, 37181, 37189, 37199, 37201, 37217, 37223, 37243, 37253, 37273, 37277, 37307, 37309, 37313, 37321,
  37337, 37339, 37357, 37361, 37363, 37369, 37379, 37397, 37409, 37423, 37441, 37447, 37463, 37483, 37489, 37493,
  37501, 37507, 37511, 37517, 37529, 37537, 37547, 37549, 37561, 37567, 37571, 37573, 37579, 37589, 37591, 37607,
  37619, 37633, 37643, 37649, 37657, 37663, 37691, 37693, 37699, 37717, 37747, 37781, 37783, 37799, 37811, 37813,
  37831, 37847, 37853, 37861, 37871, 37879, 37889, 37897, 37907, 37951, 37957, 37963, 37967, 37987, 37991, 37993,
  37997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock19 : List ℕ := [
  38011, 38039, 38047, 38053, 38069, 38083, 38113, 38119, 38149, 38153, 38167, 38177, 38183, 38189, 38197, 38201,
  38219, 38231, 38237, 38239, 38261, 38273, 38281, 38287, 38299, 38303, 38317, 38321, 38327, 38329, 38333, 38351,
  38371, 38377, 38393, 38431, 38447, 38449, 38453, 38459, 38461, 38501, 38543, 38557, 38561, 38567, 38569, 38593,
  38603, 38609, 38611, 38629, 38639, 38651, 38653, 38669, 38671, 38677, 38693, 38699, 38707, 38711, 38713, 38723,
  38729, 38737, 38747, 38749, 38767, 38783, 38791, 38803, 38821, 38833, 38839, 38851, 38861, 38867, 38873, 38891,
  38903, 38917, 38921, 38923, 38933, 38953, 38959, 38971, 38977, 38993, 39019, 39023, 39041, 39043, 39047, 39079,
  39089, 39097, 39103, 39107, 39113, 39119, 39133, 39139, 39157, 39161, 39163, 39181, 39191, 39199, 39209, 39217,
  39227, 39229, 39233, 39239, 39241, 39251, 39293, 39301, 39313, 39317, 39323, 39341, 39343, 39359, 39367, 39371,
  39373, 39383, 39397, 39409, 39419, 39439, 39443, 39451, 39461, 39499, 39503, 39509, 39511, 39521, 39541, 39551,
  39563, 39569, 39581, 39607, 39619, 39623, 39631, 39659, 39667, 39671, 39679, 39703, 39709, 39719, 39727, 39733,
  39749, 39761, 39769, 39779, 39791, 39799, 39821, 39827, 39829, 39839, 39841, 39847, 39857, 39863, 39869, 39877,
  39883, 39887, 39901, 39929, 39937, 39953, 39971, 39979, 39983, 39989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock20 : List ℕ := [
  40009, 40013, 40031, 40037, 40039, 40063, 40087, 40093, 40099, 40111, 40123, 40127, 40129, 40151, 40153, 40163,
  40169, 40177, 40189, 40193, 40213, 40231, 40237, 40241, 40253, 40277, 40283, 40289, 40343, 40351, 40357, 40361,
  40387, 40423, 40427, 40429, 40433, 40459, 40471, 40483, 40487, 40493, 40499, 40507, 40519, 40529, 40531, 40543,
  40559, 40577, 40583, 40591, 40597, 40609, 40627, 40637, 40639, 40693, 40697, 40699, 40709, 40739, 40751, 40759,
  40763, 40771, 40787, 40801, 40813, 40819, 40823, 40829, 40841, 40847, 40849, 40853, 40867, 40879, 40883, 40897,
  40903, 40927, 40933, 40939, 40949, 40961, 40973, 40993, 41011, 41017, 41023, 41039, 41047, 41051, 41057, 41077,
  41081, 41113, 41117, 41131, 41141, 41143, 41149, 41161, 41177, 41179, 41183, 41189, 41201, 41203, 41213, 41221,
  41227, 41231, 41233, 41243, 41257, 41263, 41269, 41281, 41299, 41333, 41341, 41351, 41357, 41381, 41387, 41389,
  41399, 41411, 41413, 41443, 41453, 41467, 41479, 41491, 41507, 41513, 41519, 41521, 41539, 41543, 41549, 41579,
  41593, 41597, 41603, 41609, 41611, 41617, 41621, 41627, 41641, 41647, 41651, 41659, 41669, 41681, 41687, 41719,
  41729, 41737, 41759, 41761, 41771, 41777, 41801, 41809, 41813, 41843, 41849, 41851, 41863, 41879, 41887, 41893,
  41897, 41903, 41911, 41927, 41941, 41947, 41953, 41957, 41959, 41969, 41981, 41983, 41999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock21 : List ℕ := [
  42013, 42017, 42019, 42023, 42043, 42061, 42071, 42073, 42083, 42089, 42101, 42131, 42139, 42157, 42169, 42179,
  42181, 42187, 42193, 42197, 42209, 42221, 42223, 42227, 42239, 42257, 42281, 42283, 42293, 42299, 42307, 42323,
  42331, 42337, 42349, 42359, 42373, 42379, 42391, 42397, 42403, 42407, 42409, 42433, 42437, 42443, 42451, 42457,
  42461, 42463, 42467, 42473, 42487, 42491, 42499, 42509, 42533, 42557, 42569, 42571, 42577, 42589, 42611, 42641,
  42643, 42649, 42667, 42677, 42683, 42689, 42697, 42701, 42703, 42709, 42719, 42727, 42737, 42743, 42751, 42767,
  42773, 42787, 42793, 42797, 42821, 42829, 42839, 42841, 42853, 42859, 42863, 42899, 42901, 42923, 42929, 42937,
  42943, 42953, 42961, 42967, 42979, 42989, 43003, 43013, 43019, 43037, 43049, 43051, 43063, 43067, 43093, 43103,
  43117, 43133, 43151, 43159, 43177, 43189, 43201, 43207, 43223, 43237, 43261, 43271, 43283, 43291, 43313, 43319,
  43321, 43331, 43391, 43397, 43399, 43403, 43411, 43427, 43441, 43451, 43457, 43481, 43487, 43499, 43517, 43541,
  43543, 43573, 43577, 43579, 43591, 43597, 43607, 43609, 43613, 43627, 43633, 43649, 43651, 43661, 43669, 43691,
  43711, 43717, 43721, 43753, 43759, 43777, 43781, 43783, 43787, 43789, 43793, 43801, 43853, 43867, 43889, 43891,
  43913, 43933, 43943, 43951, 43961, 43963, 43969, 43973, 43987, 43991, 43997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock22 : List ℕ := [
  44017, 44021, 44027, 44029, 44041, 44053, 44059, 44071, 44087, 44089, 44101, 44111, 44119, 44123, 44129, 44131,
  44159, 44171, 44179, 44189, 44201, 44203, 44207, 44221, 44249, 44257, 44263, 44267, 44269, 44273, 44279, 44281,
  44293, 44351, 44357, 44371, 44381, 44383, 44389, 44417, 44449, 44453, 44483, 44491, 44497, 44501, 44507, 44519,
  44531, 44533, 44537, 44543, 44549, 44563, 44579, 44587, 44617, 44621, 44623, 44633, 44641, 44647, 44651, 44657,
  44683, 44687, 44699, 44701, 44711, 44729, 44741, 44753, 44771, 44773, 44777, 44789, 44797, 44809, 44819, 44839,
  44843, 44851, 44867, 44879, 44887, 44893, 44909, 44917, 44927, 44939, 44953, 44959, 44963, 44971, 44983, 44987,
  45007, 45013, 45053, 45061, 45077, 45083, 45119, 45121, 45127, 45131, 45137, 45139, 45161, 45179, 45181, 45191,
  45197, 45233, 45247, 45259, 45263, 45281, 45289, 45293, 45307, 45317, 45319, 45329, 45337, 45341, 45343, 45361,
  45377, 45389, 45403, 45413, 45427, 45433, 45439, 45481, 45491, 45497, 45503, 45523, 45533, 45541, 45553, 45557,
  45569, 45587, 45589, 45599, 45613, 45631, 45641, 45659, 45667, 45673, 45677, 45691, 45697, 45707, 45737, 45751,
  45757, 45763, 45767, 45779, 45817, 45821, 45823, 45827, 45833, 45841, 45853, 45863, 45869, 45887, 45893, 45943,
  45949, 45953, 45959, 45971, 45979, 45989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock23 : List ℕ := [
  46021, 46027, 46049, 46051, 46061, 46073, 46091, 46093, 46099, 46103, 46133, 46141, 46147, 46153, 46171, 46181,
  46183, 46187, 46199, 46219, 46229, 46237, 46261, 46271, 46273, 46279, 46301, 46307, 46309, 46327, 46337, 46349,
  46351, 46381, 46399, 46411, 46439, 46441, 46447, 46451, 46457, 46471, 46477, 46489, 46499, 46507, 46511, 46523,
  46549, 46559, 46567, 46573, 46589, 46591, 46601, 46619, 46633, 46639, 46643, 46649, 46663, 46679, 46681, 46687,
  46691, 46703, 46723, 46727, 46747, 46751, 46757, 46769, 46771, 46807, 46811, 46817, 46819, 46829, 46831, 46853,
  46861, 46867, 46877, 46889, 46901, 46919, 46933, 46957, 46993, 46997, 47017, 47041, 47051, 47057, 47059, 47087,
  47093, 47111, 47119, 47123, 47129, 47137, 47143, 47147, 47149, 47161, 47189, 47207, 47221, 47237, 47251, 47269,
  47279, 47287, 47293, 47297, 47303, 47309, 47317, 47339, 47351, 47353, 47363, 47381, 47387, 47389, 47407, 47417,
  47419, 47431, 47441, 47459, 47491, 47497, 47501, 47507, 47513, 47521, 47527, 47533, 47543, 47563, 47569, 47581,
  47591, 47599, 47609, 47623, 47629, 47639, 47653, 47657, 47659, 47681, 47699, 47701, 47711, 47713, 47717, 47737,
  47741, 47743, 47777, 47779, 47791, 47797, 47807, 47809, 47819, 47837, 47843, 47857, 47869, 47881, 47903, 47911,
  47917, 47933, 47939, 47947, 47951, 47963, 47969, 47977, 47981
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock24 : List ℕ := [
  48017, 48023, 48029, 48049, 48073, 48079, 48091, 48109, 48119, 48121, 48131, 48157, 48163, 48179, 48187, 48193,
  48197, 48221, 48239, 48247, 48259, 48271, 48281, 48299, 48311, 48313, 48337, 48341, 48353, 48371, 48383, 48397,
  48407, 48409, 48413, 48437, 48449, 48463, 48473, 48479, 48481, 48487, 48491, 48497, 48523, 48527, 48533, 48539,
  48541, 48563, 48571, 48589, 48593, 48611, 48619, 48623, 48647, 48649, 48661, 48673, 48677, 48679, 48731, 48733,
  48751, 48757, 48761, 48767, 48779, 48781, 48787, 48799, 48809, 48817, 48821, 48823, 48847, 48857, 48859, 48869,
  48871, 48883, 48889, 48907, 48947, 48953, 48973, 48989, 48991, 49003, 49009, 49019, 49031, 49033, 49037, 49043,
  49057, 49069, 49081, 49103, 49109, 49117, 49121, 49123, 49139, 49157, 49169, 49171, 49177, 49193, 49199, 49201,
  49207, 49211, 49223, 49253, 49261, 49277, 49279, 49297, 49307, 49331, 49333, 49339, 49363, 49367, 49369, 49391,
  49393, 49409, 49411, 49417, 49429, 49433, 49451, 49459, 49463, 49477, 49481, 49499, 49523, 49529, 49531, 49537,
  49547, 49549, 49559, 49597, 49603, 49613, 49627, 49633, 49639, 49663, 49667, 49669, 49681, 49697, 49711, 49727,
  49739, 49741, 49747, 49757, 49783, 49787, 49789, 49801, 49807, 49811, 49823, 49831, 49843, 49853, 49871, 49877,
  49891, 49919, 49921, 49927, 49937, 49939, 49943, 49957, 49991, 49993, 49999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock25 : List ℕ := [
  50021, 50023, 50033, 50047, 50051, 50053, 50069, 50077, 50087, 50093, 50101, 50111, 50119, 50123, 50129, 50131,
  50147, 50153, 50159, 50177, 50207, 50221, 50227, 50231, 50261, 50263, 50273, 50287, 50291, 50311, 50321, 50329,
  50333, 50341, 50359, 50363, 50377, 50383, 50387, 50411, 50417, 50423, 50441, 50459, 50461, 50497, 50503, 50513,
  50527, 50539, 50543, 50549, 50551, 50581, 50587, 50591, 50593, 50599, 50627, 50647, 50651, 50671, 50683, 50707,
  50723, 50741, 50753, 50767, 50773, 50777, 50789, 50821, 50833, 50839, 50849, 50857, 50867, 50873, 50891, 50893,
  50909, 50923, 50929, 50951, 50957, 50969, 50971, 50989, 50993, 51001, 51031, 51043, 51047, 51059, 51061, 51071,
  51109, 51131, 51133, 51137, 51151, 51157, 51169, 51193, 51197, 51199, 51203, 51217, 51229, 51239, 51241, 51257,
  51263, 51283, 51287, 51307, 51329, 51341, 51343, 51347, 51349, 51361, 51383, 51407, 51413, 51419, 51421, 51427,
  51431, 51437, 51439, 51449, 51461, 51473, 51479, 51481, 51487, 51503, 51511, 51517, 51521, 51539, 51551, 51563,
  51577, 51581, 51593, 51599, 51607, 51613, 51631, 51637, 51647, 51659, 51673, 51679, 51683, 51691, 51713, 51719,
  51721, 51749, 51767, 51769, 51787, 51797, 51803, 51817, 51827, 51829, 51839, 51853, 51859, 51869, 51871, 51893,
  51899, 51907, 51913, 51929, 51941, 51949, 51971, 51973, 51977, 51991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock26 : List ℕ := [
  52009, 52021, 52027, 52051, 52057, 52067, 52069, 52081, 52103, 52121, 52127, 52147, 52153, 52163, 52177, 52181,
  52183, 52189, 52201, 52223, 52237, 52249, 52253, 52259, 52267, 52289, 52291, 52301, 52313, 52321, 52361, 52363,
  52369, 52379, 52387, 52391, 52433, 52453, 52457, 52489, 52501, 52511, 52517, 52529, 52541, 52543, 52553, 52561,
  52567, 52571, 52579, 52583, 52609, 52627, 52631, 52639, 52667, 52673, 52691, 52697, 52709, 52711, 52721, 52727,
  52733, 52747, 52757, 52769, 52783, 52807, 52813, 52817, 52837, 52859, 52861, 52879, 52883, 52889, 52901, 52903,
  52919, 52937, 52951, 52957, 52963, 52967, 52973, 52981, 52999, 53003, 53017, 53047, 53051, 53069, 53077, 53087,
  53089, 53093, 53101, 53113, 53117, 53129, 53147, 53149, 53161, 53171, 53173, 53189, 53197, 53201, 53231, 53233,
  53239, 53267, 53269, 53279, 53281, 53299, 53309, 53323, 53327, 53353, 53359, 53377, 53381, 53401, 53407, 53411,
  53419, 53437, 53441, 53453, 53479, 53503, 53507, 53527, 53549, 53551, 53569, 53591, 53593, 53597, 53609, 53611,
  53617, 53623, 53629, 53633, 53639, 53653, 53657, 53681, 53693, 53699, 53717, 53719, 53731, 53759, 53773, 53777,
  53783, 53791, 53813, 53819, 53831, 53849, 53857, 53861, 53881, 53887, 53891, 53897, 53899, 53917, 53923, 53927,
  53939, 53951, 53959, 53987, 53993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock27 : List ℕ := [
  54001, 54011, 54013, 54037, 54049, 54059, 54083, 54091, 54101, 54121, 54133, 54139, 54151, 54163, 54167, 54181,
  54193, 54217, 54251, 54269, 54277, 54287, 54293, 54311, 54319, 54323, 54331, 54347, 54361, 54367, 54371, 54377,
  54401, 54403, 54409, 54413, 54419, 54421, 54437, 54443, 54449, 54469, 54493, 54497, 54499, 54503, 54517, 54521,
  54539, 54541, 54547, 54559, 54563, 54577, 54581, 54583, 54601, 54617, 54623, 54629, 54631, 54647, 54667, 54673,
  54679, 54709, 54713, 54721, 54727, 54751, 54767, 54773, 54779, 54787, 54799, 54829, 54833, 54851, 54869, 54877,
  54881, 54907, 54917, 54919, 54941, 54949, 54959, 54973, 54979, 54983, 55001, 55009, 55021, 55049, 55051, 55057,
  55061, 55073, 55079, 55103, 55109, 55117, 55127, 55147, 55163, 55171, 55201, 55207, 55213, 55217, 55219, 55229,
  55243, 55249, 55259, 55291, 55313, 55331, 55333, 55337, 55339, 55343, 55351, 55373, 55381, 55399, 55411, 55439,
  55441, 55457, 55469, 55487, 55501, 55511, 55529, 55541, 55547, 55579, 55589, 55603, 55609, 55619, 55621, 55631,
  55633, 55639, 55661, 55663, 55667, 55673, 55681, 55691, 55697, 55711, 55717, 55721, 55733, 55763, 55787, 55793,
  55799, 55807, 55813, 55817, 55819, 55823, 55829, 55837, 55843, 55849, 55871, 55889, 55897, 55901, 55903, 55921,
  55927, 55931, 55933, 55949, 55967, 55987, 55997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock28 : List ℕ := [
  56003, 56009, 56039, 56041, 56053, 56081, 56087, 56093, 56099, 56101, 56113, 56123, 56131, 56149, 56167, 56171,
  56179, 56197, 56207, 56209, 56237, 56239, 56249, 56263, 56267, 56269, 56299, 56311, 56333, 56359, 56369, 56377,
  56383, 56393, 56401, 56417, 56431, 56437, 56443, 56453, 56467, 56473, 56477, 56479, 56489, 56501, 56503, 56509,
  56519, 56527, 56531, 56533, 56543, 56569, 56591, 56597, 56599, 56611, 56629, 56633, 56659, 56663, 56671, 56681,
  56687, 56701, 56711, 56713, 56731, 56737, 56747, 56767, 56773, 56779, 56783, 56807, 56809, 56813, 56821, 56827,
  56843, 56857, 56873, 56891, 56893, 56897, 56909, 56911, 56921, 56923, 56929, 56941, 56951, 56957, 56963, 56983,
  56989, 56993, 56999, 57037, 57041, 57047, 57059, 57073, 57077, 57089, 57097, 57107, 57119, 57131, 57139, 57143,
  57149, 57163, 57173, 57179, 57191, 57193, 57203, 57221, 57223, 57241, 57251, 57259, 57269, 57271, 57283, 57287,
  57301, 57329, 57331, 57347, 57349, 57367, 57373, 57383, 57389, 57397, 57413, 57427, 57457, 57467, 57487, 57493,
  57503, 57527, 57529, 57557, 57559, 57571, 57587, 57593, 57601, 57637, 57641, 57649, 57653, 57667, 57679, 57689,
  57697, 57709, 57713, 57719, 57727, 57731, 57737, 57751, 57773, 57781, 57787, 57791, 57793, 57803, 57809, 57829,
  57839, 57847, 57853, 57859, 57881, 57899, 57901, 57917, 57923, 57943, 57947, 57973, 57977, 57991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock29 : List ℕ := [
  58013, 58027, 58031, 58043, 58049, 58057, 58061, 58067, 58073, 58099, 58109, 58111, 58129, 58147, 58151, 58153,
  58169, 58171, 58189, 58193, 58199, 58207, 58211, 58217, 58229, 58231, 58237, 58243, 58271, 58309, 58313, 58321,
  58337, 58363, 58367, 58369, 58379, 58391, 58393, 58403, 58411, 58417, 58427, 58439, 58441, 58451, 58453, 58477,
  58481, 58511, 58537, 58543, 58549, 58567, 58573, 58579, 58601, 58603, 58613, 58631, 58657, 58661, 58679, 58687,
  58693, 58699, 58711, 58727, 58733, 58741, 58757, 58763, 58771, 58787, 58789, 58831, 58889, 58897, 58901, 58907,
  58909, 58913, 58921, 58937, 58943, 58963, 58967, 58979, 58991, 58997, 59009, 59011, 59021, 59023, 59029, 59051,
  59053, 59063, 59069, 59077, 59083, 59093, 59107, 59113, 59119, 59123, 59141, 59149, 59159, 59167, 59183, 59197,
  59207, 59209, 59219, 59221, 59233, 59239, 59243, 59263, 59273, 59281, 59333, 59341, 59351, 59357, 59359, 59369,
  59377, 59387, 59393, 59399, 59407, 59417, 59419, 59441, 59443, 59447, 59453, 59467, 59471, 59473, 59497, 59509,
  59513, 59539, 59557, 59561, 59567, 59581, 59611, 59617, 59621, 59627, 59629, 59651, 59659, 59663, 59669, 59671,
  59693, 59699, 59707, 59723, 59729, 59743, 59747, 59753, 59771, 59779, 59791, 59797, 59809, 59833, 59863, 59879,
  59887, 59921, 59929, 59951, 59957, 59971, 59981, 59999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock30 : List ℕ := [
  60013, 60017, 60029, 60037, 60041, 60077, 60083, 60089, 60091, 60101, 60103, 60107, 60127, 60133, 60139, 60149,
  60161, 60167, 60169, 60209, 60217, 60223, 60251, 60257, 60259, 60271, 60289, 60293, 60317, 60331, 60337, 60343,
  60353, 60373, 60383, 60397, 60413, 60427, 60443, 60449, 60457, 60493, 60497, 60509, 60521, 60527, 60539, 60589,
  60601, 60607, 60611, 60617, 60623, 60631, 60637, 60647, 60649, 60659, 60661, 60679, 60689, 60703, 60719, 60727,
  60733, 60737, 60757, 60761, 60763, 60773, 60779, 60793, 60811, 60821, 60859, 60869, 60887, 60889, 60899, 60901,
  60913, 60917, 60919, 60923, 60937, 60943, 60953, 60961, 61001, 61007, 61027, 61031, 61043, 61051, 61057, 61091,
  61099, 61121, 61129, 61141, 61151, 61153, 61169, 61211, 61223, 61231, 61253, 61261, 61283, 61291, 61297, 61331,
  61333, 61339, 61343, 61357, 61363, 61379, 61381, 61403, 61409, 61417, 61441, 61463, 61469, 61471, 61483, 61487,
  61493, 61507, 61511, 61519, 61543, 61547, 61553, 61559, 61561, 61583, 61603, 61609, 61613, 61627, 61631, 61637,
  61643, 61651, 61657, 61667, 61673, 61681, 61687, 61703, 61717, 61723, 61729, 61751, 61757, 61781, 61813, 61819,
  61837, 61843, 61861, 61871, 61879, 61909, 61927, 61933, 61949, 61961, 61967, 61979, 61981, 61987, 61991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock31 : List ℕ := [
  62003, 62011, 62017, 62039, 62047, 62053, 62057, 62071, 62081, 62099, 62119, 62129, 62131, 62137, 62141, 62143,
  62171, 62189, 62191, 62201, 62207, 62213, 62219, 62233, 62273, 62297, 62299, 62303, 62311, 62323, 62327, 62347,
  62351, 62383, 62401, 62417, 62423, 62459, 62467, 62473, 62477, 62483, 62497, 62501, 62507, 62533, 62539, 62549,
  62563, 62581, 62591, 62597, 62603, 62617, 62627, 62633, 62639, 62653, 62659, 62683, 62687, 62701, 62723, 62731,
  62743, 62753, 62761, 62773, 62791, 62801, 62819, 62827, 62851, 62861, 62869, 62873, 62897, 62903, 62921, 62927,
  62929, 62939, 62969, 62971, 62981, 62983, 62987, 62989, 63029, 63031, 63059, 63067, 63073, 63079, 63097, 63103,
  63113, 63127, 63131, 63149, 63179, 63197, 63199, 63211, 63241, 63247, 63277, 63281, 63299, 63311, 63313, 63317,
  63331, 63337, 63347, 63353, 63361, 63367, 63377, 63389, 63391, 63397, 63409, 63419, 63421, 63439, 63443, 63463,
  63467, 63473, 63487, 63493, 63499, 63521, 63527, 63533, 63541, 63559, 63577, 63587, 63589, 63599, 63601, 63607,
  63611, 63617, 63629, 63647, 63649, 63659, 63667, 63671, 63689, 63691, 63697, 63703, 63709, 63719, 63727, 63737,
  63743, 63761, 63773, 63781, 63793, 63799, 63803, 63809, 63823, 63839, 63841, 63853, 63857, 63863, 63901, 63907,
  63913, 63929, 63949, 63977, 63997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock32 : List ℕ := [
  64007, 64013, 64019, 64033, 64037, 64063, 64067, 64081, 64091, 64109, 64123, 64151, 64153, 64157, 64171, 64187,
  64189, 64217, 64223, 64231, 64237, 64271, 64279, 64283, 64301, 64303, 64319, 64327, 64333, 64373, 64381, 64399,
  64403, 64433, 64439, 64451, 64453, 64483, 64489, 64499, 64513, 64553, 64567, 64577, 64579, 64591, 64601, 64609,
  64613, 64621, 64627, 64633, 64661, 64663, 64667, 64679, 64693, 64709, 64717, 64747, 64763, 64781, 64783, 64793,
  64811, 64817, 64849, 64853, 64871, 64877, 64879, 64891, 64901, 64919, 64921, 64927, 64937, 64951, 64969, 64997,
  65003, 65011, 65027, 65029, 65033, 65053, 65063, 65071, 65089, 65099, 65101, 65111, 65119, 65123, 65129, 65141,
  65147, 65167, 65171, 65173, 65179, 65183, 65203, 65213, 65239, 65257, 65267, 65269, 65287, 65293, 65309, 65323,
  65327, 65353, 65357, 65371, 65381, 65393, 65407, 65413, 65419, 65423, 65437, 65447, 65449, 65479, 65497, 65519,
  65521, 65537, 65539, 65543, 65551, 65557, 65563, 65579, 65581, 65587, 65599, 65609, 65617, 65629, 65633, 65647,
  65651, 65657, 65677, 65687, 65699, 65701, 65707, 65713, 65717, 65719, 65729, 65731, 65761, 65777, 65789, 65809,
  65827, 65831, 65837, 65839, 65843, 65851, 65867, 65881, 65899, 65921, 65927, 65929, 65951, 65957, 65963, 65981,
  65983, 65993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock33 : List ℕ := [
  66029, 66037, 66041, 66047, 66067, 66071, 66083, 66089, 66103, 66107, 66109, 66137, 66161, 66169, 66173, 66179,
  66191, 66221, 66239, 66271, 66293, 66301, 66337, 66343, 66347, 66359, 66361, 66373, 66377, 66383, 66403, 66413,
  66431, 66449, 66457, 66463, 66467, 66491, 66499, 66509, 66523, 66529, 66533, 66541, 66553, 66569, 66571, 66587,
  66593, 66601, 66617, 66629, 66643, 66653, 66683, 66697, 66701, 66713, 66721, 66733, 66739, 66749, 66751, 66763,
  66791, 66797, 66809, 66821, 66841, 66851, 66853, 66863, 66877, 66883, 66889, 66919, 66923, 66931, 66943, 66947,
  66949, 66959, 66973, 66977, 67003, 67021, 67033, 67043, 67049, 67057, 67061, 67073, 67079, 67103, 67121, 67129,
  67139, 67141, 67153, 67157, 67169, 67181, 67187, 67189, 67211, 67213, 67217, 67219, 67231, 67247, 67261, 67271,
  67273, 67289, 67307, 67339, 67343, 67349, 67369, 67391, 67399, 67409, 67411, 67421, 67427, 67429, 67433, 67447,
  67453, 67477, 67481, 67489, 67493, 67499, 67511, 67523, 67531, 67537, 67547, 67559, 67567, 67577, 67579, 67589,
  67601, 67607, 67619, 67631, 67651, 67679, 67699, 67709, 67723, 67733, 67741, 67751, 67757, 67759, 67763, 67777,
  67783, 67789, 67801, 67807, 67819, 67829, 67843, 67853, 67867, 67883, 67891, 67901, 67927, 67931, 67933, 67939,
  67943, 67957, 67961, 67967, 67979, 67987, 67993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock34 : List ℕ := [
  68023, 68041, 68053, 68059, 68071, 68087, 68099, 68111, 68113, 68141, 68147, 68161, 68171, 68207, 68209, 68213,
  68219, 68227, 68239, 68261, 68279, 68281, 68311, 68329, 68351, 68371, 68389, 68399, 68437, 68443, 68447, 68449,
  68473, 68477, 68483, 68489, 68491, 68501, 68507, 68521, 68531, 68539, 68543, 68567, 68581, 68597, 68611, 68633,
  68639, 68659, 68669, 68683, 68687, 68699, 68711, 68713, 68729, 68737, 68743, 68749, 68767, 68771, 68777, 68791,
  68813, 68819, 68821, 68863, 68879, 68881, 68891, 68897, 68899, 68903, 68909, 68917, 68927, 68947, 68963, 68993,
  69001, 69011, 69019, 69029, 69031, 69061, 69067, 69073, 69109, 69119, 69127, 69143, 69149, 69151, 69163, 69191,
  69193, 69197, 69203, 69221, 69233, 69239, 69247, 69257, 69259, 69263, 69313, 69317, 69337, 69341, 69371, 69379,
  69383, 69389, 69401, 69403, 69427, 69431, 69439, 69457, 69463, 69467, 69473, 69481, 69491, 69493, 69497, 69499,
  69539, 69557, 69593, 69623, 69653, 69661, 69677, 69691, 69697, 69709, 69737, 69739, 69761, 69763, 69767, 69779,
  69809, 69821, 69827, 69829, 69833, 69847, 69857, 69859, 69877, 69899, 69911, 69929, 69931, 69941, 69959, 69991,
  69997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock35 : List ℕ := [
  70001, 70003, 70009, 70019, 70039, 70051, 70061, 70067, 70079, 70099, 70111, 70117, 70121, 70123, 70139, 70141,
  70157, 70163, 70177, 70181, 70183, 70199, 70201, 70207, 70223, 70229, 70237, 70241, 70249, 70271, 70289, 70297,
  70309, 70313, 70321, 70327, 70351, 70373, 70379, 70381, 70393, 70423, 70429, 70439, 70451, 70457, 70459, 70481,
  70487, 70489, 70501, 70507, 70529, 70537, 70549, 70571, 70573, 70583, 70589, 70607, 70619, 70621, 70627, 70639,
  70657, 70663, 70667, 70687, 70709, 70717, 70729, 70753, 70769, 70783, 70793, 70823, 70841, 70843, 70849, 70853,
  70867, 70877, 70879, 70891, 70901, 70913, 70919, 70921, 70937, 70949, 70951, 70957, 70969, 70979, 70981, 70991,
  70997, 70999, 71011, 71023, 71039, 71059, 71069, 71081, 71089, 71119, 71129, 71143, 71147, 71153, 71161, 71167,
  71171, 71191, 71209, 71233, 71237, 71249, 71257, 71261, 71263, 71287, 71293, 71317, 71327, 71329, 71333, 71339,
  71341, 71347, 71353, 71359, 71363, 71387, 71389, 71399, 71411, 71413, 71419, 71429, 71437, 71443, 71453, 71471,
  71473, 71479, 71483, 71503, 71527, 71537, 71549, 71551, 71563, 71569, 71593, 71597, 71633, 71647, 71663, 71671,
  71693, 71699, 71707, 71711, 71713, 71719, 71741, 71761, 71777, 71789, 71807, 71809, 71821, 71837, 71843, 71849,
  71861, 71867, 71879, 71881, 71887, 71899, 71909, 71917, 71933, 71941, 71947, 71963, 71971, 71983, 71987, 71993,
  71999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock36 : List ℕ := [
  72019, 72031, 72043, 72047, 72053, 72073, 72077, 72089, 72091, 72101, 72103, 72109, 72139, 72161, 72167, 72169,
  72173, 72211, 72221, 72223, 72227, 72229, 72251, 72253, 72269, 72271, 72277, 72287, 72307, 72313, 72337, 72341,
  72353, 72367, 72379, 72383, 72421, 72431, 72461, 72467, 72469, 72481, 72493, 72497, 72503, 72533, 72547, 72551,
  72559, 72577, 72613, 72617, 72623, 72643, 72647, 72649, 72661, 72671, 72673, 72679, 72689, 72701, 72707, 72719,
  72727, 72733, 72739, 72763, 72767, 72797, 72817, 72823, 72859, 72869, 72871, 72883, 72889, 72893, 72901, 72907,
  72911, 72923, 72931, 72937, 72949, 72953, 72959, 72973, 72977, 72997, 73009, 73013, 73019, 73037, 73039, 73043,
  73061, 73063, 73079, 73091, 73121, 73127, 73133, 73141, 73181, 73189, 73237, 73243, 73259, 73277, 73291, 73303,
  73309, 73327, 73331, 73351, 73361, 73363, 73369, 73379, 73387, 73417, 73421, 73433, 73453, 73459, 73471, 73477,
  73483, 73517, 73523, 73529, 73547, 73553, 73561, 73571, 73583, 73589, 73597, 73607, 73609, 73613, 73637, 73643,
  73651, 73673, 73679, 73681, 73693, 73699, 73709, 73721, 73727, 73751, 73757, 73771, 73783, 73819, 73823, 73847,
  73849, 73859, 73867, 73877, 73883, 73897, 73907, 73939, 73943, 73951, 73961, 73973, 73999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock37 : List ℕ := [
  74017, 74021, 74027, 74047, 74051, 74071, 74077, 74093, 74099, 74101, 74131, 74143, 74149, 74159, 74161, 74167,
  74177, 74189, 74197, 74201, 74203, 74209, 74219, 74231, 74257, 74279, 74287, 74293, 74297, 74311, 74317, 74323,
  74353, 74357, 74363, 74377, 74381, 74383, 74411, 74413, 74419, 74441, 74449, 74453, 74471, 74489, 74507, 74509,
  74521, 74527, 74531, 74551, 74561, 74567, 74573, 74587, 74597, 74609, 74611, 74623, 74653, 74687, 74699, 74707,
  74713, 74717, 74719, 74729, 74731, 74747, 74759, 74761, 74771, 74779, 74797, 74821, 74827, 74831, 74843, 74857,
  74861, 74869, 74873, 74887, 74891, 74897, 74903, 74923, 74929, 74933, 74941, 74959, 75011, 75013, 75017, 75029,
  75037, 75041, 75079, 75083, 75109, 75133, 75149, 75161, 75167, 75169, 75181, 75193, 75209, 75211, 75217, 75223,
  75227, 75239, 75253, 75269, 75277, 75289, 75307, 75323, 75329, 75337, 75347, 75353, 75367, 75377, 75389, 75391,
  75401, 75403, 75407, 75431, 75437, 75479, 75503, 75511, 75521, 75527, 75533, 75539, 75541, 75553, 75557, 75571,
  75577, 75583, 75611, 75617, 75619, 75629, 75641, 75653, 75659, 75679, 75683, 75689, 75703, 75707, 75709, 75721,
  75731, 75743, 75767, 75773, 75781, 75787, 75793, 75797, 75821, 75833, 75853, 75869, 75883, 75913, 75931, 75937,
  75941, 75967, 75979, 75983, 75989, 75991, 75997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock38 : List ℕ := [
  76001, 76003, 76031, 76039, 76079, 76081, 76091, 76099, 76103, 76123, 76129, 76147, 76157, 76159, 76163, 76207,
  76213, 76231, 76243, 76249, 76253, 76259, 76261, 76283, 76289, 76303, 76333, 76343, 76367, 76369, 76379, 76387,
  76403, 76421, 76423, 76441, 76463, 76471, 76481, 76487, 76493, 76507, 76511, 76519, 76537, 76541, 76543, 76561,
  76579, 76597, 76603, 76607, 76631, 76649, 76651, 76667, 76673, 76679, 76697, 76717, 76733, 76753, 76757, 76771,
  76777, 76781, 76801, 76819, 76829, 76831, 76837, 76847, 76871, 76873, 76883, 76907, 76913, 76919, 76943, 76949,
  76961, 76963, 76991, 77003, 77017, 77023, 77029, 77041, 77047, 77069, 77081, 77093, 77101, 77137, 77141, 77153,
  77167, 77171, 77191, 77201, 77213, 77237, 77239, 77243, 77249, 77261, 77263, 77267, 77269, 77279, 77291, 77317,
  77323, 77339, 77347, 77351, 77359, 77369, 77377, 77383, 77417, 77419, 77431, 77447, 77471, 77477, 77479, 77489,
  77491, 77509, 77513, 77521, 77527, 77543, 77549, 77551, 77557, 77563, 77569, 77573, 77587, 77591, 77611, 77617,
  77621, 77641, 77647, 77659, 77681, 77687, 77689, 77699, 77711, 77713, 77719, 77723, 77731, 77743, 77747, 77761,
  77773, 77783, 77797, 77801, 77813, 77839, 77849, 77863, 77867, 77893, 77899, 77929, 77933, 77951, 77969, 77977,
  77983, 77999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock39 : List ℕ := [
  78007, 78017, 78031, 78041, 78049, 78059, 78079, 78101, 78121, 78137, 78139, 78157, 78163, 78167, 78173, 78179,
  78191, 78193, 78203, 78229, 78233, 78241, 78259, 78277, 78283, 78301, 78307, 78311, 78317, 78341, 78347, 78367,
  78401, 78427, 78437, 78439, 78467, 78479, 78487, 78497, 78509, 78511, 78517, 78539, 78541, 78553, 78569, 78571,
  78577, 78583, 78593, 78607, 78623, 78643, 78649, 78653, 78691, 78697, 78707, 78713, 78721, 78737, 78779, 78781,
  78787, 78791, 78797, 78803, 78809, 78823, 78839, 78853, 78857, 78877, 78887, 78889, 78893, 78901, 78919, 78929,
  78941, 78977, 78979, 78989, 79031, 79039, 79043, 79063, 79087, 79103, 79111, 79133, 79139, 79147, 79151, 79153,
  79159, 79181, 79187, 79193, 79201, 79229, 79231, 79241, 79259, 79273, 79279, 79283, 79301, 79309, 79319, 79333,
  79337, 79349, 79357, 79367, 79379, 79393, 79397, 79399, 79411, 79423, 79427, 79433, 79451, 79481, 79493, 79531,
  79537, 79549, 79559, 79561, 79579, 79589, 79601, 79609, 79613, 79621, 79627, 79631, 79633, 79657, 79669, 79687,
  79691, 79693, 79697, 79699, 79757, 79769, 79777, 79801, 79811, 79813, 79817, 79823, 79829, 79841, 79843, 79847,
  79861, 79867, 79873, 79889, 79901, 79903, 79907, 79939, 79943, 79967, 79973, 79979, 79987, 79997, 79999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock40 : List ℕ := [
  80021, 80039, 80051, 80071, 80077, 80107, 80111, 80141, 80147, 80149, 80153, 80167, 80173, 80177, 80191, 80207,
  80209, 80221, 80231, 80233, 80239, 80251, 80263, 80273, 80279, 80287, 80309, 80317, 80329, 80341, 80347, 80363,
  80369, 80387, 80407, 80429, 80447, 80449, 80471, 80473, 80489, 80491, 80513, 80527, 80537, 80557, 80567, 80599,
  80603, 80611, 80621, 80627, 80629, 80651, 80657, 80669, 80671, 80677, 80681, 80683, 80687, 80701, 80713, 80737,
  80747, 80749, 80761, 80777, 80779, 80783, 80789, 80803, 80809, 80819, 80831, 80833, 80849, 80863, 80897, 80909,
  80911, 80917, 80923, 80929, 80933, 80953, 80963, 80989, 81001, 81013, 81017, 81019, 81023, 81031, 81041, 81043,
  81047, 81049, 81071, 81077, 81083, 81097, 81101, 81119, 81131, 81157, 81163, 81173, 81181, 81197, 81199, 81203,
  81223, 81233, 81239, 81281, 81283, 81293, 81299, 81307, 81331, 81343, 81349, 81353, 81359, 81371, 81373, 81401,
  81409, 81421, 81439, 81457, 81463, 81509, 81517, 81527, 81533, 81547, 81551, 81553, 81559, 81563, 81569, 81611,
  81619, 81629, 81637, 81647, 81649, 81667, 81671, 81677, 81689, 81701, 81703, 81707, 81727, 81737, 81749, 81761,
  81769, 81773, 81799, 81817, 81839, 81847, 81853, 81869, 81883, 81899, 81901, 81919, 81929, 81931, 81937, 81943,
  81953, 81967, 81971, 81973
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock41 : List ℕ := [
  82003, 82007, 82009, 82013, 82021, 82031, 82037, 82039, 82051, 82067, 82073, 82129, 82139, 82141, 82153, 82163,
  82171, 82183, 82189, 82193, 82207, 82217, 82219, 82223, 82231, 82237, 82241, 82261, 82267, 82279, 82301, 82307,
  82339, 82349, 82351, 82361, 82373, 82387, 82393, 82421, 82457, 82463, 82469, 82471, 82483, 82487, 82493, 82499,
  82507, 82529, 82531, 82549, 82559, 82561, 82567, 82571, 82591, 82601, 82609, 82613, 82619, 82633, 82651, 82657,
  82699, 82721, 82723, 82727, 82729, 82757, 82759, 82763, 82781, 82787, 82793, 82799, 82811, 82813, 82837, 82847,
  82883, 82889, 82891, 82903, 82913, 82939, 82963, 82981, 82997, 83003, 83009, 83023, 83047, 83059, 83063, 83071,
  83077, 83089, 83093, 83101, 83117, 83137, 83177, 83203, 83207, 83219, 83221, 83227, 83231, 83233, 83243, 83257,
  83267, 83269, 83273, 83299, 83311, 83339, 83341, 83357, 83383, 83389, 83399, 83401, 83407, 83417, 83423, 83431,
  83437, 83443, 83449, 83459, 83471, 83477, 83497, 83537, 83557, 83561, 83563, 83579, 83591, 83597, 83609, 83617,
  83621, 83639, 83641, 83653, 83663, 83689, 83701, 83717, 83719, 83737, 83761, 83773, 83777, 83791, 83813, 83833,
  83843, 83857, 83869, 83873, 83891, 83903, 83911, 83921, 83933, 83939, 83969, 83983, 83987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock42 : List ℕ := [
  84011, 84017, 84047, 84053, 84059, 84061, 84067, 84089, 84121, 84127, 84131, 84137, 84143, 84163, 84179, 84181,
  84191, 84199, 84211, 84221, 84223, 84229, 84239, 84247, 84263, 84299, 84307, 84313, 84317, 84319, 84347, 84349,
  84377, 84389, 84391, 84401, 84407, 84421, 84431, 84437, 84443, 84449, 84457, 84463, 84467, 84481, 84499, 84503,
  84509, 84521, 84523, 84533, 84551, 84559, 84589, 84629, 84631, 84649, 84653, 84659, 84673, 84691, 84697, 84701,
  84713, 84719, 84731, 84737, 84751, 84761, 84787, 84793, 84809, 84811, 84827, 84857, 84859, 84869, 84871, 84913,
  84919, 84947, 84961, 84967, 84977, 84979, 84991, 85009, 85021, 85027, 85037, 85049, 85061, 85081, 85087, 85091,
  85093, 85103, 85109, 85121, 85133, 85147, 85159, 85193, 85199, 85201, 85213, 85223, 85229, 85237, 85243, 85247,
  85259, 85297, 85303, 85313, 85331, 85333, 85361, 85363, 85369, 85381, 85411, 85427, 85429, 85439, 85447, 85451,
  85453, 85469, 85487, 85513, 85517, 85523, 85531, 85549, 85571, 85577, 85597, 85601, 85607, 85619, 85621, 85627,
  85639, 85643, 85661, 85667, 85669, 85691, 85703, 85711, 85717, 85733, 85751, 85781, 85793, 85817, 85819, 85829,
  85831, 85837, 85843, 85847, 85853, 85889, 85903, 85909, 85931, 85933, 85991, 85999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock43 : List ℕ := [
  86011, 86017, 86027, 86029, 86069, 86077, 86083, 86111, 86113, 86117, 86131, 86137, 86143, 86161, 86171, 86179,
  86183, 86197, 86201, 86209, 86239, 86243, 86249, 86257, 86263, 86269, 86287, 86291, 86293, 86297, 86311, 86323,
  86341, 86351, 86353, 86357, 86369, 86371, 86381, 86389, 86399, 86413, 86423, 86441, 86453, 86461, 86467, 86477,
  86491, 86501, 86509, 86531, 86533, 86539, 86561, 86573, 86579, 86587, 86599, 86627, 86629, 86677, 86689, 86693,
  86711, 86719, 86729, 86743, 86753, 86767, 86771, 86783, 86813, 86837, 86843, 86851, 86857, 86861, 86869, 86923,
  86927, 86929, 86939, 86951, 86959, 86969, 86981, 86993, 87011, 87013, 87037, 87041, 87049, 87071, 87083, 87103,
  87107, 87119, 87121, 87133, 87149, 87151, 87179, 87181, 87187, 87211, 87221, 87223, 87251, 87253, 87257, 87277,
  87281, 87293, 87299, 87313, 87317, 87323, 87337, 87359, 87383, 87403, 87407, 87421, 87427, 87433, 87443, 87473,
  87481, 87491, 87509, 87511, 87517, 87523, 87539, 87541, 87547, 87553, 87557, 87559, 87583, 87587, 87589, 87613,
  87623, 87629, 87631, 87641, 87643, 87649, 87671, 87679, 87683, 87691, 87697, 87701, 87719, 87721, 87739, 87743,
  87751, 87767, 87793, 87797, 87803, 87811, 87833, 87853, 87869, 87877, 87881, 87887, 87911, 87917, 87931, 87943,
  87959, 87961, 87973, 87977, 87991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock44 : List ℕ := [
  88001, 88003, 88007, 88019, 88037, 88069, 88079, 88093, 88117, 88129, 88169, 88177, 88211, 88223, 88237, 88241,
  88259, 88261, 88289, 88301, 88321, 88327, 88337, 88339, 88379, 88397, 88411, 88423, 88427, 88463, 88469, 88471,
  88493, 88499, 88513, 88523, 88547, 88589, 88591, 88607, 88609, 88643, 88651, 88657, 88661, 88663, 88667, 88681,
  88721, 88729, 88741, 88747, 88771, 88789, 88793, 88799, 88801, 88807, 88811, 88813, 88817, 88819, 88843, 88853,
  88861, 88867, 88873, 88883, 88897, 88903, 88919, 88937, 88951, 88969, 88993, 88997, 89003, 89009, 89017, 89021,
  89041, 89051, 89057, 89069, 89071, 89083, 89087, 89101, 89107, 89113, 89119, 89123, 89137, 89153, 89189, 89203,
  89209, 89213, 89227, 89231, 89237, 89261, 89269, 89273, 89293, 89303, 89317, 89329, 89363, 89371, 89381, 89387,
  89393, 89399, 89413, 89417, 89431, 89443, 89449, 89459, 89477, 89491, 89501, 89513, 89519, 89521, 89527, 89533,
  89561, 89563, 89567, 89591, 89597, 89599, 89603, 89611, 89627, 89633, 89653, 89657, 89659, 89669, 89671, 89681,
  89689, 89753, 89759, 89767, 89779, 89783, 89797, 89809, 89819, 89821, 89833, 89839, 89849, 89867, 89891, 89897,
  89899, 89909, 89917, 89923, 89939, 89959, 89963, 89977, 89983, 89989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock45 : List ℕ := [
  90001, 90007, 90011, 90017, 90019, 90023, 90031, 90053, 90059, 90067, 90071, 90073, 90089, 90107, 90121, 90127,
  90149, 90163, 90173, 90187, 90191, 90197, 90199, 90203, 90217, 90227, 90239, 90247, 90263, 90271, 90281, 90289,
  90313, 90353, 90359, 90371, 90373, 90379, 90397, 90401, 90403, 90407, 90437, 90439, 90469, 90473, 90481, 90499,
  90511, 90523, 90527, 90529, 90533, 90547, 90583, 90599, 90617, 90619, 90631, 90641, 90647, 90659, 90677, 90679,
  90697, 90703, 90709, 90731, 90749, 90787, 90793, 90803, 90821, 90823, 90833, 90841, 90847, 90863, 90887, 90901,
  90907, 90911, 90917, 90931, 90947, 90971, 90977, 90989, 90997, 91009, 91019, 91033, 91079, 91081, 91097, 91099,
  91121, 91127, 91129, 91139, 91141, 91151, 91153, 91159, 91163, 91183, 91193, 91199, 91229, 91237, 91243, 91249,
  91253, 91283, 91291, 91297, 91303, 91309, 91331, 91367, 91369, 91373, 91381, 91387, 91393, 91397, 91411, 91423,
  91433, 91453, 91457, 91459, 91463, 91493, 91499, 91513, 91529, 91541, 91571, 91573, 91577, 91583, 91591, 91621,
  91631, 91639, 91673, 91691, 91703, 91711, 91733, 91753, 91757, 91771, 91781, 91801, 91807, 91811, 91813, 91823,
  91837, 91841, 91867, 91873, 91909, 91921, 91939, 91943, 91951, 91957, 91961, 91967, 91969, 91997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock46 : List ℕ := [
  92003, 92009, 92033, 92041, 92051, 92077, 92083, 92107, 92111, 92119, 92143, 92153, 92173, 92177, 92179, 92189,
  92203, 92219, 92221, 92227, 92233, 92237, 92243, 92251, 92269, 92297, 92311, 92317, 92333, 92347, 92353, 92357,
  92363, 92369, 92377, 92381, 92383, 92387, 92399, 92401, 92413, 92419, 92431, 92459, 92461, 92467, 92479, 92489,
  92503, 92507, 92551, 92557, 92567, 92569, 92581, 92593, 92623, 92627, 92639, 92641, 92647, 92657, 92669, 92671,
  92681, 92683, 92693, 92699, 92707, 92717, 92723, 92737, 92753, 92761, 92767, 92779, 92789, 92791, 92801, 92809,
  92821, 92831, 92849, 92857, 92861, 92863, 92867, 92893, 92899, 92921, 92927, 92941, 92951, 92957, 92959, 92987,
  92993, 93001, 93047, 93053, 93059, 93077, 93083, 93089, 93097, 93103, 93113, 93131, 93133, 93139, 93151, 93169,
  93179, 93187, 93199, 93229, 93239, 93241, 93251, 93253, 93257, 93263, 93281, 93283, 93287, 93307, 93319, 93323,
  93329, 93337, 93371, 93377, 93383, 93407, 93419, 93427, 93463, 93479, 93481, 93487, 93491, 93493, 93497, 93503,
  93523, 93529, 93553, 93557, 93559, 93563, 93581, 93601, 93607, 93629, 93637, 93683, 93701, 93703, 93719, 93739,
  93761, 93763, 93787, 93809, 93811, 93827, 93851, 93871, 93887, 93889, 93893, 93901, 93911, 93913, 93923, 93937,
  93941, 93949, 93967, 93971, 93979, 93983, 93997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock47 : List ℕ := [
  94007, 94009, 94033, 94049, 94057, 94063, 94079, 94099, 94109, 94111, 94117, 94121, 94151, 94153, 94169, 94201,
  94207, 94219, 94229, 94253, 94261, 94273, 94291, 94307, 94309, 94321, 94327, 94331, 94343, 94349, 94351, 94379,
  94397, 94399, 94421, 94427, 94433, 94439, 94441, 94447, 94463, 94477, 94483, 94513, 94529, 94531, 94541, 94543,
  94547, 94559, 94561, 94573, 94583, 94597, 94603, 94613, 94621, 94649, 94651, 94687, 94693, 94709, 94723, 94727,
  94747, 94771, 94777, 94781, 94789, 94793, 94811, 94819, 94823, 94837, 94841, 94847, 94849, 94873, 94889, 94903,
  94907, 94933, 94949, 94951, 94961, 94993, 94999, 95003, 95009, 95021, 95027, 95063, 95071, 95083, 95087, 95089,
  95093, 95101, 95107, 95111, 95131, 95143, 95153, 95177, 95189, 95191, 95203, 95213, 95219, 95231, 95233, 95239,
  95257, 95261, 95267, 95273, 95279, 95287, 95311, 95317, 95327, 95339, 95369, 95383, 95393, 95401, 95413, 95419,
  95429, 95441, 95443, 95461, 95467, 95471, 95479, 95483, 95507, 95527, 95531, 95539, 95549, 95561, 95569, 95581,
  95597, 95603, 95617, 95621, 95629, 95633, 95651, 95701, 95707, 95713, 95717, 95723, 95731, 95737, 95747, 95773,
  95783, 95789, 95791, 95801, 95803, 95813, 95819, 95857, 95869, 95873, 95881, 95891, 95911, 95917, 95923, 95929,
  95947, 95957, 95959, 95971, 95987, 95989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock48 : List ℕ := [
  96001, 96013, 96017, 96043, 96053, 96059, 96079, 96097, 96137, 96149, 96157, 96167, 96179, 96181, 96199, 96211,
  96221, 96223, 96233, 96259, 96263, 96269, 96281, 96289, 96293, 96323, 96329, 96331, 96337, 96353, 96377, 96401,
  96419, 96431, 96443, 96451, 96457, 96461, 96469, 96479, 96487, 96493, 96497, 96517, 96527, 96553, 96557, 96581,
  96587, 96589, 96601, 96643, 96661, 96667, 96671, 96697, 96703, 96731, 96737, 96739, 96749, 96757, 96763, 96769,
  96779, 96787, 96797, 96799, 96821, 96823, 96827, 96847, 96851, 96857, 96893, 96907, 96911, 96931, 96953, 96959,
  96973, 96979, 96989, 96997, 97001, 97003, 97007, 97021, 97039, 97073, 97081, 97103, 97117, 97127, 97151, 97157,
  97159, 97169, 97171, 97177, 97187, 97213, 97231, 97241, 97259, 97283, 97301, 97303, 97327, 97367, 97369, 97373,
  97379, 97381, 97387, 97397, 97423, 97429, 97441, 97453, 97459, 97463, 97499, 97501, 97511, 97523, 97547, 97549,
  97553, 97561, 97571, 97577, 97579, 97583, 97607, 97609, 97613, 97649, 97651, 97673, 97687, 97711, 97729, 97771,
  97777, 97787, 97789, 97813, 97829, 97841, 97843, 97847, 97849, 97859, 97861, 97871, 97879, 97883, 97919, 97927,
  97931, 97943, 97961, 97967, 97973, 97987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock49 : List ℕ := [
  98009, 98011, 98017, 98041, 98047, 98057, 98081, 98101, 98123, 98129, 98143, 98179, 98207, 98213, 98221, 98227,
  98251, 98257, 98269, 98297, 98299, 98317, 98321, 98323, 98327, 98347, 98369, 98377, 98387, 98389, 98407, 98411,
  98419, 98429, 98443, 98453, 98459, 98467, 98473, 98479, 98491, 98507, 98519, 98533, 98543, 98561, 98563, 98573,
  98597, 98621, 98627, 98639, 98641, 98663, 98669, 98689, 98711, 98713, 98717, 98729, 98731, 98737, 98773, 98779,
  98801, 98807, 98809, 98837, 98849, 98867, 98869, 98873, 98887, 98893, 98897, 98899, 98909, 98911, 98927, 98929,
  98939, 98947, 98953, 98963, 98981, 98993, 98999, 99013, 99017, 99023, 99041, 99053, 99079, 99083, 99089, 99103,
  99109, 99119, 99131, 99133, 99137, 99139, 99149, 99173, 99181, 99191, 99223, 99233, 99241, 99251, 99257, 99259,
  99277, 99289, 99317, 99347, 99349, 99367, 99371, 99377, 99391, 99397, 99401, 99409, 99431, 99439, 99469, 99487,
  99497, 99523, 99527, 99529, 99551, 99559, 99563, 99571, 99577, 99581, 99607, 99611, 99623, 99643, 99661, 99667,
  99679, 99689, 99707, 99709, 99713, 99719, 99721, 99733, 99761, 99767, 99787, 99793, 99809, 99817, 99823, 99829,
  99833, 99839, 99859, 99871, 99877, 99881, 99901, 99907, 99923, 99929, 99961, 99971, 99989, 99991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock50 : List ℕ := [
  100003, 100019, 100043, 100049, 100057, 100069, 100103, 100109, 100129, 100151, 100153, 100169, 100183, 100189, 100193, 100207,
  100213, 100237, 100267, 100271, 100279, 100291, 100297, 100313, 100333, 100343, 100357, 100361, 100363, 100379, 100391, 100393,
  100403, 100411, 100417, 100447, 100459, 100469, 100483, 100493, 100501, 100511, 100517, 100519, 100523, 100537, 100547, 100549,
  100559, 100591, 100609, 100613, 100621, 100649, 100669, 100673, 100693, 100699, 100703, 100733, 100741, 100747, 100769, 100787,
  100799, 100801, 100811, 100823, 100829, 100847, 100853, 100907, 100913, 100927, 100931, 100937, 100943, 100957, 100981, 100987,
  100999, 101009, 101021, 101027, 101051, 101063, 101081, 101089, 101107, 101111, 101113, 101117, 101119, 101141, 101149, 101159,
  101161, 101173, 101183, 101197, 101203, 101207, 101209, 101221, 101267, 101273, 101279, 101281, 101287, 101293, 101323, 101333,
  101341, 101347, 101359, 101363, 101377, 101383, 101399, 101411, 101419, 101429, 101449, 101467, 101477, 101483, 101489, 101501,
  101503, 101513, 101527, 101531, 101533, 101537, 101561, 101573, 101581, 101599, 101603, 101611, 101627, 101641, 101653, 101663,
  101681, 101693, 101701, 101719, 101723, 101737, 101741, 101747, 101749, 101771, 101789, 101797, 101807, 101833, 101837, 101839,
  101863, 101869, 101873, 101879, 101891, 101917, 101921, 101929, 101939, 101957, 101963, 101977, 101987, 101999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock51 : List ℕ := [
  102001, 102013, 102019, 102023, 102031, 102043, 102059, 102061, 102071, 102077, 102079, 102101, 102103, 102107, 102121, 102139,
  102149, 102161, 102181, 102191, 102197, 102199, 102203, 102217, 102229, 102233, 102241, 102251, 102253, 102259, 102293, 102299,
  102301, 102317, 102329, 102337, 102359, 102367, 102397, 102407, 102409, 102433, 102437, 102451, 102461, 102481, 102497, 102499,
  102503, 102523, 102533, 102539, 102547, 102551, 102559, 102563, 102587, 102593, 102607, 102611, 102643, 102647, 102653, 102667,
  102673, 102677, 102679, 102701, 102761, 102763, 102769, 102793, 102797, 102811, 102829, 102841, 102859, 102871, 102877, 102881,
  102911, 102913, 102929, 102931, 102953, 102967, 102983, 103001, 103007, 103043, 103049, 103067, 103069, 103079, 103087, 103091,
  103093, 103099, 103123, 103141, 103171, 103177, 103183, 103217, 103231, 103237, 103289, 103291, 103307, 103319, 103333, 103349,
  103357, 103387, 103391, 103393, 103399, 103409, 103421, 103423, 103451, 103457, 103471, 103483, 103511, 103529, 103549, 103553,
  103561, 103567, 103573, 103577, 103583, 103591, 103613, 103619, 103643, 103651, 103657, 103669, 103681, 103687, 103699, 103703,
  103723, 103769, 103787, 103801, 103811, 103813, 103837, 103841, 103843, 103867, 103889, 103903, 103913, 103919, 103951, 103963,
  103967, 103969, 103979, 103981, 103991, 103993, 103997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock52 : List ℕ := [
  104003, 104009, 104021, 104033, 104047, 104053, 104059, 104087, 104089, 104107, 104113, 104119, 104123, 104147, 104149, 104161,
  104173, 104179, 104183, 104207, 104231, 104233, 104239, 104243, 104281, 104287, 104297, 104309, 104311, 104323, 104327, 104347,
  104369, 104381, 104383, 104393, 104399, 104417, 104459, 104471, 104473, 104479, 104491, 104513, 104527, 104537, 104543, 104549,
  104551, 104561, 104579, 104593, 104597, 104623, 104639, 104651, 104659, 104677, 104681, 104683, 104693, 104701, 104707, 104711,
  104717, 104723, 104729, 104743, 104759, 104761, 104773, 104779, 104789, 104801, 104803, 104827, 104831, 104849, 104851, 104869,
  104879, 104891, 104911, 104917, 104933, 104947, 104953, 104959, 104971, 104987, 104999, 105019, 105023, 105031, 105037, 105071,
  105097, 105107, 105137, 105143, 105167, 105173, 105199, 105211, 105227, 105229, 105239, 105251, 105253, 105263, 105269, 105277,
  105319, 105323, 105331, 105337, 105341, 105359, 105361, 105367, 105373, 105379, 105389, 105397, 105401, 105407, 105437, 105449,
  105467, 105491, 105499, 105503, 105509, 105517, 105527, 105529, 105533, 105541, 105557, 105563, 105601, 105607, 105613, 105619,
  105649, 105653, 105667, 105673, 105683, 105691, 105701, 105727, 105733, 105751, 105761, 105767, 105769, 105817, 105829, 105863,
  105871, 105883, 105899, 105907, 105913, 105929, 105943, 105953, 105967, 105971, 105977, 105983, 105997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock53 : List ℕ := [
  106013, 106019, 106031, 106033, 106087, 106103, 106109, 106121, 106123, 106129, 106163, 106181, 106187, 106189, 106207, 106213,
  106217, 106219, 106243, 106261, 106273, 106277, 106279, 106291, 106297, 106303, 106307, 106319, 106321, 106331, 106349, 106357,
  106363, 106367, 106373, 106391, 106397, 106411, 106417, 106427, 106433, 106441, 106451, 106453, 106487, 106501, 106531, 106537,
  106541, 106543, 106591, 106619, 106621, 106627, 106637, 106649, 106657, 106661, 106663, 106669, 106681, 106693, 106699, 106703,
  106721, 106727, 106739, 106747, 106751, 106753, 106759, 106781, 106783, 106787, 106801, 106823, 106853, 106859, 106861, 106867,
  106871, 106877, 106903, 106907, 106921, 106937, 106949, 106957, 106961, 106963, 106979, 106993, 107021, 107033, 107053, 107057,
  107069, 107071, 107077, 107089, 107099, 107101, 107119, 107123, 107137, 107171, 107183, 107197, 107201, 107209, 107227, 107243,
  107251, 107269, 107273, 107279, 107309, 107323, 107339, 107347, 107351, 107357, 107377, 107441, 107449, 107453, 107467, 107473,
  107507, 107509, 107563, 107581, 107599, 107603, 107609, 107621, 107641, 107647, 107671, 107687, 107693, 107699, 107713, 107717,
  107719, 107741, 107747, 107761, 107773, 107777, 107791, 107827, 107837, 107839, 107843, 107857, 107867, 107873, 107881, 107897,
  107903, 107923, 107927, 107941, 107951, 107971, 107981, 107999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock54 : List ℕ := [
  108007, 108011, 108013, 108023, 108037, 108041, 108061, 108079, 108089, 108107, 108109, 108127, 108131, 108139, 108161, 108179,
  108187, 108191, 108193, 108203, 108211, 108217, 108223, 108233, 108247, 108263, 108271, 108287, 108289, 108293, 108301, 108343,
  108347, 108359, 108377, 108379, 108401, 108413, 108421, 108439, 108457, 108461, 108463, 108497, 108499, 108503, 108517, 108529,
  108533, 108541, 108553, 108557, 108571, 108587, 108631, 108637, 108643, 108649, 108677, 108707, 108709, 108727, 108739, 108751,
  108761, 108769, 108791, 108793, 108799, 108803, 108821, 108827, 108863, 108869, 108877, 108881, 108883, 108887, 108893, 108907,
  108917, 108923, 108929, 108943, 108947, 108949, 108959, 108961, 108967, 108971, 108991, 109001, 109013, 109037, 109049, 109063,
  109073, 109097, 109103, 109111, 109121, 109133, 109139, 109141, 109147, 109159, 109169, 109171, 109199, 109201, 109211, 109229,
  109253, 109267, 109279, 109297, 109303, 109313, 109321, 109331, 109357, 109363, 109367, 109379, 109387, 109391, 109397, 109423,
  109433, 109441, 109451, 109453, 109469, 109471, 109481, 109507, 109517, 109519, 109537, 109541, 109547, 109567, 109579, 109583,
  109589, 109597, 109609, 109619, 109621, 109639, 109661, 109663, 109673, 109717, 109721, 109741, 109751, 109789, 109793, 109807,
  109819, 109829, 109831, 109841, 109843, 109847, 109849, 109859, 109873, 109883, 109891, 109897, 109903, 109913, 109919, 109937,
  109943, 109961, 109987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock55 : List ℕ := [
  110017, 110023, 110039, 110051, 110059, 110063, 110069, 110083, 110119, 110129, 110161, 110183, 110221, 110233, 110237, 110251,
  110261, 110269, 110273, 110281, 110291, 110311, 110321, 110323, 110339, 110359, 110419, 110431, 110437, 110441, 110459, 110477,
  110479, 110491, 110501, 110503, 110527, 110533, 110543, 110557, 110563, 110567, 110569, 110573, 110581, 110587, 110597, 110603,
  110609, 110623, 110629, 110641, 110647, 110651, 110681, 110711, 110729, 110731, 110749, 110753, 110771, 110777, 110807, 110813,
  110819, 110821, 110849, 110863, 110879, 110881, 110899, 110909, 110917, 110921, 110923, 110927, 110933, 110939, 110947, 110951,
  110969, 110977, 110989, 111029, 111031, 111043, 111049, 111053, 111091, 111103, 111109, 111119, 111121, 111127, 111143, 111149,
  111187, 111191, 111211, 111217, 111227, 111229, 111253, 111263, 111269, 111271, 111301, 111317, 111323, 111337, 111341, 111347,
  111373, 111409, 111427, 111431, 111439, 111443, 111467, 111487, 111491, 111493, 111497, 111509, 111521, 111533, 111539, 111577,
  111581, 111593, 111599, 111611, 111623, 111637, 111641, 111653, 111659, 111667, 111697, 111721, 111731, 111733, 111751, 111767,
  111773, 111779, 111781, 111791, 111799, 111821, 111827, 111829, 111833, 111847, 111857, 111863, 111869, 111871, 111893, 111913,
  111919, 111949, 111953, 111959, 111973, 111977, 111997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock56 : List ℕ := [
  112019, 112031, 112061, 112067, 112069, 112087, 112097, 112103, 112111, 112121, 112129, 112139, 112153, 112163, 112181, 112199,
  112207, 112213, 112223, 112237, 112241, 112247, 112249, 112253, 112261, 112279, 112289, 112291, 112297, 112303, 112327, 112331,
  112337, 112339, 112349, 112361, 112363, 112397, 112403, 112429, 112459, 112481, 112501, 112507, 112543, 112559, 112571, 112573,
  112577, 112583, 112589, 112601, 112603, 112621, 112643, 112657, 112663, 112687, 112691, 112741, 112757, 112759, 112771, 112787,
  112799, 112807, 112831, 112843, 112859, 112877, 112901, 112909, 112913, 112919, 112921, 112927, 112939, 112951, 112967, 112979,
  112997, 113011, 113017, 113021, 113023, 113027, 113039, 113041, 113051, 113063, 113081, 113083, 113089, 113093, 113111, 113117,
  113123, 113131, 113143, 113147, 113149, 113153, 113159, 113161, 113167, 113171, 113173, 113177, 113189, 113209, 113213, 113227,
  113233, 113279, 113287, 113327, 113329, 113341, 113357, 113359, 113363, 113371, 113381, 113383, 113417, 113437, 113453, 113467,
  113489, 113497, 113501, 113513, 113537, 113539, 113557, 113567, 113591, 113621, 113623, 113647, 113657, 113683, 113717, 113719,
  113723, 113731, 113749, 113759, 113761, 113777, 113779, 113783, 113797, 113809, 113819, 113837, 113843, 113891, 113899, 113903,
  113909, 113921, 113933, 113947, 113957, 113963, 113969, 113983, 113989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock57 : List ℕ := [
  114001, 114013, 114031, 114041, 114043, 114067, 114073, 114077, 114083, 114089, 114113, 114143, 114157, 114161, 114167, 114193,
  114197, 114199, 114203, 114217, 114221, 114229, 114259, 114269, 114277, 114281, 114299, 114311, 114319, 114329, 114343, 114371,
  114377, 114407, 114419, 114451, 114467, 114473, 114479, 114487, 114493, 114547, 114553, 114571, 114577, 114593, 114599, 114601,
  114613, 114617, 114641, 114643, 114649, 114659, 114661, 114671, 114679, 114689, 114691, 114713, 114743, 114749, 114757, 114761,
  114769, 114773, 114781, 114797, 114799, 114809, 114827, 114833, 114847, 114859, 114883, 114889, 114901, 114913, 114941, 114967,
  114973, 114997, 115001, 115013, 115019, 115021, 115057, 115061, 115067, 115079, 115099, 115117, 115123, 115127, 115133, 115151,
  115153, 115163, 115183, 115201, 115211, 115223, 115237, 115249, 115259, 115279, 115301, 115303, 115309, 115319, 115321, 115327,
  115331, 115337, 115343, 115361, 115363, 115399, 115421, 115429, 115459, 115469, 115471, 115499, 115513, 115523, 115547, 115553,
  115561, 115571, 115589, 115597, 115601, 115603, 115613, 115631, 115637, 115657, 115663, 115679, 115693, 115727, 115733, 115741,
  115751, 115757, 115763, 115769, 115771, 115777, 115781, 115783, 115793, 115807, 115811, 115823, 115831, 115837, 115849, 115853,
  115859, 115861, 115873, 115877, 115879, 115883, 115891, 115901, 115903, 115931, 115933, 115963, 115979, 115981, 115987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock58 : List ℕ := [
  116009, 116027, 116041, 116047, 116089, 116099, 116101, 116107, 116113, 116131, 116141, 116159, 116167, 116177, 116189, 116191,
  116201, 116239, 116243, 116257, 116269, 116273, 116279, 116293, 116329, 116341, 116351, 116359, 116371, 116381, 116387, 116411,
  116423, 116437, 116443, 116447, 116461, 116471, 116483, 116491, 116507, 116531, 116533, 116537, 116539, 116549, 116579, 116593,
  116639, 116657, 116663, 116681, 116687, 116689, 116707, 116719, 116731, 116741, 116747, 116789, 116791, 116797, 116803, 116819,
  116827, 116833, 116849, 116867, 116881, 116903, 116911, 116923, 116927, 116929, 116933, 116953, 116959, 116969, 116981, 116989,
  116993, 117017, 117023, 117037, 117041, 117043, 117053, 117071, 117101, 117109, 117119, 117127, 117133, 117163, 117167, 117191,
  117193, 117203, 117209, 117223, 117239, 117241, 117251, 117259, 117269, 117281, 117307, 117319, 117329, 117331, 117353, 117361,
  117371, 117373, 117389, 117413, 117427, 117431, 117437, 117443, 117497, 117499, 117503, 117511, 117517, 117529, 117539, 117541,
  117563, 117571, 117577, 117617, 117619, 117643, 117659, 117671, 117673, 117679, 117701, 117703, 117709, 117721, 117727, 117731,
  117751, 117757, 117763, 117773, 117779, 117787, 117797, 117809, 117811, 117833, 117839, 117841, 117851, 117877, 117881, 117883,
  117889, 117899, 117911, 117917, 117937, 117959, 117973, 117977, 117979, 117989, 117991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock59 : List ℕ := [
  118033, 118037, 118043, 118051, 118057, 118061, 118081, 118093, 118127, 118147, 118163, 118169, 118171, 118189, 118211, 118213,
  118219, 118247, 118249, 118253, 118259, 118273, 118277, 118297, 118343, 118361, 118369, 118373, 118387, 118399, 118409, 118411,
  118423, 118429, 118453, 118457, 118463, 118471, 118493, 118529, 118543, 118549, 118571, 118583, 118589, 118603, 118619, 118621,
  118633, 118661, 118669, 118673, 118681, 118687, 118691, 118709, 118717, 118739, 118747, 118751, 118757, 118787, 118799, 118801,
  118819, 118831, 118843, 118861, 118873, 118891, 118897, 118901, 118903, 118907, 118913, 118927, 118931, 118967, 118973, 119027,
  119033, 119039, 119047, 119057, 119069, 119083, 119087, 119089, 119099, 119101, 119107, 119129, 119131, 119159, 119173, 119179,
  119183, 119191, 119227, 119233, 119237, 119243, 119267, 119291, 119293, 119297, 119299, 119311, 119321, 119359, 119363, 119389,
  119417, 119419, 119429, 119447, 119489, 119503, 119513, 119533, 119549, 119551, 119557, 119563, 119569, 119591, 119611, 119617,
  119627, 119633, 119653, 119657, 119659, 119671, 119677, 119687, 119689, 119699, 119701, 119723, 119737, 119747, 119759, 119771,
  119773, 119783, 119797, 119809, 119813, 119827, 119831, 119839, 119849, 119851, 119869, 119881, 119891, 119921, 119923, 119929,
  119953, 119963, 119971, 119981, 119983, 119993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock60 : List ℕ := [
  120011, 120017, 120041, 120047, 120049, 120067, 120077, 120079, 120091, 120097, 120103, 120121, 120157, 120163, 120167, 120181,
  120193, 120199, 120209, 120223, 120233, 120247, 120277, 120283, 120293, 120299, 120319, 120331, 120349, 120371, 120383, 120391,
  120397, 120401, 120413, 120427, 120431, 120473, 120503, 120511, 120539, 120551, 120557, 120563, 120569, 120577, 120587, 120607,
  120619, 120623, 120641, 120647, 120661, 120671, 120677, 120689, 120691, 120709, 120713, 120721, 120737, 120739, 120749, 120763,
  120767, 120779, 120811, 120817, 120823, 120829, 120833, 120847, 120851, 120863, 120871, 120877, 120889, 120899, 120907, 120917,
  120919, 120929, 120937, 120941, 120943, 120947, 120977, 120997, 121001, 121007, 121013, 121019, 121021, 121039, 121061, 121063,
  121067, 121081, 121123, 121139, 121151, 121157, 121169, 121171, 121181, 121189, 121229, 121259, 121267, 121271, 121283, 121291,
  121309, 121313, 121321, 121327, 121333, 121343, 121349, 121351, 121357, 121367, 121369, 121379, 121403, 121421, 121439, 121441,
  121447, 121453, 121469, 121487, 121493, 121501, 121507, 121523, 121531, 121547, 121553, 121559, 121571, 121577, 121579, 121591,
  121607, 121609, 121621, 121631, 121633, 121637, 121661, 121687, 121697, 121711, 121721, 121727, 121763, 121787, 121789, 121843,
  121853, 121867, 121883, 121889, 121909, 121921, 121931, 121937, 121949, 121951, 121963, 121967, 121993, 121997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock61 : List ℕ := [
  122011, 122021, 122027, 122029, 122033, 122039, 122041, 122051, 122053, 122069, 122081, 122099, 122117, 122131, 122147, 122149,
  122167, 122173, 122201, 122203, 122207, 122209, 122219, 122231, 122251, 122263, 122267, 122273, 122279, 122299, 122321, 122323,
  122327, 122347, 122363, 122387, 122389, 122393, 122399, 122401, 122443, 122449, 122453, 122471, 122477, 122489, 122497, 122501,
  122503, 122509, 122527, 122533, 122557, 122561, 122579, 122597, 122599, 122609, 122611, 122651, 122653, 122663, 122693, 122701,
  122719, 122741, 122743, 122753, 122761, 122777, 122789, 122819, 122827, 122833, 122839, 122849, 122861, 122867, 122869, 122887,
  122891, 122921, 122929, 122939, 122953, 122957, 122963, 122971, 123001, 123007, 123017, 123031, 123049, 123059, 123077, 123083,
  123091, 123113, 123121, 123127, 123143, 123169, 123191, 123203, 123209, 123217, 123229, 123239, 123259, 123269, 123289, 123307,
  123311, 123323, 123341, 123373, 123377, 123379, 123397, 123401, 123407, 123419, 123427, 123433, 123439, 123449, 123457, 123479,
  123491, 123493, 123499, 123503, 123517, 123527, 123547, 123551, 123553, 123581, 123583, 123593, 123601, 123619, 123631, 123637,
  123653, 123661, 123667, 123677, 123701, 123707, 123719, 123727, 123731, 123733, 123737, 123757, 123787, 123791, 123803, 123817,
  123821, 123829, 123833, 123853, 123863, 123887, 123911, 123923, 123931, 123941, 123953, 123973, 123979, 123983, 123989, 123997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock62 : List ℕ := [
  124001, 124021, 124067, 124087, 124097, 124121, 124123, 124133, 124139, 124147, 124153, 124171, 124181, 124183, 124193, 124199,
  124213, 124231, 124247, 124249, 124277, 124291, 124297, 124301, 124303, 124309, 124337, 124339, 124343, 124349, 124351, 124363,
  124367, 124427, 124429, 124433, 124447, 124459, 124471, 124477, 124489, 124493, 124513, 124529, 124541, 124543, 124561, 124567,
  124577, 124601, 124633, 124643, 124669, 124673, 124679, 124693, 124699, 124703, 124717, 124721, 124739, 124753, 124759, 124769,
  124771, 124777, 124781, 124783, 124793, 124799, 124819, 124823, 124847, 124853, 124897, 124907, 124909, 124919, 124951, 124979,
  124981, 124987, 124991, 125003, 125017, 125029, 125053, 125063, 125093, 125101, 125107, 125113, 125117, 125119, 125131, 125141,
  125149, 125183, 125197, 125201, 125207, 125219, 125221, 125231, 125243, 125261, 125269, 125287, 125299, 125303, 125311, 125329,
  125339, 125353, 125371, 125383, 125387, 125399, 125407, 125423, 125429, 125441, 125453, 125471, 125497, 125507, 125509, 125527,
  125539, 125551, 125591, 125597, 125617, 125621, 125627, 125639, 125641, 125651, 125659, 125669, 125683, 125687, 125693, 125707,
  125711, 125717, 125731, 125737, 125743, 125753, 125777, 125789, 125791, 125803, 125813, 125821, 125863, 125887, 125897, 125899,
  125921, 125927, 125929, 125933, 125941, 125959, 125963
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock63 : List ℕ := [
  126001, 126011, 126013, 126019, 126023, 126031, 126037, 126041, 126047, 126067, 126079, 126097, 126107, 126127, 126131, 126143,
  126151, 126173, 126199, 126211, 126223, 126227, 126229, 126233, 126241, 126257, 126271, 126307, 126311, 126317, 126323, 126337,
  126341, 126349, 126359, 126397, 126421, 126433, 126443, 126457, 126461, 126473, 126481, 126487, 126491, 126493, 126499, 126517,
  126541, 126547, 126551, 126583, 126601, 126611, 126613, 126631, 126641, 126653, 126683, 126691, 126703, 126713, 126719, 126733,
  126739, 126743, 126751, 126757, 126761, 126781, 126823, 126827, 126839, 126851, 126857, 126859, 126913, 126923, 126943, 126949,
  126961, 126967, 126989, 127031, 127033, 127037, 127051, 127079, 127081, 127103, 127123, 127133, 127139, 127157, 127163, 127189,
  127207, 127217, 127219, 127241, 127247, 127249, 127261, 127271, 127277, 127289, 127291, 127297, 127301, 127321, 127331, 127343,
  127363, 127373, 127399, 127403, 127423, 127447, 127453, 127481, 127487, 127493, 127507, 127529, 127541, 127549, 127579, 127583,
  127591, 127597, 127601, 127607, 127609, 127637, 127643, 127649, 127657, 127663, 127669, 127679, 127681, 127691, 127703, 127709,
  127711, 127717, 127727, 127733, 127739, 127747, 127763, 127781, 127807, 127817, 127819, 127837, 127843, 127849, 127859, 127867,
  127873, 127877, 127913, 127921, 127931, 127951, 127973, 127979, 127997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock64 : List ℕ := [
  128021, 128033, 128047, 128053, 128099, 128111, 128113, 128119, 128147, 128153, 128159, 128173, 128189, 128201, 128203, 128213,
  128221, 128237, 128239, 128257, 128273, 128287, 128291, 128311, 128321, 128327, 128339, 128341, 128347, 128351, 128377, 128389,
  128393, 128399, 128411, 128413, 128431, 128437, 128449, 128461, 128467, 128473, 128477, 128483, 128489, 128509, 128519, 128521,
  128549, 128551, 128563, 128591, 128599, 128603, 128621, 128629, 128657, 128659, 128663, 128669, 128677, 128683, 128693, 128717,
  128747, 128749, 128761, 128767, 128813, 128819, 128831, 128833, 128837, 128857, 128861, 128873, 128879, 128903, 128923, 128939,
  128941, 128951, 128959, 128969, 128971, 128981, 128983, 128987, 128993, 129001, 129011, 129023, 129037, 129049, 129061, 129083,
  129089, 129097, 129113, 129119, 129121, 129127, 129169, 129187, 129193, 129197, 129209, 129221, 129223, 129229, 129263, 129277,
  129281, 129287, 129289, 129293, 129313, 129341, 129347, 129361, 129379, 129401, 129403, 129419, 129439, 129443, 129449, 129457,
  129461, 129469, 129491, 129497, 129499, 129509, 129517, 129527, 129529, 129533, 129539, 129553, 129581, 129587, 129589, 129593,
  129607, 129629, 129631, 129641, 129643, 129671, 129707, 129719, 129733, 129737, 129749, 129757, 129763, 129769, 129793, 129803,
  129841, 129853, 129887, 129893, 129901, 129917, 129919, 129937, 129953, 129959, 129967, 129971
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock65 : List ℕ := [
  130003, 130021, 130027, 130043, 130051, 130057, 130069, 130073, 130079, 130087, 130099, 130121, 130127, 130147, 130171, 130183,
  130199, 130201, 130211, 130223, 130241, 130253, 130259, 130261, 130267, 130279, 130303, 130307, 130337, 130343, 130349, 130363,
  130367, 130369, 130379, 130399, 130409, 130411, 130423, 130439, 130447, 130457, 130469, 130477, 130483, 130489, 130513, 130517,
  130523, 130531, 130547, 130553, 130579, 130589, 130619, 130621, 130631, 130633, 130639, 130643, 130649, 130651, 130657, 130681,
  130687, 130693, 130699, 130729, 130769, 130783, 130787, 130807, 130811, 130817, 130829, 130841, 130843, 130859, 130873, 130927,
  130957, 130969, 130973, 130981, 130987, 131009, 131011, 131023, 131041, 131059, 131063, 131071, 131101, 131111, 131113, 131129,
  131143, 131149, 131171, 131203, 131213, 131221, 131231, 131249, 131251, 131267, 131293, 131297, 131303, 131311, 131317, 131321,
  131357, 131363, 131371, 131381, 131413, 131431, 131437, 131441, 131447, 131449, 131477, 131479, 131489, 131497, 131501, 131507,
  131519, 131543, 131561, 131581, 131591, 131611, 131617, 131627, 131639, 131641, 131671, 131687, 131701, 131707, 131711, 131713,
  131731, 131743, 131749, 131759, 131771, 131777, 131779, 131783, 131797, 131837, 131839, 131849, 131861, 131891, 131893, 131899,
  131909, 131927, 131933, 131939, 131941, 131947, 131959, 131969
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock66 : List ℕ := [
  132001, 132019, 132047, 132049, 132059, 132071, 132103, 132109, 132113, 132137, 132151, 132157, 132169, 132173, 132199, 132229,
  132233, 132241, 132247, 132257, 132263, 132283, 132287, 132299, 132313, 132329, 132331, 132347, 132361, 132367, 132371, 132383,
  132403, 132409, 132421, 132437, 132439, 132469, 132491, 132499, 132511, 132523, 132527, 132529, 132533, 132541, 132547, 132589,
  132607, 132611, 132619, 132623, 132631, 132637, 132647, 132661, 132667, 132679, 132689, 132697, 132701, 132707, 132709, 132721,
  132739, 132749, 132751, 132757, 132761, 132763, 132817, 132833, 132851, 132857, 132859, 132863, 132887, 132893, 132911, 132929,
  132947, 132949, 132953, 132961, 132967, 132971, 132989, 133013, 133033, 133039, 133051, 133069, 133073, 133087, 133097, 133103,
  133109, 133117, 133121, 133153, 133157, 133169, 133183, 133187, 133201, 133213, 133241, 133253, 133261, 133271, 133277, 133279,
  133283, 133303, 133319, 133321, 133327, 133337, 133349, 133351, 133379, 133387, 133391, 133403, 133417, 133439, 133447, 133451,
  133481, 133493, 133499, 133519, 133541, 133543, 133559, 133571, 133583, 133597, 133631, 133633, 133649, 133657, 133669, 133673,
  133691, 133697, 133709, 133711, 133717, 133723, 133733, 133769, 133781, 133801, 133811, 133813, 133831, 133843, 133853, 133873,
  133877, 133919, 133949, 133963, 133967, 133979, 133981, 133993, 133999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock67 : List ℕ := [
  134033, 134039, 134047, 134053, 134059, 134077, 134081, 134087, 134089, 134093, 134129, 134153, 134161, 134171, 134177, 134191,
  134207, 134213, 134219, 134227, 134243, 134257, 134263, 134269, 134287, 134291, 134293, 134327, 134333, 134339, 134341, 134353,
  134359, 134363, 134369, 134371, 134399, 134401, 134417, 134437, 134443, 134471, 134489, 134503, 134507, 134513, 134581, 134587,
  134591, 134593, 134597, 134609, 134639, 134669, 134677, 134681, 134683, 134699, 134707, 134731, 134741, 134753, 134777, 134789,
  134807, 134837, 134839, 134851, 134857, 134867, 134873, 134887, 134909, 134917, 134921, 134923, 134947, 134951, 134989, 134999,
  135007, 135017, 135019, 135029, 135043, 135049, 135059, 135077, 135089, 135101, 135119, 135131, 135151, 135173, 135181, 135193,
  135197, 135209, 135211, 135221, 135241, 135257, 135271, 135277, 135281, 135283, 135301, 135319, 135329, 135347, 135349, 135353,
  135367, 135389, 135391, 135403, 135409, 135427, 135431, 135433, 135449, 135461, 135463, 135467, 135469, 135479, 135497, 135511,
  135533, 135559, 135571, 135581, 135589, 135593, 135599, 135601, 135607, 135613, 135617, 135623, 135637, 135647, 135649, 135661,
  135671, 135697, 135701, 135719, 135721, 135727, 135731, 135743, 135757, 135781, 135787, 135799, 135829, 135841, 135851, 135859,
  135887, 135893, 135899, 135911, 135913, 135929, 135937, 135977, 135979
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock68 : List ℕ := [
  136013, 136027, 136033, 136043, 136057, 136067, 136069, 136093, 136099, 136111, 136133, 136139, 136163, 136177, 136189, 136193,
  136207, 136217, 136223, 136237, 136247, 136261, 136273, 136277, 136303, 136309, 136319, 136327, 136333, 136337, 136343, 136351,
  136361, 136373, 136379, 136393, 136397, 136399, 136403, 136417, 136421, 136429, 136447, 136453, 136463, 136471, 136481, 136483,
  136501, 136511, 136519, 136523, 136531, 136537, 136541, 136547, 136559, 136573, 136601, 136603, 136607, 136621, 136649, 136651,
  136657, 136691, 136693, 136709, 136711, 136727, 136733, 136739, 136751, 136753, 136769, 136777, 136811, 136813, 136841, 136849,
  136859, 136861, 136879, 136883, 136889, 136897, 136943, 136949, 136951, 136963, 136973, 136979, 136987, 136991, 136993, 136999,
  137029, 137077, 137087, 137089, 137117, 137119, 137131, 137143, 137147, 137153, 137177, 137183, 137191, 137197, 137201, 137209,
  137219, 137239, 137251, 137273, 137279, 137303, 137321, 137339, 137341, 137353, 137359, 137363, 137369, 137383, 137387, 137393,
  137399, 137413, 137437, 137443, 137447, 137453, 137477, 137483, 137491, 137507, 137519, 137537, 137567, 137573, 137587, 137593,
  137597, 137623, 137633, 137639, 137653, 137659, 137699, 137707, 137713, 137723, 137737, 137743, 137771, 137777, 137791, 137803,
  137827, 137831, 137849, 137867, 137869, 137873, 137909, 137911, 137927, 137933, 137941, 137947, 137957, 137983, 137993, 137999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock69 : List ℕ := [
  138007, 138041, 138053, 138059, 138071, 138077, 138079, 138101, 138107, 138113, 138139, 138143, 138157, 138163, 138179, 138181,
  138191, 138197, 138209, 138239, 138241, 138247, 138251, 138283, 138289, 138311, 138319, 138323, 138337, 138349, 138371, 138373,
  138389, 138401, 138403, 138407, 138427, 138433, 138449, 138451, 138461, 138469, 138493, 138497, 138511, 138517, 138547, 138559,
  138563, 138569, 138571, 138577, 138581, 138587, 138599, 138617, 138629, 138637, 138641, 138647, 138661, 138679, 138683, 138727,
  138731, 138739, 138763, 138793, 138797, 138799, 138821, 138829, 138841, 138863, 138869, 138883, 138889, 138893, 138899, 138917,
  138923, 138937, 138959, 138967, 138977, 139021, 139033, 139067, 139079, 139091, 139109, 139121, 139123, 139133, 139169, 139177,
  139187, 139199, 139201, 139241, 139267, 139273, 139291, 139297, 139301, 139303, 139309, 139313, 139333, 139339, 139343, 139361,
  139367, 139369, 139387, 139393, 139397, 139409, 139423, 139429, 139439, 139457, 139459, 139483, 139487, 139493, 139501, 139511,
  139537, 139547, 139571, 139589, 139591, 139597, 139609, 139619, 139627, 139661, 139663, 139681, 139697, 139703, 139709, 139721,
  139729, 139739, 139747, 139753, 139759, 139787, 139801, 139813, 139831, 139837, 139861, 139871, 139883, 139891, 139901, 139907,
  139921, 139939, 139943, 139967, 139969, 139981, 139987, 139991, 139999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock70 : List ℕ := [
  140009, 140053, 140057, 140069, 140071, 140111, 140123, 140143, 140159, 140167, 140171, 140177, 140191, 140197, 140207, 140221,
  140227, 140237, 140249, 140263, 140269, 140281, 140297, 140317, 140321, 140333, 140339, 140351, 140363, 140381, 140401, 140407,
  140411, 140417, 140419, 140423, 140443, 140449, 140453, 140473, 140477, 140521, 140527, 140533, 140549, 140551, 140557, 140587,
  140593, 140603, 140611, 140617, 140627, 140629, 140639, 140659, 140663, 140677, 140681, 140683, 140689, 140717, 140729, 140731,
  140741, 140759, 140761, 140773, 140779, 140797, 140813, 140827, 140831, 140837, 140839, 140863, 140867, 140869, 140891, 140893,
  140897, 140909, 140929, 140939, 140977, 140983, 140989, 141023, 141041, 141061, 141067, 141073, 141079, 141101, 141107, 141121,
  141131, 141157, 141161, 141179, 141181, 141199, 141209, 141221, 141223, 141233, 141241, 141257, 141263, 141269, 141277, 141283,
  141301, 141307, 141311, 141319, 141353, 141359, 141371, 141397, 141403, 141413, 141439, 141443, 141461, 141481, 141497, 141499,
  141509, 141511, 141529, 141539, 141551, 141587, 141601, 141613, 141619, 141623, 141629, 141637, 141649, 141653, 141667, 141671,
  141677, 141679, 141689, 141697, 141707, 141709, 141719, 141731, 141761, 141767, 141769, 141773, 141793, 141803, 141811, 141829,
  141833, 141851, 141853, 141863, 141871, 141907, 141917, 141931, 141937, 141941, 141959, 141961, 141971, 141991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock71 : List ℕ := [
  142007, 142019, 142031, 142039, 142049, 142057, 142061, 142067, 142097, 142099, 142111, 142123, 142151, 142157, 142159, 142169,
  142183, 142189, 142193, 142211, 142217, 142223, 142231, 142237, 142271, 142297, 142319, 142327, 142357, 142369, 142381, 142391,
  142403, 142421, 142427, 142433, 142453, 142469, 142501, 142529, 142537, 142543, 142547, 142553, 142559, 142567, 142573, 142589,
  142591, 142601, 142607, 142609, 142619, 142657, 142673, 142697, 142699, 142711, 142733, 142757, 142759, 142771, 142787, 142789,
  142799, 142811, 142837, 142841, 142867, 142871, 142873, 142897, 142903, 142907, 142939, 142949, 142963, 142969, 142973, 142979,
  142981, 142993, 143053, 143063, 143093, 143107, 143111, 143113, 143137, 143141, 143159, 143177, 143197, 143239, 143243, 143249,
  143257, 143261, 143263, 143281, 143287, 143291, 143329, 143333, 143357, 143387, 143401, 143413, 143419, 143443, 143461, 143467,
  143477, 143483, 143489, 143501, 143503, 143509, 143513, 143519, 143527, 143537, 143551, 143567, 143569, 143573, 143593, 143609,
  143617, 143629, 143651, 143653, 143669, 143677, 143687, 143699, 143711, 143719, 143729, 143743, 143779, 143791, 143797, 143807,
  143813, 143821, 143827, 143831, 143833, 143873, 143879, 143881, 143909, 143947, 143953, 143971, 143977, 143981, 143999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock72 : List ℕ := [
  144013, 144031, 144037, 144061, 144071, 144073, 144103, 144139, 144161, 144163, 144167, 144169, 144173, 144203, 144223, 144241,
  144247, 144253, 144259, 144271, 144289, 144299, 144307, 144311, 144323, 144341, 144349, 144379, 144383, 144407, 144409, 144413,
  144427, 144439, 144451, 144461, 144479, 144481, 144497, 144511, 144539, 144541, 144563, 144569, 144577, 144583, 144589, 144593,
  144611, 144629, 144659, 144667, 144671, 144701, 144709, 144719, 144731, 144737, 144751, 144757, 144763, 144773, 144779, 144791,
  144817, 144829, 144839, 144847, 144883, 144887, 144889, 144899, 144917, 144931, 144941, 144961, 144967, 144973, 144983, 145007,
  145009, 145021, 145031, 145037, 145043, 145063, 145069, 145091, 145109, 145121, 145133, 145139, 145177, 145193, 145207, 145213,
  145219, 145253, 145259, 145267, 145283, 145289, 145303, 145307, 145349, 145361, 145381, 145391, 145399, 145417, 145423, 145433,
  145441, 145451, 145459, 145463, 145471, 145477, 145487, 145501, 145511, 145513, 145517, 145531, 145543, 145547, 145549, 145577,
  145589, 145601, 145603, 145633, 145637, 145643, 145661, 145679, 145681, 145687, 145703, 145709, 145721, 145723, 145753, 145757,
  145759, 145771, 145777, 145799, 145807, 145819, 145823, 145829, 145861, 145879, 145897, 145903, 145931, 145933, 145949, 145963,
  145967, 145969, 145987, 145991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock73 : List ℕ := [
  146009, 146011, 146021, 146023, 146033, 146051, 146057, 146059, 146063, 146077, 146093, 146099, 146117, 146141, 146161, 146173,
  146191, 146197, 146203, 146213, 146221, 146239, 146249, 146273, 146291, 146297, 146299, 146309, 146317, 146323, 146347, 146359,
  146369, 146381, 146383, 146389, 146407, 146417, 146423, 146437, 146449, 146477, 146513, 146519, 146521, 146527, 146539, 146543,
  146563, 146581, 146603, 146609, 146617, 146639, 146647, 146669, 146677, 146681, 146683, 146701, 146719, 146743, 146749, 146767,
  146777, 146801, 146807, 146819, 146833, 146837, 146843, 146849, 146857, 146891, 146893, 146917, 146921, 146933, 146941, 146953,
  146977, 146983, 146987, 146989, 147011, 147029, 147031, 147047, 147073, 147083, 147089, 147097, 147107, 147137, 147139, 147151,
  147163, 147179, 147197, 147209, 147211, 147221, 147227, 147229, 147253, 147263, 147283, 147289, 147293, 147299, 147311, 147319,
  147331, 147341, 147347, 147353, 147377, 147391, 147397, 147401, 147409, 147419, 147449, 147451, 147457, 147481, 147487, 147503,
  147517, 147541, 147547, 147551, 147557, 147571, 147583, 147607, 147613, 147617, 147629, 147647, 147661, 147671, 147673, 147689,
  147703, 147709, 147727, 147739, 147743, 147761, 147769, 147773, 147779, 147787, 147793, 147799, 147811, 147827, 147853, 147859,
  147863, 147881, 147919, 147937, 147949, 147977, 147997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock74 : List ℕ := [
  148013, 148021, 148061, 148063, 148073, 148079, 148091, 148123, 148139, 148147, 148151, 148153, 148157, 148171, 148193, 148199,
  148201, 148207, 148229, 148243, 148249, 148279, 148301, 148303, 148331, 148339, 148361, 148367, 148381, 148387, 148399, 148403,
  148411, 148429, 148439, 148457, 148469, 148471, 148483, 148501, 148513, 148517, 148531, 148537, 148549, 148573, 148579, 148609,
  148627, 148633, 148639, 148663, 148667, 148669, 148691, 148693, 148711, 148721, 148723, 148727, 148747, 148763, 148781, 148783,
  148793, 148817, 148829, 148853, 148859, 148861, 148867, 148873, 148891, 148913, 148921, 148927, 148931, 148933, 148949, 148957,
  148961, 148991, 148997, 149011, 149021, 149027, 149033, 149053, 149057, 149059, 149069, 149077, 149087, 149099, 149101, 149111,
  149113, 149119, 149143, 149153, 149159, 149161, 149173, 149183, 149197, 149213, 149239, 149249, 149251, 149257, 149269, 149287,
  149297, 149309, 149323, 149333, 149341, 149351, 149371, 149377, 149381, 149393, 149399, 149411, 149417, 149419, 149423, 149441,
  149459, 149489, 149491, 149497, 149503, 149519, 149521, 149531, 149533, 149543, 149551, 149561, 149563, 149579, 149603, 149623,
  149627, 149629, 149689, 149711, 149713, 149717, 149729, 149731, 149749, 149759, 149767, 149771, 149791, 149803, 149827, 149837,
  149839, 149861, 149867, 149873, 149893, 149899, 149909, 149911, 149921, 149939, 149953, 149969, 149971, 149993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock75 : List ℕ := [
  150001, 150011, 150041, 150053, 150061, 150067, 150077, 150083, 150089, 150091, 150097, 150107, 150131, 150151, 150169, 150193,
  150197, 150203, 150209, 150211, 150217, 150221, 150223, 150239, 150247, 150287, 150299, 150301, 150323, 150329, 150343, 150373,
  150377, 150379, 150383, 150401, 150407, 150413, 150427, 150431, 150439, 150473, 150497, 150503, 150517, 150523, 150533, 150551,
  150559, 150571, 150583, 150587, 150589, 150607, 150611, 150617, 150649, 150659, 150697, 150707, 150721, 150743, 150767, 150769,
  150779, 150791, 150797, 150827, 150833, 150847, 150869, 150881, 150883, 150889, 150893, 150901, 150907, 150919, 150929, 150959,
  150961, 150967, 150979, 150989, 150991, 151007, 151009, 151013, 151027, 151049, 151051, 151057, 151091, 151121, 151141, 151153,
  151157, 151163, 151169, 151171, 151189, 151201, 151213, 151237, 151241, 151243, 151247, 151253, 151273, 151279, 151289, 151303,
  151337, 151339, 151343, 151357, 151379, 151381, 151391, 151397, 151423, 151429, 151433, 151451, 151471, 151477, 151483, 151499,
  151507, 151517, 151523, 151531, 151537, 151549, 151553, 151561, 151573, 151579, 151597, 151603, 151607, 151609, 151631, 151637,
  151643, 151651, 151667, 151673, 151681, 151687, 151693, 151703, 151717, 151729, 151733, 151769, 151771, 151783, 151787, 151799,
  151813, 151817, 151841, 151847, 151849, 151871, 151883, 151897, 151901, 151903, 151909, 151937, 151939, 151967, 151969
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock76 : List ℕ := [
  152003, 152017, 152027, 152029, 152039, 152041, 152063, 152077, 152081, 152083, 152093, 152111, 152123, 152147, 152183, 152189,
  152197, 152203, 152213, 152219, 152231, 152239, 152249, 152267, 152287, 152293, 152297, 152311, 152363, 152377, 152381, 152389,
  152393, 152407, 152417, 152419, 152423, 152429, 152441, 152443, 152459, 152461, 152501, 152519, 152531, 152533, 152539, 152563,
  152567, 152597, 152599, 152617, 152623, 152629, 152639, 152641, 152657, 152671, 152681, 152717, 152723, 152729, 152753, 152767,
  152777, 152783, 152791, 152809, 152819, 152821, 152833, 152837, 152839, 152843, 152851, 152857, 152879, 152897, 152899, 152909,
  152939, 152941, 152947, 152953, 152959, 152981, 152989, 152993, 153001, 153059, 153067, 153071, 153073, 153077, 153089, 153107,
  153113, 153133, 153137, 153151, 153191, 153247, 153259, 153269, 153271, 153277, 153281, 153287, 153313, 153319, 153337, 153343,
  153353, 153359, 153371, 153379, 153407, 153409, 153421, 153427, 153437, 153443, 153449, 153457, 153469, 153487, 153499, 153509,
  153511, 153521, 153523, 153529, 153533, 153557, 153563, 153589, 153607, 153611, 153623, 153641, 153649, 153689, 153701, 153719,
  153733, 153739, 153743, 153749, 153757, 153763, 153817, 153841, 153871, 153877, 153887, 153889, 153911, 153913, 153929, 153941,
  153947, 153949, 153953, 153991, 153997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock77 : List ℕ := [
  154001, 154027, 154043, 154057, 154061, 154067, 154073, 154079, 154081, 154087, 154097, 154111, 154127, 154153, 154157, 154159,
  154181, 154183, 154211, 154213, 154229, 154243, 154247, 154267, 154277, 154279, 154291, 154303, 154313, 154321, 154333, 154339,
  154351, 154369, 154373, 154387, 154409, 154417, 154423, 154439, 154459, 154487, 154493, 154501, 154523, 154543, 154571, 154573,
  154579, 154589, 154591, 154613, 154619, 154621, 154643, 154667, 154669, 154681, 154691, 154699, 154723, 154727, 154733, 154747,
  154753, 154769, 154787, 154789, 154799, 154807, 154823, 154841, 154849, 154871, 154873, 154877, 154883, 154897, 154927, 154933,
  154937, 154943, 154981, 154991, 155003, 155009, 155017, 155027, 155047, 155069, 155081, 155083, 155087, 155119, 155137, 155153,
  155161, 155167, 155171, 155191, 155201, 155203, 155209, 155219, 155231, 155251, 155269, 155291, 155299, 155303, 155317, 155327,
  155333, 155371, 155377, 155381, 155383, 155387, 155399, 155413, 155423, 155443, 155453, 155461, 155473, 155501, 155509, 155521,
  155537, 155539, 155557, 155569, 155579, 155581, 155593, 155599, 155609, 155621, 155627, 155653, 155657, 155663, 155671, 155689,
  155693, 155699, 155707, 155717, 155719, 155723, 155731, 155741, 155747, 155773, 155777, 155783, 155797, 155801, 155809, 155821,
  155833, 155849, 155851, 155861, 155863, 155887, 155891, 155893, 155921
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock78 : List ℕ := [
  156007, 156011, 156019, 156041, 156059, 156061, 156071, 156089, 156109, 156119, 156127, 156131, 156139, 156151, 156157, 156217,
  156227, 156229, 156241, 156253, 156257, 156259, 156269, 156307, 156319, 156329, 156347, 156353, 156361, 156371, 156419, 156421,
  156437, 156467, 156487, 156491, 156493, 156511, 156521, 156539, 156577, 156589, 156593, 156601, 156619, 156623, 156631, 156641,
  156659, 156671, 156677, 156679, 156683, 156691, 156703, 156707, 156719, 156727, 156733, 156749, 156781, 156797, 156799, 156817,
  156823, 156833, 156841, 156887, 156899, 156901, 156913, 156941, 156943, 156967, 156971, 156979, 157007, 157013, 157019, 157037,
  157049, 157051, 157057, 157061, 157081, 157103, 157109, 157127, 157133, 157141, 157163, 157177, 157181, 157189, 157207, 157211,
  157217, 157219, 157229, 157231, 157243, 157247, 157253, 157259, 157271, 157273, 157277, 157279, 157291, 157303, 157307, 157321,
  157327, 157349, 157351, 157363, 157393, 157411, 157427, 157429, 157433, 157457, 157477, 157483, 157489, 157513, 157519, 157523,
  157543, 157559, 157561, 157571, 157579, 157627, 157637, 157639, 157649, 157667, 157669, 157679, 157721, 157733, 157739, 157747,
  157769, 157771, 157793, 157799, 157813, 157823, 157831, 157837, 157841, 157867, 157877, 157889, 157897, 157901, 157907, 157931,
  157933, 157951, 157991, 157999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock79 : List ℕ := [
  158003, 158009, 158017, 158029, 158047, 158071, 158077, 158113, 158129, 158141, 158143, 158161, 158189, 158201, 158209, 158227,
  158231, 158233, 158243, 158261, 158269, 158293, 158303, 158329, 158341, 158351, 158357, 158359, 158363, 158371, 158393, 158407,
  158419, 158429, 158443, 158449, 158489, 158507, 158519, 158527, 158537, 158551, 158563, 158567, 158573, 158581, 158591, 158597,
  158611, 158617, 158621, 158633, 158647, 158657, 158663, 158699, 158731, 158747, 158749, 158759, 158761, 158771, 158777, 158791,
  158803, 158843, 158849, 158863, 158867, 158881, 158909, 158923, 158927, 158941, 158959, 158981, 158993, 159013, 159017, 159023,
  159059, 159073, 159079, 159097, 159113, 159119, 159157, 159161, 159167, 159169, 159179, 159191, 159193, 159199, 159209, 159223,
  159227, 159233, 159287, 159293, 159311, 159319, 159337, 159347, 159349, 159361, 159389, 159403, 159407, 159421, 159431, 159437,
  159457, 159463, 159469, 159473, 159491, 159499, 159503, 159521, 159539, 159541, 159553, 159563, 159569, 159571, 159589, 159617,
  159623, 159629, 159631, 159667, 159671, 159673, 159683, 159697, 159701, 159707, 159721, 159737, 159739, 159763, 159769, 159773,
  159779, 159787, 159791, 159793, 159799, 159811, 159833, 159839, 159853, 159857, 159869, 159871, 159899, 159911, 159931, 159937,
  159977, 159979
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock80 : List ℕ := [
  160001, 160009, 160019, 160031, 160033, 160049, 160073, 160079, 160081, 160087, 160091, 160093, 160117, 160141, 160159, 160163,
  160169, 160183, 160201, 160207, 160217, 160231, 160243, 160253, 160309, 160313, 160319, 160343, 160357, 160367, 160373, 160387,
  160397, 160403, 160409, 160423, 160441, 160453, 160481, 160483, 160499, 160507, 160541, 160553, 160579, 160583, 160591, 160603,
  160619, 160621, 160627, 160637, 160639, 160649, 160651, 160663, 160669, 160681, 160687, 160697, 160709, 160711, 160723, 160739,
  160751, 160753, 160757, 160781, 160789, 160807, 160813, 160817, 160829, 160841, 160861, 160877, 160879, 160883, 160903, 160907,
  160933, 160967, 160969, 160981, 160997, 161009, 161017, 161033, 161039, 161047, 161053, 161059, 161071, 161087, 161093, 161123,
  161137, 161141, 161149, 161159, 161167, 161201, 161221, 161233, 161237, 161263, 161267, 161281, 161303, 161309, 161323, 161333,
  161339, 161341, 161363, 161377, 161387, 161407, 161411, 161453, 161459, 161461, 161471, 161503, 161507, 161521, 161527, 161531,
  161543, 161561, 161563, 161569, 161573, 161591, 161599, 161611, 161627, 161639, 161641, 161659, 161683, 161717, 161729, 161731,
  161741, 161743, 161753, 161761, 161771, 161773, 161779, 161783, 161807, 161831, 161839, 161869, 161873, 161879, 161881, 161911,
  161921, 161923, 161947, 161957, 161969, 161971, 161977, 161983, 161999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock81 : List ℕ := [
  162007, 162011, 162017, 162053, 162059, 162079, 162091, 162109, 162119, 162143, 162209, 162221, 162229, 162251, 162257, 162263,
  162269, 162277, 162287, 162289, 162293, 162343, 162359, 162389, 162391, 162413, 162419, 162439, 162451, 162457, 162473, 162493,
  162499, 162517, 162523, 162527, 162529, 162553, 162557, 162563, 162577, 162593, 162601, 162611, 162623, 162629, 162641, 162649,
  162671, 162677, 162683, 162691, 162703, 162709, 162713, 162727, 162731, 162739, 162749, 162751, 162779, 162787, 162791, 162821,
  162823, 162829, 162839, 162847, 162853, 162859, 162881, 162889, 162901, 162907, 162917, 162937, 162947, 162971, 162973, 162989,
  162997, 163003, 163019, 163021, 163027, 163061, 163063, 163109, 163117, 163127, 163129, 163147, 163151, 163169, 163171, 163181,
  163193, 163199, 163211, 163223, 163243, 163249, 163259, 163307, 163309, 163321, 163327, 163337, 163351, 163363, 163367, 163393,
  163403, 163409, 163411, 163417, 163433, 163469, 163477, 163481, 163483, 163487, 163517, 163543, 163561, 163567, 163573, 163601,
  163613, 163621, 163627, 163633, 163637, 163643, 163661, 163673, 163679, 163697, 163729, 163733, 163741, 163753, 163771, 163781,
  163789, 163811, 163819, 163841, 163847, 163853, 163859, 163861, 163871, 163883, 163901, 163909, 163927, 163973, 163979, 163981,
  163987, 163991, 163993, 163997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock82 : List ℕ := [
  164011, 164023, 164039, 164051, 164057, 164071, 164089, 164093, 164113, 164117, 164147, 164149, 164173, 164183, 164191, 164201,
  164209, 164231, 164233, 164239, 164249, 164251, 164267, 164279, 164291, 164299, 164309, 164321, 164341, 164357, 164363, 164371,
  164377, 164387, 164413, 164419, 164429, 164431, 164443, 164447, 164449, 164471, 164477, 164503, 164513, 164531, 164569, 164581,
  164587, 164599, 164617, 164621, 164623, 164627, 164653, 164663, 164677, 164683, 164701, 164707, 164729, 164743, 164767, 164771,
  164789, 164809, 164821, 164831, 164837, 164839, 164881, 164893, 164911, 164953, 164963, 164987, 164999, 165001, 165037, 165041,
  165047, 165049, 165059, 165079, 165083, 165089, 165103, 165133, 165161, 165173, 165181, 165203, 165211, 165229, 165233, 165247,
  165287, 165293, 165311, 165313, 165317, 165331, 165343, 165349, 165367, 165379, 165383, 165391, 165397, 165437, 165443, 165449,
  165457, 165463, 165469, 165479, 165511, 165523, 165527, 165533, 165541, 165551, 165553, 165559, 165569, 165587, 165589, 165601,
  165611, 165617, 165653, 165667, 165673, 165701, 165703, 165707, 165709, 165713, 165719, 165721, 165749, 165779, 165799, 165811,
  165817, 165829, 165833, 165857, 165877, 165883, 165887, 165901, 165931, 165941, 165947, 165961, 165983
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock83 : List ℕ := [
  166013, 166021, 166027, 166031, 166043, 166063, 166081, 166099, 166147, 166151, 166157, 166169, 166183, 166189, 166207, 166219,
  166237, 166247, 166259, 166273, 166289, 166297, 166301, 166303, 166319, 166349, 166351, 166357, 166363, 166393, 166399, 166403,
  166409, 166417, 166429, 166457, 166471, 166487, 166541, 166561, 166567, 166571, 166597, 166601, 166603, 166609, 166613, 166619,
  166627, 166631, 166643, 166657, 166667, 166669, 166679, 166693, 166703, 166723, 166739, 166741, 166781, 166783, 166799, 166807,
  166823, 166841, 166843, 166847, 166849, 166853, 166861, 166867, 166871, 166909, 166919, 166931, 166949, 166967, 166973, 166979,
  166987, 167009, 167017, 167021, 167023, 167033, 167039, 167047, 167051, 167071, 167077, 167081, 167087, 167099, 167107, 167113,
  167117, 167119, 167149, 167159, 167173, 167177, 167191, 167197, 167213, 167221, 167249, 167261, 167267, 167269, 167309, 167311,
  167317, 167329, 167339, 167341, 167381, 167393, 167407, 167413, 167423, 167429, 167437, 167441, 167443, 167449, 167471, 167483,
  167491, 167521, 167537, 167543, 167593, 167597, 167611, 167621, 167623, 167627, 167633, 167641, 167663, 167677, 167683, 167711,
  167729, 167747, 167759, 167771, 167777, 167779, 167801, 167809, 167861, 167863, 167873, 167879, 167887, 167891, 167899, 167911,
  167917, 167953, 167971, 167987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock84 : List ℕ := [
  168013, 168023, 168029, 168037, 168043, 168067, 168071, 168083, 168089, 168109, 168127, 168143, 168151, 168193, 168197, 168211,
  168227, 168247, 168253, 168263, 168269, 168277, 168281, 168293, 168323, 168331, 168347, 168353, 168391, 168409, 168433, 168449,
  168451, 168457, 168463, 168481, 168491, 168499, 168523, 168527, 168533, 168541, 168559, 168599, 168601, 168617, 168629, 168631,
  168643, 168673, 168677, 168697, 168713, 168719, 168731, 168737, 168743, 168761, 168769, 168781, 168803, 168851, 168863, 168869,
  168887, 168893, 168899, 168901, 168913, 168937, 168943, 168977, 168991, 169003, 169007, 169009, 169019, 169049, 169063, 169067,
  169069, 169079, 169093, 169097, 169111, 169129, 169151, 169159, 169177, 169181, 169199, 169217, 169219, 169241, 169243, 169249,
  169259, 169283, 169307, 169313, 169319, 169321, 169327, 169339, 169343, 169361, 169369, 169373, 169399, 169409, 169427, 169457,
  169471, 169483, 169489, 169493, 169501, 169523, 169531, 169553, 169567, 169583, 169591, 169607, 169627, 169633, 169639, 169649,
  169657, 169661, 169667, 169681, 169691, 169693, 169709, 169733, 169751, 169753, 169769, 169777, 169783, 169789, 169817, 169823,
  169831, 169837, 169843, 169859, 169889, 169891, 169909, 169913, 169919, 169933, 169937, 169943, 169951, 169957, 169987, 169991
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock85 : List ℕ := [
  170003, 170021, 170029, 170047, 170057, 170063, 170081, 170099, 170101, 170111, 170123, 170141, 170167, 170179, 170189, 170197,
  170207, 170213, 170227, 170231, 170239, 170243, 170249, 170263, 170267, 170279, 170293, 170299, 170327, 170341, 170347, 170351,
  170353, 170363, 170369, 170371, 170383, 170389, 170393, 170413, 170441, 170447, 170473, 170483, 170497, 170503, 170509, 170537,
  170539, 170551, 170557, 170579, 170603, 170609, 170627, 170633, 170641, 170647, 170669, 170689, 170701, 170707, 170711, 170741,
  170749, 170759, 170761, 170767, 170773, 170777, 170801, 170809, 170813, 170827, 170837, 170843, 170851, 170857, 170873, 170881,
  170887, 170899, 170921, 170927, 170953, 170957, 170971, 171007, 171023, 171029, 171043, 171047, 171049, 171053, 171077, 171079,
  171091, 171103, 171131, 171161, 171163, 171167, 171169, 171179, 171203, 171233, 171251, 171253, 171263, 171271, 171293, 171299,
  171317, 171329, 171341, 171383, 171401, 171403, 171427, 171439, 171449, 171467, 171469, 171473, 171481, 171491, 171517, 171529,
  171539, 171541, 171553, 171559, 171571, 171583, 171617, 171629, 171637, 171641, 171653, 171659, 171671, 171673, 171679, 171697,
  171707, 171713, 171719, 171733, 171757, 171761, 171763, 171793, 171799, 171803, 171811, 171823, 171827, 171851, 171863, 171869,
  171877, 171881, 171889, 171917, 171923, 171929, 171937, 171947
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock86 : List ℕ := [
  172001, 172009, 172021, 172027, 172031, 172049, 172069, 172079, 172093, 172097, 172127, 172147, 172153, 172157, 172169, 172171,
  172181, 172199, 172213, 172217, 172219, 172223, 172243, 172259, 172279, 172283, 172297, 172307, 172313, 172321, 172331, 172343,
  172351, 172357, 172373, 172399, 172411, 172421, 172423, 172427, 172433, 172439, 172441, 172489, 172507, 172517, 172519, 172541,
  172553, 172561, 172573, 172583, 172589, 172597, 172603, 172607, 172619, 172633, 172643, 172649, 172657, 172663, 172673, 172681,
  172687, 172709, 172717, 172721, 172741, 172751, 172759, 172787, 172801, 172807, 172829, 172849, 172853, 172859, 172867, 172871,
  172877, 172883, 172933, 172969, 172973, 172981, 172987, 172993, 172999, 173021, 173023, 173039, 173053, 173059, 173081, 173087,
  173099, 173137, 173141, 173149, 173177, 173183, 173189, 173191, 173207, 173209, 173219, 173249, 173263, 173267, 173273, 173291,
  173293, 173297, 173309, 173347, 173357, 173359, 173429, 173431, 173473, 173483, 173491, 173497, 173501, 173531, 173539, 173543,
  173549, 173561, 173573, 173599, 173617, 173629, 173647, 173651, 173659, 173669, 173671, 173683, 173687, 173699, 173707, 173713,
  173729, 173741, 173743, 173773, 173777, 173779, 173783, 173807, 173819, 173827, 173839, 173851, 173861, 173867, 173891, 173897,
  173909, 173917, 173923, 173933, 173969, 173977, 173981, 173993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock87 : List ℕ := [
  174007, 174017, 174019, 174047, 174049, 174061, 174067, 174071, 174077, 174079, 174091, 174101, 174121, 174137, 174143, 174149,
  174157, 174169, 174197, 174221, 174241, 174257, 174259, 174263, 174281, 174289, 174299, 174311, 174329, 174331, 174337, 174347,
  174367, 174389, 174407, 174413, 174431, 174443, 174457, 174467, 174469, 174481, 174487, 174491, 174527, 174533, 174569, 174571,
  174583, 174599, 174613, 174617, 174631, 174637, 174649, 174653, 174659, 174673, 174679, 174703, 174721, 174737, 174749, 174761,
  174763, 174767, 174773, 174799, 174821, 174829, 174851, 174859, 174877, 174893, 174901, 174907, 174917, 174929, 174931, 174943,
  174959, 174989, 174991, 175003, 175013, 175039, 175061, 175067, 175069, 175079, 175081, 175103, 175129, 175141, 175211, 175229,
  175261, 175267, 175277, 175291, 175303, 175309, 175327, 175333, 175349, 175361, 175391, 175393, 175403, 175411, 175433, 175447,
  175453, 175463, 175481, 175493, 175499, 175519, 175523, 175543, 175573, 175601, 175621, 175631, 175633, 175649, 175663, 175673,
  175687, 175691, 175699, 175709, 175723, 175727, 175753, 175757, 175759, 175781, 175783, 175811, 175829, 175837, 175843, 175853,
  175859, 175873, 175891, 175897, 175909, 175919, 175937, 175939, 175949, 175961, 175963, 175979, 175991, 175993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock88 : List ℕ := [
  176017, 176021, 176023, 176041, 176047, 176051, 176053, 176063, 176081, 176087, 176089, 176123, 176129, 176153, 176159, 176161,
  176179, 176191, 176201, 176207, 176213, 176221, 176227, 176237, 176243, 176261, 176299, 176303, 176317, 176321, 176327, 176329,
  176333, 176347, 176353, 176357, 176369, 176383, 176389, 176401, 176413, 176417, 176419, 176431, 176459, 176461, 176467, 176489,
  176497, 176503, 176507, 176509, 176521, 176531, 176537, 176549, 176551, 176557, 176573, 176591, 176597, 176599, 176609, 176611,
  176629, 176641, 176651, 176677, 176699, 176711, 176713, 176741, 176747, 176753, 176777, 176779, 176789, 176791, 176797, 176807,
  176809, 176819, 176849, 176857, 176887, 176899, 176903, 176921, 176923, 176927, 176933, 176951, 176977, 176983, 176989, 177007,
  177011, 177013, 177019, 177043, 177091, 177101, 177109, 177113, 177127, 177131, 177167, 177173, 177209, 177211, 177217, 177223,
  177239, 177257, 177269, 177283, 177301, 177319, 177323, 177337, 177347, 177379, 177383, 177409, 177421, 177427, 177431, 177433,
  177467, 177473, 177481, 177487, 177493, 177511, 177533, 177539, 177553, 177589, 177601, 177623, 177647, 177677, 177679, 177691,
  177739, 177743, 177761, 177763, 177787, 177791, 177797, 177811, 177823, 177839, 177841, 177883, 177887, 177889, 177893, 177907,
  177913, 177917, 177929, 177943, 177949, 177953, 177967, 177979
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock89 : List ℕ := [
  178001, 178021, 178037, 178039, 178067, 178069, 178091, 178093, 178103, 178117, 178127, 178141, 178151, 178169, 178183, 178187,
  178207, 178223, 178231, 178247, 178249, 178259, 178261, 178289, 178301, 178307, 178327, 178333, 178349, 178351, 178361, 178393,
  178397, 178403, 178417, 178439, 178441, 178447, 178469, 178481, 178487, 178489, 178501, 178513, 178531, 178537, 178559, 178561,
  178567, 178571, 178597, 178601, 178603, 178609, 178613, 178621, 178627, 178639, 178643, 178681, 178691, 178693, 178697, 178753,
  178757, 178781, 178793, 178799, 178807, 178813, 178817, 178819, 178831, 178853, 178859, 178873, 178877, 178889, 178897, 178903,
  178907, 178909, 178921, 178931, 178933, 178939, 178951, 178973, 178987, 179021, 179029, 179033, 179041, 179051, 179057, 179083,
  179089, 179099, 179107, 179111, 179119, 179143, 179161, 179167, 179173, 179203, 179209, 179213, 179233, 179243, 179261, 179269,
  179281, 179287, 179317, 179321, 179327, 179351, 179357, 179369, 179381, 179383, 179393, 179407, 179411, 179429, 179437, 179441,
  179453, 179461, 179471, 179479, 179483, 179497, 179519, 179527, 179533, 179549, 179563, 179573, 179579, 179581, 179591, 179593,
  179603, 179623, 179633, 179651, 179657, 179659, 179671, 179687, 179689, 179693, 179717, 179719, 179737, 179743, 179749, 179779,
  179801, 179807, 179813, 179819, 179821, 179827, 179833, 179849, 179897, 179899, 179903, 179909, 179917, 179923, 179939, 179947,
  179951, 179953, 179957, 179969, 179981, 179989, 179999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock90 : List ℕ := [
  180001, 180007, 180023, 180043, 180053, 180071, 180073, 180077, 180097, 180137, 180161, 180179, 180181, 180211, 180221, 180233,
  180239, 180241, 180247, 180259, 180263, 180281, 180287, 180289, 180307, 180311, 180317, 180331, 180337, 180347, 180361, 180371,
  180379, 180391, 180413, 180419, 180437, 180463, 180473, 180491, 180497, 180503, 180511, 180533, 180539, 180541, 180547, 180563,
  180569, 180617, 180623, 180629, 180647, 180667, 180679, 180701, 180731, 180749, 180751, 180773, 180779, 180793, 180797, 180799,
  180811, 180847, 180871, 180883, 180907, 180949, 180959, 181001, 181003, 181019, 181031, 181039, 181061, 181063, 181081, 181087,
  181123, 181141, 181157, 181183, 181193, 181199, 181201, 181211, 181213, 181219, 181243, 181253, 181273, 181277, 181283, 181297,
  181301, 181303, 181361, 181387, 181397, 181399, 181409, 181421, 181439, 181457, 181459, 181499, 181501, 181513, 181523, 181537,
  181549, 181553, 181603, 181607, 181609, 181619, 181639, 181667, 181669, 181693, 181711, 181717, 181721, 181729, 181739, 181751,
  181757, 181759, 181763, 181777, 181787, 181789, 181813, 181837, 181871, 181873, 181889, 181891, 181903, 181913, 181919, 181927,
  181931, 181943, 181957, 181967, 181981, 181997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock91 : List ℕ := [
  182009, 182011, 182027, 182029, 182041, 182047, 182057, 182059, 182089, 182099, 182101, 182107, 182111, 182123, 182129, 182131,
  182141, 182159, 182167, 182177, 182179, 182201, 182209, 182233, 182239, 182243, 182261, 182279, 182297, 182309, 182333, 182339,
  182341, 182353, 182387, 182389, 182417, 182423, 182431, 182443, 182453, 182467, 182471, 182473, 182489, 182503, 182509, 182519,
  182537, 182549, 182561, 182579, 182587, 182593, 182599, 182603, 182617, 182627, 182639, 182641, 182653, 182657, 182659, 182681,
  182687, 182701, 182711, 182713, 182747, 182773, 182779, 182789, 182803, 182813, 182821, 182839, 182851, 182857, 182867, 182887,
  182893, 182899, 182921, 182927, 182929, 182933, 182953, 182957, 182969, 182981, 182999, 183023, 183037, 183041, 183047, 183059,
  183067, 183089, 183091, 183119, 183151, 183167, 183191, 183203, 183247, 183259, 183263, 183283, 183289, 183299, 183301, 183307,
  183317, 183319, 183329, 183343, 183349, 183361, 183373, 183377, 183383, 183389, 183397, 183437, 183439, 183451, 183461, 183473,
  183479, 183487, 183497, 183499, 183503, 183509, 183511, 183523, 183527, 183569, 183571, 183577, 183581, 183587, 183593, 183611,
  183637, 183661, 183683, 183691, 183697, 183707, 183709, 183713, 183761, 183763, 183797, 183809, 183823, 183829, 183871, 183877,
  183881, 183907, 183917, 183919, 183943, 183949, 183959, 183971, 183973, 183979
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock92 : List ℕ := [
  184003, 184007, 184013, 184031, 184039, 184043, 184057, 184073, 184081, 184087, 184111, 184117, 184133, 184153, 184157, 184181,
  184187, 184189, 184199, 184211, 184231, 184241, 184259, 184271, 184273, 184279, 184291, 184309, 184321, 184333, 184337, 184351,
  184369, 184409, 184417, 184441, 184447, 184463, 184477, 184487, 184489, 184511, 184517, 184523, 184553, 184559, 184567, 184571,
  184577, 184607, 184609, 184627, 184631, 184633, 184649, 184651, 184669, 184687, 184693, 184703, 184711, 184721, 184727, 184733,
  184753, 184777, 184823, 184829, 184831, 184837, 184843, 184859, 184879, 184901, 184903, 184913, 184949, 184957, 184967, 184969,
  184993, 184997, 184999, 185021, 185027, 185051, 185057, 185063, 185069, 185071, 185077, 185089, 185099, 185123, 185131, 185137,
  185149, 185153, 185161, 185167, 185177, 185183, 185189, 185221, 185233, 185243, 185267, 185291, 185299, 185303, 185309, 185323,
  185327, 185359, 185363, 185369, 185371, 185401, 185429, 185441, 185467, 185477, 185483, 185491, 185519, 185527, 185531, 185533,
  185539, 185543, 185551, 185557, 185567, 185569, 185593, 185599, 185621, 185641, 185651, 185677, 185681, 185683, 185693, 185699,
  185707, 185711, 185723, 185737, 185747, 185749, 185753, 185767, 185789, 185797, 185813, 185819, 185821, 185831, 185833, 185849,
  185869, 185873, 185893, 185897, 185903, 185917, 185923, 185947, 185951, 185957, 185959, 185971, 185987, 185993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock93 : List ℕ := [
  186007, 186013, 186019, 186023, 186037, 186041, 186049, 186071, 186097, 186103, 186107, 186113, 186119, 186149, 186157, 186161,
  186163, 186187, 186191, 186211, 186227, 186229, 186239, 186247, 186253, 186259, 186271, 186283, 186299, 186301, 186311, 186317,
  186343, 186377, 186379, 186391, 186397, 186419, 186437, 186451, 186469, 186479, 186481, 186551, 186569, 186581, 186583, 186587,
  186601, 186619, 186629, 186647, 186649, 186653, 186671, 186679, 186689, 186701, 186707, 186709, 186727, 186733, 186743, 186757,
  186761, 186763, 186773, 186793, 186799, 186841, 186859, 186869, 186871, 186877, 186883, 186889, 186917, 186947, 186959, 187003,
  187009, 187027, 187043, 187049, 187067, 187069, 187073, 187081, 187091, 187111, 187123, 187127, 187129, 187133, 187139, 187141,
  187163, 187171, 187177, 187181, 187189, 187193, 187211, 187217, 187219, 187223, 187237, 187273, 187277, 187303, 187337, 187339,
  187349, 187361, 187367, 187373, 187379, 187387, 187393, 187409, 187417, 187423, 187433, 187441, 187463, 187469, 187471, 187477,
  187507, 187513, 187531, 187547, 187559, 187573, 187597, 187631, 187633, 187637, 187639, 187651, 187661, 187669, 187687, 187699,
  187711, 187721, 187751, 187763, 187787, 187793, 187823, 187843, 187861, 187871, 187877, 187883, 187897, 187907, 187909, 187921,
  187927, 187931, 187951, 187963, 187973, 187987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock94 : List ℕ := [
  188011, 188017, 188021, 188029, 188107, 188137, 188143, 188147, 188159, 188171, 188179, 188189, 188197, 188249, 188261, 188273,
  188281, 188291, 188299, 188303, 188311, 188317, 188323, 188333, 188351, 188359, 188369, 188389, 188401, 188407, 188417, 188431,
  188437, 188443, 188459, 188473, 188483, 188491, 188519, 188527, 188533, 188563, 188579, 188603, 188609, 188621, 188633, 188653,
  188677, 188681, 188687, 188693, 188701, 188707, 188711, 188719, 188729, 188753, 188767, 188779, 188791, 188801, 188827, 188831,
  188833, 188843, 188857, 188861, 188863, 188869, 188891, 188911, 188927, 188933, 188939, 188941, 188953, 188957, 188983, 188999,
  189011, 189017, 189019, 189041, 189043, 189061, 189067, 189127, 189139, 189149, 189151, 189169, 189187, 189199, 189223, 189229,
  189239, 189251, 189253, 189257, 189271, 189307, 189311, 189337, 189347, 189349, 189353, 189361, 189377, 189389, 189391, 189401,
  189407, 189421, 189433, 189437, 189439, 189463, 189467, 189473, 189479, 189491, 189493, 189509, 189517, 189523, 189529, 189547,
  189559, 189583, 189593, 189599, 189613, 189617, 189619, 189643, 189653, 189661, 189671, 189691, 189697, 189701, 189713, 189733,
  189743, 189757, 189767, 189797, 189799, 189817, 189823, 189851, 189853, 189859, 189877, 189881, 189887, 189901, 189913, 189929,
  189947, 189949, 189961, 189967, 189977, 189983, 189989, 189997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock95 : List ℕ := [
  190027, 190031, 190051, 190063, 190093, 190097, 190121, 190129, 190147, 190159, 190181, 190207, 190243, 190249, 190261, 190271,
  190283, 190297, 190301, 190313, 190321, 190331, 190339, 190357, 190367, 190369, 190387, 190391, 190403, 190409, 190471, 190507,
  190523, 190529, 190537, 190543, 190573, 190577, 190579, 190583, 190591, 190607, 190613, 190633, 190639, 190649, 190657, 190667,
  190669, 190699, 190709, 190711, 190717, 190753, 190759, 190763, 190769, 190783, 190787, 190793, 190807, 190811, 190823, 190829,
  190837, 190843, 190871, 190889, 190891, 190901, 190909, 190913, 190921, 190979, 190997, 191021, 191027, 191033, 191039, 191047,
  191057, 191071, 191089, 191099, 191119, 191123, 191137, 191141, 191143, 191161, 191173, 191189, 191227, 191231, 191237, 191249,
  191251, 191281, 191297, 191299, 191339, 191341, 191353, 191413, 191441, 191447, 191449, 191453, 191459, 191461, 191467, 191473,
  191491, 191497, 191507, 191509, 191519, 191531, 191533, 191537, 191551, 191561, 191563, 191579, 191599, 191621, 191627, 191657,
  191669, 191671, 191677, 191689, 191693, 191699, 191707, 191717, 191747, 191749, 191773, 191783, 191791, 191801, 191803, 191827,
  191831, 191833, 191837, 191861, 191899, 191903, 191911, 191929, 191953, 191969, 191977, 191999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock96 : List ℕ := [
  192007, 192013, 192029, 192037, 192043, 192047, 192053, 192091, 192097, 192103, 192113, 192121, 192133, 192149, 192161, 192173,
  192187, 192191, 192193, 192229, 192233, 192239, 192251, 192259, 192263, 192271, 192307, 192317, 192319, 192323, 192341, 192343,
  192347, 192373, 192377, 192383, 192391, 192407, 192431, 192461, 192463, 192497, 192499, 192529, 192539, 192547, 192553, 192557,
  192571, 192581, 192583, 192587, 192601, 192611, 192613, 192617, 192629, 192631, 192637, 192667, 192677, 192697, 192737, 192743,
  192749, 192757, 192767, 192781, 192791, 192799, 192811, 192817, 192833, 192847, 192853, 192859, 192877, 192883, 192887, 192889,
  192917, 192923, 192931, 192949, 192961, 192971, 192977, 192979, 192991, 193003, 193009, 193013, 193031, 193043, 193051, 193057,
  193073, 193093, 193133, 193139, 193147, 193153, 193163, 193181, 193183, 193189, 193201, 193243, 193247, 193261, 193283, 193301,
  193327, 193337, 193357, 193367, 193373, 193379, 193381, 193387, 193393, 193423, 193433, 193441, 193447, 193451, 193463, 193469,
  193493, 193507, 193513, 193541, 193549, 193559, 193573, 193577, 193597, 193601, 193603, 193607, 193619, 193649, 193663, 193679,
  193703, 193723, 193727, 193741, 193751, 193757, 193763, 193771, 193789, 193793, 193799, 193811, 193813, 193841, 193847, 193859,
  193861, 193871, 193873, 193877, 193883, 193891, 193937, 193939, 193943, 193951, 193957, 193979, 193993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock97 : List ℕ := [
  194003, 194017, 194027, 194057, 194069, 194071, 194083, 194087, 194093, 194101, 194113, 194119, 194141, 194149, 194167, 194179,
  194197, 194203, 194239, 194263, 194267, 194269, 194309, 194323, 194353, 194371, 194377, 194413, 194431, 194443, 194471, 194479,
  194483, 194507, 194521, 194527, 194543, 194569, 194581, 194591, 194609, 194647, 194653, 194659, 194671, 194681, 194683, 194687,
  194707, 194713, 194717, 194723, 194729, 194749, 194767, 194771, 194809, 194813, 194819, 194827, 194839, 194861, 194863, 194867,
  194869, 194891, 194899, 194911, 194917, 194933, 194963, 194977, 194981, 194989, 195023, 195029, 195043, 195047, 195049, 195053,
  195071, 195077, 195089, 195103, 195121, 195127, 195131, 195137, 195157, 195161, 195163, 195193, 195197, 195203, 195229, 195241,
  195253, 195259, 195271, 195277, 195281, 195311, 195319, 195329, 195341, 195343, 195353, 195359, 195389, 195401, 195407, 195413,
  195427, 195443, 195457, 195469, 195479, 195493, 195497, 195511, 195527, 195539, 195541, 195581, 195593, 195599, 195659, 195677,
  195691, 195697, 195709, 195731, 195733, 195737, 195739, 195743, 195751, 195761, 195781, 195787, 195791, 195809, 195817, 195863,
  195869, 195883, 195887, 195893, 195907, 195913, 195919, 195929, 195931, 195967, 195971, 195973, 195977, 195991, 195997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock98 : List ℕ := [
  196003, 196033, 196039, 196043, 196051, 196073, 196081, 196087, 196111, 196117, 196139, 196159, 196169, 196171, 196177, 196181,
  196187, 196193, 196201, 196247, 196271, 196277, 196279, 196291, 196303, 196307, 196331, 196337, 196379, 196387, 196429, 196439,
  196453, 196459, 196477, 196499, 196501, 196519, 196523, 196541, 196543, 196549, 196561, 196579, 196583, 196597, 196613, 196643,
  196657, 196661, 196663, 196681, 196687, 196699, 196709, 196717, 196727, 196739, 196751, 196769, 196771, 196799, 196817, 196831,
  196837, 196853, 196871, 196873, 196879, 196901, 196907, 196919, 196927, 196961, 196991, 196993, 197003, 197009, 197023, 197033,
  197059, 197063, 197077, 197083, 197089, 197101, 197117, 197123, 197137, 197147, 197159, 197161, 197203, 197207, 197221, 197233,
  197243, 197257, 197261, 197269, 197273, 197279, 197293, 197297, 197299, 197311, 197339, 197341, 197347, 197359, 197369, 197371,
  197381, 197383, 197389, 197419, 197423, 197441, 197453, 197479, 197507, 197521, 197539, 197551, 197567, 197569, 197573, 197597,
  197599, 197609, 197621, 197641, 197647, 197651, 197677, 197683, 197689, 197699, 197711, 197713, 197741, 197753, 197759, 197767,
  197773, 197779, 197803, 197807, 197831, 197837, 197887, 197891, 197893, 197909, 197921, 197927, 197933, 197947, 197957, 197959,
  197963, 197969, 197971
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock99 : List ℕ := [
  198013, 198017, 198031, 198043, 198047, 198073, 198083, 198091, 198097, 198109, 198127, 198139, 198173, 198179, 198193, 198197,
  198221, 198223, 198241, 198251, 198257, 198259, 198277, 198281, 198301, 198313, 198323, 198337, 198347, 198349, 198377, 198391,
  198397, 198409, 198413, 198427, 198437, 198439, 198461, 198463, 198469, 198479, 198491, 198503, 198529, 198533, 198553, 198571,
  198589, 198593, 198599, 198613, 198623, 198637, 198641, 198647, 198659, 198673, 198689, 198701, 198719, 198733, 198761, 198769,
  198811, 198817, 198823, 198827, 198829, 198833, 198839, 198841, 198851, 198859, 198899, 198901, 198929, 198937, 198941, 198943,
  198953, 198959, 198967, 198971, 198977, 198997, 199021, 199033, 199037, 199039, 199049, 199081, 199103, 199109, 199151, 199153,
  199181, 199193, 199207, 199211, 199247, 199261, 199267, 199289, 199313, 199321, 199337, 199343, 199357, 199373, 199379, 199399,
  199403, 199411, 199417, 199429, 199447, 199453, 199457, 199483, 199487, 199489, 199499, 199501, 199523, 199559, 199567, 199583,
  199601, 199603, 199621, 199637, 199657, 199669, 199673, 199679, 199687, 199697, 199721, 199729, 199739, 199741, 199751, 199753,
  199777, 199783, 199799, 199807, 199811, 199813, 199819, 199831, 199853, 199873, 199877, 199889, 199909, 199921, 199931, 199933,
  199961, 199967, 199999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock100 : List ℕ := [
  200003, 200009, 200017, 200023, 200029, 200033, 200041, 200063, 200087, 200117, 200131, 200153, 200159, 200171, 200177, 200183,
  200191, 200201, 200227, 200231, 200237, 200257, 200273, 200293, 200297, 200323, 200329, 200341, 200351, 200357, 200363, 200371,
  200381, 200383, 200401, 200407, 200437, 200443, 200461, 200467, 200483, 200513, 200569, 200573, 200579, 200587, 200591, 200597,
  200609, 200639, 200657, 200671, 200689, 200699, 200713, 200723, 200731, 200771, 200779, 200789, 200797, 200807, 200843, 200861,
  200867, 200869, 200881, 200891, 200899, 200903, 200909, 200927, 200929, 200971, 200983, 200987, 200989, 201007, 201011, 201031,
  201037, 201049, 201073, 201101, 201107, 201119, 201121, 201139, 201151, 201163, 201167, 201193, 201203, 201209, 201211, 201233,
  201247, 201251, 201281, 201287, 201307, 201329, 201337, 201359, 201389, 201401, 201403, 201413, 201437, 201449, 201451, 201473,
  201491, 201493, 201497, 201499, 201511, 201517, 201547, 201557, 201577, 201581, 201589, 201599, 201611, 201623, 201629, 201653,
  201661, 201667, 201673, 201683, 201701, 201709, 201731, 201743, 201757, 201767, 201769, 201781, 201787, 201791, 201797, 201809,
  201821, 201823, 201827, 201829, 201833, 201847, 201881, 201889, 201893, 201907, 201911, 201919, 201923, 201937, 201947, 201953,
  201961, 201973, 201979, 201997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock101 : List ℕ := [
  202001, 202021, 202031, 202049, 202061, 202063, 202067, 202087, 202099, 202109, 202121, 202127, 202129, 202183, 202187, 202201,
  202219, 202231, 202243, 202277, 202289, 202291, 202309, 202327, 202339, 202343, 202357, 202361, 202381, 202387, 202393, 202403,
  202409, 202441, 202471, 202481, 202493, 202519, 202529, 202549, 202567, 202577, 202591, 202613, 202621, 202627, 202637, 202639,
  202661, 202667, 202679, 202693, 202717, 202729, 202733, 202747, 202751, 202753, 202757, 202777, 202799, 202817, 202823, 202841,
  202859, 202877, 202879, 202889, 202907, 202921, 202931, 202933, 202949, 202967, 202973, 202981, 202987, 202999, 203011, 203017,
  203023, 203039, 203051, 203057, 203117, 203141, 203173, 203183, 203207, 203209, 203213, 203221, 203227, 203233, 203249, 203279,
  203293, 203309, 203311, 203317, 203321, 203323, 203339, 203341, 203351, 203353, 203363, 203381, 203383, 203387, 203393, 203417,
  203419, 203429, 203431, 203449, 203459, 203461, 203531, 203549, 203563, 203569, 203579, 203591, 203617, 203627, 203641, 203653,
  203657, 203659, 203663, 203669, 203713, 203761, 203767, 203771, 203773, 203789, 203807, 203809, 203821, 203843, 203857, 203869,
  203873, 203897, 203909, 203911, 203921, 203947, 203953, 203969, 203971, 203977, 203989, 203999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock102 : List ℕ := [
  204007, 204013, 204019, 204023, 204047, 204059, 204067, 204101, 204107, 204133, 204137, 204143, 204151, 204161, 204163, 204173,
  204233, 204251, 204299, 204301, 204311, 204319, 204329, 204331, 204353, 204359, 204361, 204367, 204371, 204377, 204397, 204427,
  204431, 204437, 204439, 204443, 204461, 204481, 204487, 204509, 204511, 204517, 204521, 204557, 204563, 204583, 204587, 204599,
  204601, 204613, 204623, 204641, 204667, 204679, 204707, 204719, 204733, 204749, 204751, 204781, 204791, 204793, 204797, 204803,
  204821, 204857, 204859, 204871, 204887, 204913, 204917, 204923, 204931, 204947, 204973, 204979, 204983, 205019, 205031, 205033,
  205043, 205063, 205069, 205081, 205097, 205103, 205111, 205129, 205133, 205141, 205151, 205157, 205171, 205187, 205201, 205211,
  205213, 205223, 205237, 205253, 205267, 205297, 205307, 205319, 205327, 205339, 205357, 205391, 205397, 205399, 205417, 205421,
  205423, 205427, 205433, 205441, 205453, 205463, 205477, 205483, 205487, 205493, 205507, 205519, 205529, 205537, 205549, 205553,
  205559, 205589, 205603, 205607, 205619, 205627, 205633, 205651, 205657, 205661, 205663, 205703, 205721, 205759, 205763, 205783,
  205817, 205823, 205837, 205847, 205879, 205883, 205913, 205937, 205949, 205951, 205957, 205963, 205967, 205981, 205991, 205993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock103 : List ℕ := [
  206009, 206021, 206027, 206033, 206039, 206047, 206051, 206069, 206077, 206081, 206083, 206123, 206153, 206177, 206179, 206183,
  206191, 206197, 206203, 206209, 206221, 206233, 206237, 206249, 206251, 206263, 206273, 206279, 206281, 206291, 206299, 206303,
  206341, 206347, 206351, 206369, 206383, 206399, 206407, 206411, 206413, 206419, 206447, 206461, 206467, 206477, 206483, 206489,
  206501, 206519, 206527, 206543, 206551, 206593, 206597, 206603, 206623, 206627, 206639, 206641, 206651, 206699, 206749, 206779,
  206783, 206803, 206807, 206813, 206819, 206821, 206827, 206879, 206887, 206897, 206909, 206911, 206917, 206923, 206933, 206939,
  206951, 206953, 206993, 207013, 207017, 207029, 207037, 207041, 207061, 207073, 207079, 207113, 207121, 207127, 207139, 207169,
  207187, 207191, 207197, 207199, 207227, 207239, 207241, 207257, 207269, 207287, 207293, 207301, 207307, 207329, 207331, 207341,
  207343, 207367, 207371, 207377, 207401, 207409, 207433, 207443, 207457, 207463, 207469, 207479, 207481, 207491, 207497, 207509,
  207511, 207517, 207521, 207523, 207541, 207547, 207551, 207563, 207569, 207589, 207593, 207619, 207629, 207643, 207653, 207661,
  207671, 207673, 207679, 207709, 207719, 207721, 207743, 207763, 207769, 207797, 207799, 207811, 207821, 207833, 207847, 207869,
  207877, 207923, 207931, 207941, 207947, 207953, 207967, 207971, 207973, 207997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock104 : List ℕ := [
  208001, 208003, 208009, 208037, 208049, 208057, 208067, 208073, 208099, 208111, 208121, 208129, 208139, 208141, 208147, 208189,
  208207, 208213, 208217, 208223, 208231, 208253, 208261, 208277, 208279, 208283, 208291, 208309, 208319, 208333, 208337, 208367,
  208379, 208387, 208391, 208393, 208409, 208433, 208441, 208457, 208459, 208463, 208469, 208489, 208493, 208499, 208501, 208511,
  208513, 208519, 208529, 208553, 208577, 208589, 208591, 208609, 208627, 208631, 208657, 208667, 208673, 208687, 208697, 208699,
  208721, 208729, 208739, 208759, 208787, 208799, 208807, 208837, 208843, 208877, 208889, 208891, 208907, 208927, 208931, 208933,
  208961, 208963, 208991, 208993, 208997, 209021, 209029, 209039, 209063, 209071, 209089, 209123, 209147, 209159, 209173, 209179,
  209189, 209201, 209203, 209213, 209221, 209227, 209233, 209249, 209257, 209263, 209267, 209269, 209299, 209311, 209317, 209327,
  209333, 209347, 209353, 209357, 209359, 209371, 209381, 209393, 209401, 209431, 209441, 209449, 209459, 209471, 209477, 209497,
  209519, 209533, 209543, 209549, 209563, 209567, 209569, 209579, 209581, 209597, 209621, 209623, 209639, 209647, 209659, 209669,
  209687, 209701, 209707, 209717, 209719, 209743, 209767, 209771, 209789, 209801, 209809, 209813, 209819, 209821, 209837, 209851,
  209857, 209861, 209887, 209917, 209927, 209929, 209939, 209953, 209959, 209971, 209977, 209983, 209987
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock105 : List ℕ := [
  210011, 210019, 210031, 210037, 210053, 210071, 210097, 210101, 210109, 210113, 210127, 210131, 210139, 210143, 210157, 210169,
  210173, 210187, 210191, 210193, 210209, 210229, 210233, 210241, 210247, 210257, 210263, 210277, 210283, 210299, 210317, 210319,
  210323, 210347, 210359, 210361, 210391, 210401, 210403, 210407, 210421, 210437, 210461, 210467, 210481, 210487, 210491, 210499,
  210523, 210527, 210533, 210557, 210599, 210601, 210619, 210631, 210643, 210659, 210671, 210709, 210713, 210719, 210731, 210739,
  210761, 210773, 210803, 210809, 210811, 210823, 210827, 210839, 210853, 210857, 210869, 210901, 210907, 210911, 210913, 210923,
  210929, 210943, 210961, 210967, 211007, 211039, 211049, 211051, 211061, 211063, 211067, 211073, 211093, 211097, 211129, 211151,
  211153, 211177, 211187, 211193, 211199, 211213, 211217, 211219, 211229, 211231, 211241, 211247, 211271, 211283, 211291, 211297,
  211313, 211319, 211333, 211339, 211349, 211369, 211373, 211403, 211427, 211433, 211441, 211457, 211469, 211493, 211499, 211501,
  211507, 211543, 211559, 211571, 211573, 211583, 211597, 211619, 211639, 211643, 211657, 211661, 211663, 211681, 211691, 211693,
  211711, 211723, 211727, 211741, 211747, 211777, 211781, 211789, 211801, 211811, 211817, 211859, 211867, 211873, 211877, 211879,
  211889, 211891, 211927, 211931, 211933, 211943, 211949, 211969, 211979, 211997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock106 : List ℕ := [
  212029, 212039, 212057, 212081, 212099, 212117, 212123, 212131, 212141, 212161, 212167, 212183, 212203, 212207, 212209, 212227,
  212239, 212243, 212281, 212293, 212297, 212353, 212369, 212383, 212411, 212419, 212423, 212437, 212447, 212453, 212461, 212467,
  212479, 212501, 212507, 212557, 212561, 212573, 212579, 212587, 212593, 212627, 212633, 212651, 212669, 212671, 212677, 212683,
  212701, 212777, 212791, 212801, 212827, 212837, 212843, 212851, 212867, 212869, 212873, 212881, 212897, 212903, 212909, 212917,
  212923, 212969, 212981, 212987, 212999, 213019, 213023, 213029, 213043, 213067, 213079, 213091, 213097, 213119, 213131, 213133,
  213139, 213149, 213173, 213181, 213193, 213203, 213209, 213217, 213223, 213229, 213247, 213253, 213263, 213281, 213287, 213289,
  213307, 213319, 213329, 213337, 213349, 213359, 213361, 213383, 213391, 213397, 213407, 213449, 213461, 213467, 213481, 213491,
  213523, 213533, 213539, 213553, 213557, 213589, 213599, 213611, 213613, 213623, 213637, 213641, 213649, 213659, 213713, 213721,
  213727, 213737, 213751, 213791, 213799, 213821, 213827, 213833, 213847, 213859, 213881, 213887, 213901, 213919, 213929, 213943,
  213947, 213949, 213953, 213973, 213977, 213989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock107 : List ℕ := [
  214003, 214007, 214009, 214021, 214031, 214033, 214043, 214051, 214063, 214069, 214087, 214091, 214129, 214133, 214141, 214147,
  214163, 214177, 214189, 214211, 214213, 214219, 214237, 214243, 214259, 214283, 214297, 214309, 214351, 214363, 214373, 214381,
  214391, 214399, 214433, 214439, 214451, 214457, 214463, 214469, 214481, 214483, 214499, 214507, 214517, 214519, 214531, 214541,
  214559, 214561, 214589, 214603, 214607, 214631, 214639, 214651, 214657, 214663, 214667, 214673, 214691, 214723, 214729, 214733,
  214741, 214759, 214763, 214771, 214783, 214787, 214789, 214807, 214811, 214817, 214831, 214849, 214853, 214867, 214883, 214891,
  214913, 214939, 214943, 214967, 214987, 214993, 215051, 215063, 215077, 215087, 215123, 215141, 215143, 215153, 215161, 215179,
  215183, 215191, 215197, 215239, 215249, 215261, 215273, 215279, 215297, 215309, 215317, 215329, 215351, 215353, 215359, 215381,
  215389, 215393, 215399, 215417, 215443, 215447, 215459, 215461, 215471, 215483, 215497, 215503, 215507, 215521, 215531, 215563,
  215573, 215587, 215617, 215653, 215659, 215681, 215687, 215689, 215693, 215723, 215737, 215753, 215767, 215771, 215797, 215801,
  215827, 215833, 215843, 215851, 215857, 215863, 215893, 215899, 215909, 215921, 215927, 215939, 215953, 215959, 215981, 215983
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock108 : List ℕ := [
  216023, 216037, 216061, 216071, 216091, 216103, 216107, 216113, 216119, 216127, 216133, 216149, 216157, 216173, 216179, 216211,
  216217, 216233, 216259, 216263, 216289, 216317, 216319, 216329, 216347, 216371, 216373, 216379, 216397, 216401, 216421, 216431,
  216451, 216481, 216493, 216509, 216523, 216551, 216553, 216569, 216571, 216577, 216607, 216617, 216641, 216647, 216649, 216653,
  216661, 216679, 216703, 216719, 216731, 216743, 216751, 216757, 216761, 216779, 216781, 216787, 216791, 216803, 216829, 216841,
  216851, 216859, 216877, 216899, 216901, 216911, 216917, 216919, 216947, 216967, 216973, 216991, 217001, 217003, 217027, 217033,
  217057, 217069, 217081, 217111, 217117, 217121, 217157, 217163, 217169, 217199, 217201, 217207, 217219, 217223, 217229, 217241,
  217253, 217271, 217307, 217309, 217313, 217319, 217333, 217337, 217339, 217351, 217361, 217363, 217367, 217369, 217387, 217397,
  217409, 217411, 217421, 217429, 217439, 217457, 217463, 217489, 217499, 217517, 217519, 217559, 217561, 217573, 217577, 217579,
  217619, 217643, 217661, 217667, 217681, 217687, 217691, 217697, 217717, 217727, 217733, 217739, 217747, 217771, 217781, 217793,
  217823, 217829, 217849, 217859, 217901, 217907, 217909, 217933, 217937, 217969, 217979, 217981
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock109 : List ℕ := [
  218003, 218021, 218047, 218069, 218077, 218081, 218083, 218087, 218107, 218111, 218117, 218131, 218137, 218143, 218149, 218171,
  218191, 218213, 218227, 218233, 218249, 218279, 218287, 218357, 218363, 218371, 218381, 218389, 218401, 218417, 218419, 218423,
  218437, 218447, 218453, 218459, 218461, 218479, 218509, 218513, 218521, 218527, 218531, 218549, 218551, 218579, 218591, 218599,
  218611, 218623, 218627, 218629, 218641, 218651, 218657, 218677, 218681, 218711, 218717, 218719, 218723, 218737, 218749, 218761,
  218783, 218797, 218809, 218819, 218833, 218839, 218843, 218849, 218857, 218873, 218887, 218923, 218941, 218947, 218963, 218969,
  218971, 218987, 218989, 218993, 219001, 219017, 219019, 219031, 219041, 219053, 219059, 219071, 219083, 219091, 219097, 219103,
  219119, 219133, 219143, 219169, 219187, 219217, 219223, 219251, 219277, 219281, 219293, 219301, 219311, 219313, 219353, 219361,
  219371, 219377, 219389, 219407, 219409, 219433, 219437, 219451, 219463, 219467, 219491, 219503, 219517, 219523, 219529, 219533,
  219547, 219577, 219587, 219599, 219607, 219613, 219619, 219629, 219647, 219649, 219677, 219679, 219683, 219689, 219707, 219721,
  219727, 219731, 219749, 219757, 219761, 219763, 219767, 219787, 219797, 219799, 219809, 219823, 219829, 219839, 219847, 219851,
  219871, 219881, 219889, 219911, 219917, 219931, 219937, 219941, 219943, 219953, 219959, 219971, 219977, 219979, 219983
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock110 : List ℕ := [
  220009, 220013, 220019, 220021, 220057, 220063, 220123, 220141, 220147, 220151, 220163, 220169, 220177, 220189, 220217, 220243,
  220279, 220291, 220301, 220307, 220327, 220333, 220351, 220357, 220361, 220369, 220373, 220391, 220399, 220403, 220411, 220421,
  220447, 220469, 220471, 220511, 220513, 220529, 220537, 220543, 220553, 220559, 220573, 220579, 220589, 220613, 220663, 220667,
  220673, 220681, 220687, 220699, 220709, 220721, 220747, 220757, 220771, 220783, 220789, 220793, 220807, 220811, 220841, 220859,
  220861, 220873, 220877, 220879, 220889, 220897, 220901, 220903, 220907, 220919, 220931, 220933, 220939, 220973, 221021, 221047,
  221059, 221069, 221071, 221077, 221083, 221087, 221093, 221101, 221159, 221171, 221173, 221197, 221201, 221203, 221209, 221219,
  221227, 221233, 221239, 221251, 221261, 221281, 221303, 221311, 221317, 221327, 221393, 221399, 221401, 221411, 221413, 221447,
  221453, 221461, 221471, 221477, 221489, 221497, 221509, 221537, 221539, 221549, 221567, 221581, 221587, 221603, 221621, 221623,
  221653, 221657, 221659, 221671, 221677, 221707, 221713, 221717, 221719, 221723, 221729, 221737, 221747, 221773, 221797, 221807,
  221813, 221827, 221831, 221849, 221873, 221891, 221909, 221941, 221951, 221953, 221957, 221987, 221989, 221999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock111 : List ℕ := [
  222007, 222011, 222023, 222029, 222041, 222043, 222059, 222067, 222073, 222107, 222109, 222113, 222127, 222137, 222149, 222151,
  222161, 222163, 222193, 222197, 222199, 222247, 222269, 222289, 222293, 222311, 222317, 222323, 222329, 222337, 222347, 222349,
  222361, 222367, 222379, 222389, 222403, 222419, 222437, 222461, 222493, 222499, 222511, 222527, 222533, 222553, 222557, 222587,
  222601, 222613, 222619, 222643, 222647, 222659, 222679, 222707, 222713, 222731, 222773, 222779, 222787, 222791, 222793, 222799,
  222823, 222839, 222841, 222857, 222863, 222877, 222883, 222913, 222919, 222931, 222941, 222947, 222953, 222967, 222977, 222979,
  222991, 223007, 223009, 223019, 223037, 223049, 223051, 223061, 223063, 223087, 223099, 223103, 223129, 223133, 223151, 223207,
  223211, 223217, 223219, 223229, 223241, 223243, 223247, 223253, 223259, 223273, 223277, 223283, 223291, 223303, 223313, 223319,
  223331, 223337, 223339, 223361, 223367, 223381, 223403, 223423, 223429, 223439, 223441, 223463, 223469, 223481, 223493, 223507,
  223529, 223543, 223547, 223549, 223577, 223589, 223621, 223633, 223637, 223667, 223679, 223681, 223697, 223711, 223747, 223753,
  223757, 223759, 223781, 223823, 223829, 223831, 223837, 223841, 223843, 223849, 223903, 223919, 223921, 223939, 223963, 223969,
  223999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock112 : List ℕ := [
  224011, 224027, 224033, 224041, 224047, 224057, 224069, 224071, 224101, 224113, 224129, 224131, 224149, 224153, 224171, 224177,
  224197, 224201, 224209, 224221, 224233, 224239, 224251, 224261, 224267, 224291, 224299, 224303, 224309, 224317, 224327, 224351,
  224359, 224363, 224401, 224423, 224429, 224443, 224449, 224461, 224467, 224473, 224491, 224501, 224513, 224527, 224563, 224569,
  224579, 224591, 224603, 224611, 224617, 224629, 224633, 224669, 224677, 224683, 224699, 224711, 224717, 224729, 224737, 224743,
  224759, 224771, 224797, 224813, 224831, 224863, 224869, 224881, 224891, 224897, 224909, 224911, 224921, 224929, 224947, 224951,
  224969, 224977, 224993, 225023, 225037, 225061, 225067, 225077, 225079, 225089, 225109, 225119, 225133, 225143, 225149, 225157,
  225161, 225163, 225167, 225217, 225221, 225223, 225227, 225241, 225257, 225263, 225287, 225289, 225299, 225307, 225341, 225343,
  225347, 225349, 225353, 225371, 225373, 225383, 225427, 225431, 225457, 225461, 225479, 225493, 225499, 225503, 225509, 225523,
  225527, 225529, 225569, 225581, 225583, 225601, 225611, 225613, 225619, 225629, 225637, 225671, 225683, 225689, 225697, 225721,
  225733, 225749, 225751, 225767, 225769, 225779, 225781, 225809, 225821, 225829, 225839, 225859, 225871, 225889, 225919, 225931,
  225941, 225943, 225949, 225961, 225977, 225983, 225989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock113 : List ℕ := [
  226001, 226007, 226013, 226027, 226063, 226087, 226099, 226103, 226123, 226129, 226133, 226141, 226169, 226183, 226189, 226199,
  226201, 226217, 226231, 226241, 226267, 226283, 226307, 226313, 226337, 226357, 226367, 226379, 226381, 226397, 226409, 226427,
  226433, 226451, 226453, 226463, 226483, 226487, 226511, 226531, 226547, 226549, 226553, 226571, 226601, 226609, 226621, 226631,
  226637, 226643, 226649, 226657, 226663, 226669, 226691, 226697, 226741, 226753, 226769, 226777, 226783, 226789, 226799, 226813,
  226817, 226819, 226823, 226843, 226871, 226901, 226903, 226907, 226913, 226937, 226943, 226991, 227011, 227027, 227053, 227081,
  227089, 227093, 227111, 227113, 227131, 227147, 227153, 227159, 227167, 227177, 227189, 227191, 227207, 227219, 227231, 227233,
  227251, 227257, 227267, 227281, 227299, 227303, 227363, 227371, 227377, 227387, 227393, 227399, 227407, 227419, 227431, 227453,
  227459, 227467, 227471, 227473, 227489, 227497, 227501, 227519, 227531, 227533, 227537, 227561, 227567, 227569, 227581, 227593,
  227597, 227603, 227609, 227611, 227627, 227629, 227651, 227653, 227663, 227671, 227693, 227699, 227707, 227719, 227729, 227743,
  227789, 227797, 227827, 227849, 227869, 227873, 227893, 227947, 227951, 227977, 227989, 227993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock114 : List ℕ := [
  228013, 228023, 228049, 228061, 228077, 228097, 228103, 228113, 228127, 228131, 228139, 228181, 228197, 228199, 228203, 228211,
  228223, 228233, 228251, 228257, 228281, 228299, 228301, 228307, 228311, 228331, 228337, 228341, 228353, 228359, 228383, 228409,
  228419, 228421, 228427, 228443, 228451, 228457, 228461, 228469, 228479, 228509, 228511, 228517, 228521, 228523, 228539, 228559,
  228577, 228581, 228587, 228593, 228601, 228611, 228617, 228619, 228637, 228647, 228677, 228707, 228713, 228731, 228733, 228737,
  228751, 228757, 228773, 228793, 228797, 228799, 228829, 228841, 228847, 228853, 228859, 228869, 228881, 228883, 228887, 228901,
  228911, 228913, 228923, 228929, 228953, 228959, 228961, 228983, 228989, 229003, 229027, 229037, 229081, 229093, 229123, 229127,
  229133, 229139, 229153, 229157, 229171, 229181, 229189, 229199, 229213, 229217, 229223, 229237, 229247, 229249, 229253, 229261,
  229267, 229283, 229309, 229321, 229343, 229351, 229373, 229393, 229399, 229403, 229409, 229423, 229433, 229459, 229469, 229487,
  229499, 229507, 229519, 229529, 229547, 229549, 229553, 229561, 229583, 229589, 229591, 229601, 229613, 229627, 229631, 229637,
  229639, 229681, 229693, 229699, 229703, 229711, 229717, 229727, 229739, 229751, 229753, 229759, 229763, 229769, 229771, 229777,
  229781, 229799, 229813, 229819, 229837, 229841, 229847, 229849, 229897, 229903, 229937, 229939, 229949, 229961, 229963, 229979,
  229981
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock115 : List ℕ := [
  230003, 230017, 230047, 230059, 230063, 230077, 230081, 230089, 230101, 230107, 230117, 230123, 230137, 230143, 230149, 230189,
  230203, 230213, 230221, 230227, 230233, 230239, 230257, 230273, 230281, 230291, 230303, 230309, 230311, 230327, 230339, 230341,
  230353, 230357, 230369, 230383, 230387, 230389, 230393, 230431, 230449, 230453, 230467, 230471, 230479, 230501, 230507, 230539,
  230551, 230561, 230563, 230567, 230597, 230611, 230647, 230653, 230663, 230683, 230693, 230719, 230729, 230743, 230761, 230767,
  230771, 230773, 230779, 230807, 230819, 230827, 230833, 230849, 230861, 230863, 230873, 230891, 230929, 230933, 230939, 230941,
  230959, 230969, 230977, 230999, 231001, 231017, 231019, 231031, 231041, 231053, 231067, 231079, 231107, 231109, 231131, 231169,
  231197, 231223, 231241, 231269, 231271, 231277, 231289, 231293, 231299, 231317, 231323, 231331, 231347, 231349, 231359, 231367,
  231379, 231409, 231419, 231431, 231433, 231443, 231461, 231463, 231479, 231481, 231493, 231503, 231529, 231533, 231547, 231551,
  231559, 231563, 231571, 231589, 231599, 231607, 231611, 231613, 231631, 231643, 231661, 231677, 231701, 231709, 231719, 231779,
  231799, 231809, 231821, 231823, 231827, 231839, 231841, 231859, 231871, 231877, 231893, 231901, 231919, 231923, 231943, 231947,
  231961, 231967
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock116 : List ℕ := [
  232003, 232007, 232013, 232049, 232051, 232073, 232079, 232081, 232091, 232103, 232109, 232117, 232129, 232153, 232171, 232187,
  232189, 232207, 232217, 232259, 232303, 232307, 232333, 232357, 232363, 232367, 232381, 232391, 232409, 232411, 232417, 232433,
  232439, 232451, 232457, 232459, 232487, 232499, 232513, 232523, 232549, 232567, 232571, 232591, 232597, 232607, 232621, 232633,
  232643, 232663, 232669, 232681, 232699, 232709, 232711, 232741, 232751, 232753, 232777, 232801, 232811, 232819, 232823, 232847,
  232853, 232861, 232871, 232877, 232891, 232901, 232907, 232919, 232937, 232961, 232963, 232987, 233021, 233069, 233071, 233083,
  233113, 233117, 233141, 233143, 233159, 233161, 233173, 233183, 233201, 233221, 233231, 233239, 233251, 233267, 233279, 233293,
  233297, 233323, 233327, 233329, 233341, 233347, 233353, 233357, 233371, 233407, 233417, 233419, 233423, 233437, 233477, 233489,
  233509, 233549, 233551, 233557, 233591, 233599, 233609, 233617, 233621, 233641, 233663, 233669, 233683, 233687, 233689, 233693,
  233713, 233743, 233747, 233759, 233777, 233837, 233851, 233861, 233879, 233881, 233911, 233917, 233921, 233923, 233939, 233941,
  233969, 233983, 233993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock117 : List ℕ := [
  234007, 234029, 234043, 234067, 234083, 234089, 234103, 234121, 234131, 234139, 234149, 234161, 234167, 234181, 234187, 234191,
  234193, 234197, 234203, 234211, 234217, 234239, 234259, 234271, 234281, 234287, 234293, 234317, 234319, 234323, 234331, 234341,
  234343, 234361, 234383, 234431, 234457, 234461, 234463, 234467, 234473, 234499, 234511, 234527, 234529, 234539, 234541, 234547,
  234571, 234587, 234589, 234599, 234613, 234629, 234653, 234659, 234673, 234683, 234713, 234721, 234727, 234733, 234743, 234749,
  234769, 234781, 234791, 234799, 234803, 234809, 234811, 234833, 234847, 234851, 234863, 234869, 234893, 234907, 234917, 234931,
  234947, 234959, 234961, 234967, 234977, 234979, 234989, 235003, 235007, 235009, 235013, 235043, 235051, 235057, 235069, 235091,
  235099, 235111, 235117, 235159, 235171, 235177, 235181, 235199, 235211, 235231, 235241, 235243, 235273, 235289, 235307, 235309,
  235337, 235349, 235369, 235397, 235439, 235441, 235447, 235483, 235489, 235493, 235513, 235519, 235523, 235537, 235541, 235553,
  235559, 235577, 235591, 235601, 235607, 235621, 235661, 235663, 235673, 235679, 235699, 235723, 235747, 235751, 235783, 235787,
  235789, 235793, 235811, 235813, 235849, 235871, 235877, 235889, 235891, 235901, 235919, 235927, 235951, 235967, 235979, 235997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock118 : List ℕ := [
  236017, 236021, 236053, 236063, 236069, 236077, 236087, 236107, 236111, 236129, 236143, 236153, 236167, 236207, 236209, 236219,
  236231, 236261, 236287, 236293, 236297, 236323, 236329, 236333, 236339, 236377, 236381, 236387, 236399, 236407, 236429, 236449,
  236461, 236471, 236477, 236479, 236503, 236507, 236519, 236527, 236549, 236563, 236573, 236609, 236627, 236641, 236653, 236659,
  236681, 236699, 236701, 236707, 236713, 236723, 236729, 236737, 236749, 236771, 236773, 236779, 236783, 236807, 236813, 236867,
  236869, 236879, 236881, 236891, 236893, 236897, 236909, 236917, 236947, 236981, 236983, 236993, 237011, 237019, 237043, 237053,
  237067, 237071, 237073, 237089, 237091, 237137, 237143, 237151, 237157, 237161, 237163, 237173, 237179, 237203, 237217, 237233,
  237257, 237271, 237277, 237283, 237287, 237301, 237313, 237319, 237331, 237343, 237361, 237373, 237379, 237401, 237409, 237467,
  237487, 237509, 237547, 237563, 237571, 237581, 237607, 237619, 237631, 237673, 237683, 237689, 237691, 237701, 237707, 237733,
  237737, 237749, 237763, 237767, 237781, 237791, 237821, 237851, 237857, 237859, 237877, 237883, 237901, 237911, 237929, 237959,
  237967, 237971, 237973, 237977, 237997
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock119 : List ℕ := [
  238001, 238009, 238019, 238031, 238037, 238039, 238079, 238081, 238093, 238099, 238103, 238109, 238141, 238151, 238157, 238159,
  238163, 238171, 238181, 238201, 238207, 238213, 238223, 238229, 238237, 238247, 238261, 238267, 238291, 238307, 238313, 238321,
  238331, 238339, 238361, 238363, 238369, 238373, 238397, 238417, 238423, 238439, 238451, 238463, 238471, 238477, 238481, 238499,
  238519, 238529, 238531, 238547, 238573, 238591, 238627, 238639, 238649, 238657, 238673, 238681, 238691, 238703, 238709, 238723,
  238727, 238729, 238747, 238759, 238781, 238789, 238801, 238829, 238837, 238841, 238853, 238859, 238877, 238879, 238883, 238897,
  238919, 238921, 238939, 238943, 238949, 238967, 238991, 239017, 239023, 239027, 239053, 239069, 239081, 239087, 239119, 239137,
  239147, 239167, 239171, 239179, 239201, 239231, 239233, 239237, 239243, 239251, 239263, 239273, 239287, 239297, 239329, 239333,
  239347, 239357, 239383, 239387, 239389, 239417, 239423, 239429, 239431, 239441, 239461, 239489, 239509, 239521, 239527, 239531,
  239539, 239543, 239557, 239567, 239579, 239587, 239597, 239611, 239623, 239633, 239641, 239671, 239689, 239699, 239711, 239713,
  239731, 239737, 239753, 239779, 239783, 239803, 239807, 239831, 239843, 239849, 239851, 239857, 239873, 239879, 239893, 239929,
  239933, 239947, 239957, 239963, 239977, 239999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock120 : List ℕ := [
  240007, 240011, 240017, 240041, 240043, 240047, 240049, 240059, 240073, 240089, 240101, 240109, 240113, 240131, 240139, 240151,
  240169, 240173, 240197, 240203, 240209, 240257, 240259, 240263, 240271, 240283, 240287, 240319, 240341, 240347, 240349, 240353,
  240371, 240379, 240421, 240433, 240437, 240473, 240479, 240491, 240503, 240509, 240517, 240551, 240571, 240587, 240589, 240599,
  240607, 240623, 240631, 240641, 240659, 240677, 240701, 240707, 240719, 240727, 240733, 240739, 240743, 240763, 240769, 240797,
  240811, 240829, 240841, 240853, 240859, 240869, 240881, 240883, 240893, 240899, 240913, 240943, 240953, 240959, 240967, 240997,
  241013, 241027, 241037, 241049, 241051, 241061, 241067, 241069, 241079, 241093, 241117, 241127, 241141, 241169, 241177, 241183,
  241207, 241229, 241249, 241253, 241259, 241261, 241271, 241291, 241303, 241313, 241321, 241327, 241333, 241337, 241343, 241361,
  241363, 241391, 241393, 241421, 241429, 241441, 241453, 241463, 241469, 241489, 241511, 241513, 241517, 241537, 241543, 241559,
  241561, 241567, 241589, 241597, 241601, 241603, 241639, 241643, 241651, 241663, 241667, 241679, 241687, 241691, 241711, 241727,
  241739, 241771, 241781, 241783, 241793, 241807, 241811, 241817, 241823, 241847, 241861, 241867, 241873, 241877, 241883, 241903,
  241907, 241919, 241921, 241931, 241939, 241951, 241963, 241973, 241979, 241981, 241993
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock121 : List ℕ := [
  242009, 242057, 242059, 242069, 242083, 242093, 242101, 242119, 242129, 242147, 242161, 242171, 242173, 242197, 242201, 242227,
  242243, 242257, 242261, 242273, 242279, 242309, 242329, 242357, 242371, 242377, 242393, 242399, 242413, 242419, 242441, 242447,
  242449, 242453, 242467, 242479, 242483, 242491, 242509, 242519, 242521, 242533, 242551, 242591, 242603, 242617, 242621, 242629,
  242633, 242639, 242647, 242659, 242677, 242681, 242689, 242713, 242729, 242731, 242747, 242773, 242779, 242789, 242797, 242807,
  242813, 242819, 242863, 242867, 242873, 242887, 242911, 242923, 242927, 242971, 242989, 242999, 243011, 243031, 243073, 243077,
  243091, 243101, 243109, 243119, 243121, 243137, 243149, 243157, 243161, 243167, 243197, 243203, 243209, 243227, 243233, 243239,
  243259, 243263, 243301, 243311, 243343, 243367, 243391, 243401, 243403, 243421, 243431, 243433, 243437, 243461, 243469, 243473,
  243479, 243487, 243517, 243521, 243527, 243533, 243539, 243553, 243577, 243583, 243587, 243589, 243613, 243623, 243631, 243643,
  243647, 243671, 243673, 243701, 243703, 243707, 243709, 243769, 243781, 243787, 243799, 243809, 243829, 243839, 243851, 243857,
  243863, 243871, 243889, 243911, 243917, 243931, 243953, 243973, 243989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock122 : List ℕ := [
  244003, 244009, 244021, 244033, 244043, 244087, 244091, 244109, 244121, 244129, 244141, 244147, 244157, 244159, 244177, 244199,
  244217, 244219, 244243, 244247, 244253, 244261, 244291, 244297, 244301, 244303, 244313, 244333, 244339, 244351, 244357, 244367,
  244379, 244381, 244393, 244399, 244403, 244411, 244423, 244429, 244451, 244457, 244463, 244471, 244481, 244493, 244507, 244529,
  244547, 244553, 244561, 244567, 244583, 244589, 244597, 244603, 244619, 244633, 244637, 244639, 244667, 244669, 244687, 244691,
  244703, 244711, 244721, 244733, 244747, 244753, 244759, 244781, 244787, 244813, 244837, 244841, 244843, 244859, 244861, 244873,
  244877, 244889, 244897, 244901, 244939, 244943, 244957, 244997, 245023, 245029, 245033, 245039, 245071, 245083, 245087, 245107,
  245129, 245131, 245149, 245171, 245173, 245177, 245183, 245209, 245251, 245257, 245261, 245269, 245279, 245291, 245299, 245317,
  245321, 245339, 245383, 245389, 245407, 245411, 245417, 245419, 245437, 245471, 245473, 245477, 245501, 245513, 245519, 245521,
  245527, 245533, 245561, 245563, 245587, 245591, 245593, 245621, 245627, 245629, 245639, 245653, 245671, 245681, 245683, 245711,
  245719, 245723, 245741, 245747, 245753, 245759, 245771, 245783, 245789, 245821, 245849, 245851, 245863, 245881, 245897, 245899,
  245909, 245911, 245941, 245963, 245977, 245981, 245983, 245989
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock123 : List ℕ := [
  246011, 246017, 246049, 246073, 246097, 246119, 246121, 246131, 246133, 246151, 246167, 246173, 246187, 246193, 246203, 246209,
  246217, 246223, 246241, 246247, 246251, 246271, 246277, 246289, 246317, 246319, 246329, 246343, 246349, 246361, 246371, 246391,
  246403, 246439, 246469, 246473, 246497, 246509, 246511, 246523, 246527, 246539, 246557, 246569, 246577, 246599, 246607, 246611,
  246613, 246637, 246641, 246643, 246661, 246683, 246689, 246707, 246709, 246713, 246731, 246739, 246769, 246773, 246781, 246787,
  246793, 246803, 246809, 246811, 246817, 246833, 246839, 246889, 246899, 246907, 246913, 246919, 246923, 246929, 246931, 246937,
  246941, 246947, 246971, 246979, 247001, 247007, 247031, 247067, 247069, 247073, 247087, 247099, 247141, 247183, 247193, 247201,
  247223, 247229, 247241, 247249, 247259, 247279, 247301, 247309, 247337, 247339, 247343, 247363, 247369, 247381, 247391, 247393,
  247409, 247421, 247433, 247439, 247451, 247463, 247501, 247519, 247529, 247531, 247547, 247553, 247579, 247591, 247601, 247603,
  247607, 247609, 247613, 247633, 247649, 247651, 247691, 247693, 247697, 247711, 247717, 247729, 247739, 247759, 247769, 247771,
  247781, 247799, 247811, 247813, 247829, 247847, 247853, 247873, 247879, 247889, 247901, 247913, 247939, 247943, 247957, 247991,
  247993, 247997, 247999
]

set_option maxRecDepth 4096 in
private def sievePrimesBlock124 : List ℕ := [
  248021, 248033, 248041, 248051, 248057, 248063, 248071, 248077, 248089, 248099, 248117, 248119, 248137, 248141, 248161, 248167,
  248177, 248179, 248189, 248201, 248203, 248231, 248243, 248257, 248267, 248291, 248293, 248299, 248309, 248317, 248323, 248351,
  248357, 248371, 248389, 248401, 248407, 248431, 248441, 248447, 248461, 248473, 248477, 248483, 248509, 248533, 248537, 248543,
  248569, 248579, 248587, 248593, 248597, 248609, 248621, 248627, 248639, 248641, 248657, 248683, 248701, 248707, 248719, 248723,
  248737, 248749, 248753, 248779, 248783, 248789, 248797, 248813, 248821, 248827, 248839, 248851, 248861, 248867, 248869, 248879,
  248887, 248891, 248893, 248903, 248909, 248971, 248981, 248987, 249017, 249037, 249059, 249079, 249089, 249097, 249103, 249107,
  249127, 249131, 249133, 249143, 249181, 249187, 249199, 249211, 249217, 249229, 249233, 249253, 249257, 249287, 249311, 249317,
  249329, 249341, 249367, 249377, 249383, 249397, 249419, 249421, 249427, 249433, 249437, 249439, 249449, 249463, 249497, 249499,
  249503, 249517, 249521, 249533, 249539, 249541, 249563, 249583, 249589, 249593, 249607, 249647, 249659, 249671, 249677, 249703,
  249721, 249727, 249737, 249749, 249763, 249779, 249797, 249811, 249827, 249833, 249853, 249857, 249859, 249863, 249871, 249881,
  249911, 249923, 249943, 249947, 249967, 249971, 249973, 249989
]

set_option maxRecDepth 4096 in
private def sievePrimeBlocks : List (List ℕ) := [
  sievePrimesBlock0, sievePrimesBlock1, sievePrimesBlock2, sievePrimesBlock3, sievePrimesBlock4, sievePrimesBlock5, sievePrimesBlock6, sievePrimesBlock7, sievePrimesBlock8, sievePrimesBlock9, sievePrimesBlock10, sievePrimesBlock11, sievePrimesBlock12, sievePrimesBlock13, sievePrimesBlock14, sievePrimesBlock15,
  sievePrimesBlock16, sievePrimesBlock17, sievePrimesBlock18, sievePrimesBlock19, sievePrimesBlock20, sievePrimesBlock21, sievePrimesBlock22, sievePrimesBlock23, sievePrimesBlock24, sievePrimesBlock25, sievePrimesBlock26, sievePrimesBlock27, sievePrimesBlock28, sievePrimesBlock29, sievePrimesBlock30, sievePrimesBlock31,
  sievePrimesBlock32, sievePrimesBlock33, sievePrimesBlock34, sievePrimesBlock35, sievePrimesBlock36, sievePrimesBlock37, sievePrimesBlock38, sievePrimesBlock39, sievePrimesBlock40, sievePrimesBlock41, sievePrimesBlock42, sievePrimesBlock43, sievePrimesBlock44, sievePrimesBlock45, sievePrimesBlock46, sievePrimesBlock47,
  sievePrimesBlock48, sievePrimesBlock49, sievePrimesBlock50, sievePrimesBlock51, sievePrimesBlock52, sievePrimesBlock53, sievePrimesBlock54, sievePrimesBlock55, sievePrimesBlock56, sievePrimesBlock57, sievePrimesBlock58, sievePrimesBlock59, sievePrimesBlock60, sievePrimesBlock61, sievePrimesBlock62, sievePrimesBlock63,
  sievePrimesBlock64, sievePrimesBlock65, sievePrimesBlock66, sievePrimesBlock67, sievePrimesBlock68, sievePrimesBlock69, sievePrimesBlock70, sievePrimesBlock71, sievePrimesBlock72, sievePrimesBlock73, sievePrimesBlock74, sievePrimesBlock75, sievePrimesBlock76, sievePrimesBlock77, sievePrimesBlock78, sievePrimesBlock79,
  sievePrimesBlock80, sievePrimesBlock81, sievePrimesBlock82, sievePrimesBlock83, sievePrimesBlock84, sievePrimesBlock85, sievePrimesBlock86, sievePrimesBlock87, sievePrimesBlock88, sievePrimesBlock89, sievePrimesBlock90, sievePrimesBlock91, sievePrimesBlock92, sievePrimesBlock93, sievePrimesBlock94, sievePrimesBlock95,
  sievePrimesBlock96, sievePrimesBlock97, sievePrimesBlock98, sievePrimesBlock99, sievePrimesBlock100, sievePrimesBlock101, sievePrimesBlock102, sievePrimesBlock103, sievePrimesBlock104, sievePrimesBlock105, sievePrimesBlock106, sievePrimesBlock107, sievePrimesBlock108, sievePrimesBlock109, sievePrimesBlock110, sievePrimesBlock111,
  sievePrimesBlock112, sievePrimesBlock113, sievePrimesBlock114, sievePrimesBlock115, sievePrimesBlock116, sievePrimesBlock117, sievePrimesBlock118, sievePrimesBlock119, sievePrimesBlock120, sievePrimesBlock121, sievePrimesBlock122, sievePrimesBlock123, sievePrimesBlock124
]

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock0_certificate :
    primesIn 0 2000 = sievePrimesBlock0 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock1_certificate :
    primesIn 2000 2000 = sievePrimesBlock1 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock2_certificate :
    primesIn 4000 2000 = sievePrimesBlock2 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock3_certificate :
    primesIn 6000 2000 = sievePrimesBlock3 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock4_certificate :
    primesIn 8000 2000 = sievePrimesBlock4 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock5_certificate :
    primesIn 10000 2000 = sievePrimesBlock5 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock6_certificate :
    primesIn 12000 2000 = sievePrimesBlock6 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock7_certificate :
    primesIn 14000 2000 = sievePrimesBlock7 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock8_certificate :
    primesIn 16000 2000 = sievePrimesBlock8 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock9_certificate :
    primesIn 18000 2000 = sievePrimesBlock9 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock10_certificate :
    primesIn 20000 2000 = sievePrimesBlock10 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock11_certificate :
    primesIn 22000 2000 = sievePrimesBlock11 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock12_certificate :
    primesIn 24000 2000 = sievePrimesBlock12 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock13_certificate :
    primesIn 26000 2000 = sievePrimesBlock13 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock14_certificate :
    primesIn 28000 2000 = sievePrimesBlock14 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock15_certificate :
    primesIn 30000 2000 = sievePrimesBlock15 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock16_certificate :
    primesIn 32000 2000 = sievePrimesBlock16 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock17_certificate :
    primesIn 34000 2000 = sievePrimesBlock17 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock18_certificate :
    primesIn 36000 2000 = sievePrimesBlock18 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock19_certificate :
    primesIn 38000 2000 = sievePrimesBlock19 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock20_certificate :
    primesIn 40000 2000 = sievePrimesBlock20 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock21_certificate :
    primesIn 42000 2000 = sievePrimesBlock21 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock22_certificate :
    primesIn 44000 2000 = sievePrimesBlock22 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock23_certificate :
    primesIn 46000 2000 = sievePrimesBlock23 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock24_certificate :
    primesIn 48000 2000 = sievePrimesBlock24 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock25_certificate :
    primesIn 50000 2000 = sievePrimesBlock25 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock26_certificate :
    primesIn 52000 2000 = sievePrimesBlock26 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock27_certificate :
    primesIn 54000 2000 = sievePrimesBlock27 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock28_certificate :
    primesIn 56000 2000 = sievePrimesBlock28 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock29_certificate :
    primesIn 58000 2000 = sievePrimesBlock29 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock30_certificate :
    primesIn 60000 2000 = sievePrimesBlock30 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock31_certificate :
    primesIn 62000 2000 = sievePrimesBlock31 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock32_certificate :
    primesIn 64000 2000 = sievePrimesBlock32 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock33_certificate :
    primesIn 66000 2000 = sievePrimesBlock33 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock34_certificate :
    primesIn 68000 2000 = sievePrimesBlock34 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock35_certificate :
    primesIn 70000 2000 = sievePrimesBlock35 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock36_certificate :
    primesIn 72000 2000 = sievePrimesBlock36 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock37_certificate :
    primesIn 74000 2000 = sievePrimesBlock37 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock38_certificate :
    primesIn 76000 2000 = sievePrimesBlock38 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock39_certificate :
    primesIn 78000 2000 = sievePrimesBlock39 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock40_certificate :
    primesIn 80000 2000 = sievePrimesBlock40 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock41_certificate :
    primesIn 82000 2000 = sievePrimesBlock41 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock42_certificate :
    primesIn 84000 2000 = sievePrimesBlock42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock43_certificate :
    primesIn 86000 2000 = sievePrimesBlock43 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock44_certificate :
    primesIn 88000 2000 = sievePrimesBlock44 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock45_certificate :
    primesIn 90000 2000 = sievePrimesBlock45 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock46_certificate :
    primesIn 92000 2000 = sievePrimesBlock46 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock47_certificate :
    primesIn 94000 2000 = sievePrimesBlock47 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock48_certificate :
    primesIn 96000 2000 = sievePrimesBlock48 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock49_certificate :
    primesIn 98000 2000 = sievePrimesBlock49 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock50_certificate :
    primesIn 100000 2000 = sievePrimesBlock50 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock51_certificate :
    primesIn 102000 2000 = sievePrimesBlock51 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock52_certificate :
    primesIn 104000 2000 = sievePrimesBlock52 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock53_certificate :
    primesIn 106000 2000 = sievePrimesBlock53 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock54_certificate :
    primesIn 108000 2000 = sievePrimesBlock54 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock55_certificate :
    primesIn 110000 2000 = sievePrimesBlock55 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock56_certificate :
    primesIn 112000 2000 = sievePrimesBlock56 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock57_certificate :
    primesIn 114000 2000 = sievePrimesBlock57 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock58_certificate :
    primesIn 116000 2000 = sievePrimesBlock58 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock59_certificate :
    primesIn 118000 2000 = sievePrimesBlock59 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock60_certificate :
    primesIn 120000 2000 = sievePrimesBlock60 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock61_certificate :
    primesIn 122000 2000 = sievePrimesBlock61 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock62_certificate :
    primesIn 124000 2000 = sievePrimesBlock62 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock63_certificate :
    primesIn 126000 2000 = sievePrimesBlock63 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock64_certificate :
    primesIn 128000 2000 = sievePrimesBlock64 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock65_certificate :
    primesIn 130000 2000 = sievePrimesBlock65 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock66_certificate :
    primesIn 132000 2000 = sievePrimesBlock66 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock67_certificate :
    primesIn 134000 2000 = sievePrimesBlock67 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock68_certificate :
    primesIn 136000 2000 = sievePrimesBlock68 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock69_certificate :
    primesIn 138000 2000 = sievePrimesBlock69 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock70_certificate :
    primesIn 140000 2000 = sievePrimesBlock70 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock71_certificate :
    primesIn 142000 2000 = sievePrimesBlock71 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock72_certificate :
    primesIn 144000 2000 = sievePrimesBlock72 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock73_certificate :
    primesIn 146000 2000 = sievePrimesBlock73 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock74_certificate :
    primesIn 148000 2000 = sievePrimesBlock74 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock75_certificate :
    primesIn 150000 2000 = sievePrimesBlock75 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock76_certificate :
    primesIn 152000 2000 = sievePrimesBlock76 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock77_certificate :
    primesIn 154000 2000 = sievePrimesBlock77 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock78_certificate :
    primesIn 156000 2000 = sievePrimesBlock78 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock79_certificate :
    primesIn 158000 2000 = sievePrimesBlock79 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock80_certificate :
    primesIn 160000 2000 = sievePrimesBlock80 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock81_certificate :
    primesIn 162000 2000 = sievePrimesBlock81 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock82_certificate :
    primesIn 164000 2000 = sievePrimesBlock82 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock83_certificate :
    primesIn 166000 2000 = sievePrimesBlock83 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock84_certificate :
    primesIn 168000 2000 = sievePrimesBlock84 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock85_certificate :
    primesIn 170000 2000 = sievePrimesBlock85 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock86_certificate :
    primesIn 172000 2000 = sievePrimesBlock86 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock87_certificate :
    primesIn 174000 2000 = sievePrimesBlock87 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock88_certificate :
    primesIn 176000 2000 = sievePrimesBlock88 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock89_certificate :
    primesIn 178000 2000 = sievePrimesBlock89 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock90_certificate :
    primesIn 180000 2000 = sievePrimesBlock90 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock91_certificate :
    primesIn 182000 2000 = sievePrimesBlock91 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock92_certificate :
    primesIn 184000 2000 = sievePrimesBlock92 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock93_certificate :
    primesIn 186000 2000 = sievePrimesBlock93 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock94_certificate :
    primesIn 188000 2000 = sievePrimesBlock94 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock95_certificate :
    primesIn 190000 2000 = sievePrimesBlock95 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock96_certificate :
    primesIn 192000 2000 = sievePrimesBlock96 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock97_certificate :
    primesIn 194000 2000 = sievePrimesBlock97 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock98_certificate :
    primesIn 196000 2000 = sievePrimesBlock98 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock99_certificate :
    primesIn 198000 2000 = sievePrimesBlock99 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock100_certificate :
    primesIn 200000 2000 = sievePrimesBlock100 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock101_certificate :
    primesIn 202000 2000 = sievePrimesBlock101 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock102_certificate :
    primesIn 204000 2000 = sievePrimesBlock102 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock103_certificate :
    primesIn 206000 2000 = sievePrimesBlock103 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock104_certificate :
    primesIn 208000 2000 = sievePrimesBlock104 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock105_certificate :
    primesIn 210000 2000 = sievePrimesBlock105 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock106_certificate :
    primesIn 212000 2000 = sievePrimesBlock106 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock107_certificate :
    primesIn 214000 2000 = sievePrimesBlock107 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock108_certificate :
    primesIn 216000 2000 = sievePrimesBlock108 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock109_certificate :
    primesIn 218000 2000 = sievePrimesBlock109 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock110_certificate :
    primesIn 220000 2000 = sievePrimesBlock110 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock111_certificate :
    primesIn 222000 2000 = sievePrimesBlock111 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock112_certificate :
    primesIn 224000 2000 = sievePrimesBlock112 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock113_certificate :
    primesIn 226000 2000 = sievePrimesBlock113 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock114_certificate :
    primesIn 228000 2000 = sievePrimesBlock114 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock115_certificate :
    primesIn 230000 2000 = sievePrimesBlock115 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock116_certificate :
    primesIn 232000 2000 = sievePrimesBlock116 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock117_certificate :
    primesIn 234000 2000 = sievePrimesBlock117 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock118_certificate :
    primesIn 236000 2000 = sievePrimesBlock118 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock119_certificate :
    primesIn 238000 2000 = sievePrimesBlock119 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock120_certificate :
    primesIn 240000 2000 = sievePrimesBlock120 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock121_certificate :
    primesIn 242000 2000 = sievePrimesBlock121 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock122_certificate :
    primesIn 244000 2000 = sievePrimesBlock122 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock123_certificate :
    primesIn 246000 2000 = sievePrimesBlock123 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem sievePrimesBlock124_certificate :
    primesIn 248000 2000 = sievePrimesBlock124 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sievePrimeBlocks_verified : VerifiedPrimeBlocks 0 250000 sievePrimeBlocks := by
  refine .append (b := 2000) (by decide) (by decide) sievePrimesBlock0_certificate ?_
  refine .append (b := 4000) (by decide) (by decide) sievePrimesBlock1_certificate ?_
  refine .append (b := 6000) (by decide) (by decide) sievePrimesBlock2_certificate ?_
  refine .append (b := 8000) (by decide) (by decide) sievePrimesBlock3_certificate ?_
  refine .append (b := 10000) (by decide) (by decide) sievePrimesBlock4_certificate ?_
  refine .append (b := 12000) (by decide) (by decide) sievePrimesBlock5_certificate ?_
  refine .append (b := 14000) (by decide) (by decide) sievePrimesBlock6_certificate ?_
  refine .append (b := 16000) (by decide) (by decide) sievePrimesBlock7_certificate ?_
  refine .append (b := 18000) (by decide) (by decide) sievePrimesBlock8_certificate ?_
  refine .append (b := 20000) (by decide) (by decide) sievePrimesBlock9_certificate ?_
  refine .append (b := 22000) (by decide) (by decide) sievePrimesBlock10_certificate ?_
  refine .append (b := 24000) (by decide) (by decide) sievePrimesBlock11_certificate ?_
  refine .append (b := 26000) (by decide) (by decide) sievePrimesBlock12_certificate ?_
  refine .append (b := 28000) (by decide) (by decide) sievePrimesBlock13_certificate ?_
  refine .append (b := 30000) (by decide) (by decide) sievePrimesBlock14_certificate ?_
  refine .append (b := 32000) (by decide) (by decide) sievePrimesBlock15_certificate ?_
  refine .append (b := 34000) (by decide) (by decide) sievePrimesBlock16_certificate ?_
  refine .append (b := 36000) (by decide) (by decide) sievePrimesBlock17_certificate ?_
  refine .append (b := 38000) (by decide) (by decide) sievePrimesBlock18_certificate ?_
  refine .append (b := 40000) (by decide) (by decide) sievePrimesBlock19_certificate ?_
  refine .append (b := 42000) (by decide) (by decide) sievePrimesBlock20_certificate ?_
  refine .append (b := 44000) (by decide) (by decide) sievePrimesBlock21_certificate ?_
  refine .append (b := 46000) (by decide) (by decide) sievePrimesBlock22_certificate ?_
  refine .append (b := 48000) (by decide) (by decide) sievePrimesBlock23_certificate ?_
  refine .append (b := 50000) (by decide) (by decide) sievePrimesBlock24_certificate ?_
  refine .append (b := 52000) (by decide) (by decide) sievePrimesBlock25_certificate ?_
  refine .append (b := 54000) (by decide) (by decide) sievePrimesBlock26_certificate ?_
  refine .append (b := 56000) (by decide) (by decide) sievePrimesBlock27_certificate ?_
  refine .append (b := 58000) (by decide) (by decide) sievePrimesBlock28_certificate ?_
  refine .append (b := 60000) (by decide) (by decide) sievePrimesBlock29_certificate ?_
  refine .append (b := 62000) (by decide) (by decide) sievePrimesBlock30_certificate ?_
  refine .append (b := 64000) (by decide) (by decide) sievePrimesBlock31_certificate ?_
  refine .append (b := 66000) (by decide) (by decide) sievePrimesBlock32_certificate ?_
  refine .append (b := 68000) (by decide) (by decide) sievePrimesBlock33_certificate ?_
  refine .append (b := 70000) (by decide) (by decide) sievePrimesBlock34_certificate ?_
  refine .append (b := 72000) (by decide) (by decide) sievePrimesBlock35_certificate ?_
  refine .append (b := 74000) (by decide) (by decide) sievePrimesBlock36_certificate ?_
  refine .append (b := 76000) (by decide) (by decide) sievePrimesBlock37_certificate ?_
  refine .append (b := 78000) (by decide) (by decide) sievePrimesBlock38_certificate ?_
  refine .append (b := 80000) (by decide) (by decide) sievePrimesBlock39_certificate ?_
  refine .append (b := 82000) (by decide) (by decide) sievePrimesBlock40_certificate ?_
  refine .append (b := 84000) (by decide) (by decide) sievePrimesBlock41_certificate ?_
  refine .append (b := 86000) (by decide) (by decide) sievePrimesBlock42_certificate ?_
  refine .append (b := 88000) (by decide) (by decide) sievePrimesBlock43_certificate ?_
  refine .append (b := 90000) (by decide) (by decide) sievePrimesBlock44_certificate ?_
  refine .append (b := 92000) (by decide) (by decide) sievePrimesBlock45_certificate ?_
  refine .append (b := 94000) (by decide) (by decide) sievePrimesBlock46_certificate ?_
  refine .append (b := 96000) (by decide) (by decide) sievePrimesBlock47_certificate ?_
  refine .append (b := 98000) (by decide) (by decide) sievePrimesBlock48_certificate ?_
  refine .append (b := 100000) (by decide) (by decide) sievePrimesBlock49_certificate ?_
  refine .append (b := 102000) (by decide) (by decide) sievePrimesBlock50_certificate ?_
  refine .append (b := 104000) (by decide) (by decide) sievePrimesBlock51_certificate ?_
  refine .append (b := 106000) (by decide) (by decide) sievePrimesBlock52_certificate ?_
  refine .append (b := 108000) (by decide) (by decide) sievePrimesBlock53_certificate ?_
  refine .append (b := 110000) (by decide) (by decide) sievePrimesBlock54_certificate ?_
  refine .append (b := 112000) (by decide) (by decide) sievePrimesBlock55_certificate ?_
  refine .append (b := 114000) (by decide) (by decide) sievePrimesBlock56_certificate ?_
  refine .append (b := 116000) (by decide) (by decide) sievePrimesBlock57_certificate ?_
  refine .append (b := 118000) (by decide) (by decide) sievePrimesBlock58_certificate ?_
  refine .append (b := 120000) (by decide) (by decide) sievePrimesBlock59_certificate ?_
  refine .append (b := 122000) (by decide) (by decide) sievePrimesBlock60_certificate ?_
  refine .append (b := 124000) (by decide) (by decide) sievePrimesBlock61_certificate ?_
  refine .append (b := 126000) (by decide) (by decide) sievePrimesBlock62_certificate ?_
  refine .append (b := 128000) (by decide) (by decide) sievePrimesBlock63_certificate ?_
  refine .append (b := 130000) (by decide) (by decide) sievePrimesBlock64_certificate ?_
  refine .append (b := 132000) (by decide) (by decide) sievePrimesBlock65_certificate ?_
  refine .append (b := 134000) (by decide) (by decide) sievePrimesBlock66_certificate ?_
  refine .append (b := 136000) (by decide) (by decide) sievePrimesBlock67_certificate ?_
  refine .append (b := 138000) (by decide) (by decide) sievePrimesBlock68_certificate ?_
  refine .append (b := 140000) (by decide) (by decide) sievePrimesBlock69_certificate ?_
  refine .append (b := 142000) (by decide) (by decide) sievePrimesBlock70_certificate ?_
  refine .append (b := 144000) (by decide) (by decide) sievePrimesBlock71_certificate ?_
  refine .append (b := 146000) (by decide) (by decide) sievePrimesBlock72_certificate ?_
  refine .append (b := 148000) (by decide) (by decide) sievePrimesBlock73_certificate ?_
  refine .append (b := 150000) (by decide) (by decide) sievePrimesBlock74_certificate ?_
  refine .append (b := 152000) (by decide) (by decide) sievePrimesBlock75_certificate ?_
  refine .append (b := 154000) (by decide) (by decide) sievePrimesBlock76_certificate ?_
  refine .append (b := 156000) (by decide) (by decide) sievePrimesBlock77_certificate ?_
  refine .append (b := 158000) (by decide) (by decide) sievePrimesBlock78_certificate ?_
  refine .append (b := 160000) (by decide) (by decide) sievePrimesBlock79_certificate ?_
  refine .append (b := 162000) (by decide) (by decide) sievePrimesBlock80_certificate ?_
  refine .append (b := 164000) (by decide) (by decide) sievePrimesBlock81_certificate ?_
  refine .append (b := 166000) (by decide) (by decide) sievePrimesBlock82_certificate ?_
  refine .append (b := 168000) (by decide) (by decide) sievePrimesBlock83_certificate ?_
  refine .append (b := 170000) (by decide) (by decide) sievePrimesBlock84_certificate ?_
  refine .append (b := 172000) (by decide) (by decide) sievePrimesBlock85_certificate ?_
  refine .append (b := 174000) (by decide) (by decide) sievePrimesBlock86_certificate ?_
  refine .append (b := 176000) (by decide) (by decide) sievePrimesBlock87_certificate ?_
  refine .append (b := 178000) (by decide) (by decide) sievePrimesBlock88_certificate ?_
  refine .append (b := 180000) (by decide) (by decide) sievePrimesBlock89_certificate ?_
  refine .append (b := 182000) (by decide) (by decide) sievePrimesBlock90_certificate ?_
  refine .append (b := 184000) (by decide) (by decide) sievePrimesBlock91_certificate ?_
  refine .append (b := 186000) (by decide) (by decide) sievePrimesBlock92_certificate ?_
  refine .append (b := 188000) (by decide) (by decide) sievePrimesBlock93_certificate ?_
  refine .append (b := 190000) (by decide) (by decide) sievePrimesBlock94_certificate ?_
  refine .append (b := 192000) (by decide) (by decide) sievePrimesBlock95_certificate ?_
  refine .append (b := 194000) (by decide) (by decide) sievePrimesBlock96_certificate ?_
  refine .append (b := 196000) (by decide) (by decide) sievePrimesBlock97_certificate ?_
  refine .append (b := 198000) (by decide) (by decide) sievePrimesBlock98_certificate ?_
  refine .append (b := 200000) (by decide) (by decide) sievePrimesBlock99_certificate ?_
  refine .append (b := 202000) (by decide) (by decide) sievePrimesBlock100_certificate ?_
  refine .append (b := 204000) (by decide) (by decide) sievePrimesBlock101_certificate ?_
  refine .append (b := 206000) (by decide) (by decide) sievePrimesBlock102_certificate ?_
  refine .append (b := 208000) (by decide) (by decide) sievePrimesBlock103_certificate ?_
  refine .append (b := 210000) (by decide) (by decide) sievePrimesBlock104_certificate ?_
  refine .append (b := 212000) (by decide) (by decide) sievePrimesBlock105_certificate ?_
  refine .append (b := 214000) (by decide) (by decide) sievePrimesBlock106_certificate ?_
  refine .append (b := 216000) (by decide) (by decide) sievePrimesBlock107_certificate ?_
  refine .append (b := 218000) (by decide) (by decide) sievePrimesBlock108_certificate ?_
  refine .append (b := 220000) (by decide) (by decide) sievePrimesBlock109_certificate ?_
  refine .append (b := 222000) (by decide) (by decide) sievePrimesBlock110_certificate ?_
  refine .append (b := 224000) (by decide) (by decide) sievePrimesBlock111_certificate ?_
  refine .append (b := 226000) (by decide) (by decide) sievePrimesBlock112_certificate ?_
  refine .append (b := 228000) (by decide) (by decide) sievePrimesBlock113_certificate ?_
  refine .append (b := 230000) (by decide) (by decide) sievePrimesBlock114_certificate ?_
  refine .append (b := 232000) (by decide) (by decide) sievePrimesBlock115_certificate ?_
  refine .append (b := 234000) (by decide) (by decide) sievePrimesBlock116_certificate ?_
  refine .append (b := 236000) (by decide) (by decide) sievePrimesBlock117_certificate ?_
  refine .append (b := 238000) (by decide) (by decide) sievePrimesBlock118_certificate ?_
  refine .append (b := 240000) (by decide) (by decide) sievePrimesBlock119_certificate ?_
  refine .append (b := 242000) (by decide) (by decide) sievePrimesBlock120_certificate ?_
  refine .append (b := 244000) (by decide) (by decide) sievePrimesBlock121_certificate ?_
  refine .append (b := 246000) (by decide) (by decide) sievePrimesBlock122_certificate ?_
  refine .append (b := 248000) (by decide) (by decide) sievePrimesBlock123_certificate ?_
  refine .append (b := 250000) (by decide) (by decide) sievePrimesBlock124_certificate ?_
  exact .done _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_190232 : SparseSieveCover 190232 250001 := by
  refine sparseSieveRow (b := 195996) (f := 10944) (cut := 443)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 86) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 201865) (f := 11084) (cut := 449)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 87) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 207826) (f := 11505) (cut := 463)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 90) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 213867) (f := 11646) (cut := 467)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 91) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 219993) (f := 11786) (cut := 479)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 92) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 226202) (f := 12066) (cut := 491)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 94) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 232471) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 238844) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 245262) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 250001) (f := 12347) (cut := 503)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 96) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact .done _

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_137287 : SparseSieveCover 137287 250001 := by
  refine sparseSieveRow (b := 142295) (f := 6481) (cut := 449)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 87) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 147370) (f := 6562) (cut := 457)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 88) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 152485) (f := 6805) (cut := 467)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 91) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 157648) (f := 6886) (cut := 479)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 92) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 162858) (f := 6967) (cut := 487)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 93) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 168128) (f := 9962) (cut := 401)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 79) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 173503) (f := 10102) (cut := 409)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 80) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 178986) (f := 10383) (cut := 421)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 82) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 184570) (f := 10523) (cut := 431)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 83) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 190232) (f := 10804) (cut := 439)
    (P := sieveFreePrimes 9) (Q := sieveTailPrimes 9 85) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_190232

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_91388 : SparseSieveCover 91388 250001 := by
  refine sparseSieveRow (b := 95546) (f := 5185) (cut := 353)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 71) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 99811) (f := 5266) (cut := 359)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 72) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 104180) (f := 5428) (cut := 373)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 74) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 108656) (f := 5590) (cut := 383)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 76) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 113218) (f := 5671) (cut := 389)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 77) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 117873) (f := 5833) (cut := 401)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 79) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 122614) (f := 5914) (cut := 409)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 80) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 127444) (f := 6076) (cut := 421)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 82) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 132333) (f := 6238) (cut := 433)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 84) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 137287) (f := 6400) (cut := 443)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 86) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_137287

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_56222 : SparseSieveCover 56222 250001 := by
  refine sparseSieveRow (b := 59173) (f := 3889) (cut := 257)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 55) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 62247) (f := 4051) (cut := 269)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 57) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 65460) (f := 4132) (cut := 271)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 58) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 68803) (f := 4375) (cut := 283)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 61) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 72264) (f := 4456) (cut := 293)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 62) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 75843) (f := 4537) (cut := 307)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 63) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 79555) (f := 4699) (cut := 313)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 65) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 83378) (f := 4780) (cut := 317)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 66) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 87326) (f := 4942) (cut := 337)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 68) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 91388) (f := 5023) (cut := 347)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 69) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_91388

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_31969 : SparseSieveCover 31969 250001 := by
  refine sparseSieveRow (b := 34010) (f := 1965) (cut := 223)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 48) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 36143) (f := 2105) (cut := 233)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 51) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 38364) (f := 2152) (cut := 239)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 52) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 40675) (f := 2246) (cut := 251)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 54) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 43047) (f := 2293) (cut := 257)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 55) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 45513) (f := 2386) (cut := 269)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 57) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 48051) (f := 2433) (cut := 271)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 58) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 50668) (f := 2526) (cut := 281)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 60) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 53385) (f := 3727) (cut := 241)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 53) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 56222) (f := 3727) (cut := 241)
    (P := sieveFreePrimes 8) (Q := sieveTailPrimes 8 53) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_56222

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_16426 : SparseSieveCover 16426 250001 := by
  refine sparseSieveRow (b := 17631) (f := 946) (cut := 173)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 40) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 18916) (f := 1404) (cut := 151)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 36) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 20282) (f := 1497) (cut := 163)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 38) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 21734) (f := 1544) (cut := 167)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 39) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 23258) (f := 1591) (cut := 173)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 40) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 24873) (f := 1685) (cut := 181)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 42) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 26579) (f := 1778) (cut := 193)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 44) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 28378) (f := 1825) (cut := 197)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 45) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 30001) (f := 1872) (cut := 199)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 46) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 31969) (f := 1918) (cut := 211)
    (P := sieveFreePrimes 7) (Q := sieveTailPrimes 7 47) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_31969

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_7332 : SparseSieveCover 7332 250001 := by
  refine sparseSieveRow (b := 8003) (f := 622) (cut := 107)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 28) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 8729) (f := 676) (cut := 113)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 30) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 9498) (f := 676) (cut := 113)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 30) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 10322) (f := 703) (cut := 127)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 31) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 11204) (f := 757) (cut := 137)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 33) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 12141) (f := 784) (cut := 139)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 34) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 13128) (f := 811) (cut := 149)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 35) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 14174) (f := 838) (cut := 151)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 36) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 15274) (f := 865) (cut := 157)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 37) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 16426) (f := 919) (cut := 167)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 39) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_16426

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_from_2913 : SparseSieveCover 2913 250001 := by
  refine sparseSieveRow (b := 3218) (f := 250) (cut := 71)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 20) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 3545) (f := 266) (cut := 73)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 21) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 3896) (f := 282) (cut := 79)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 22) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 4272) (f := 297) (cut := 83)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 23) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 4680) (f := 433) (cut := 73)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 21) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 5122) (f := 460) (cut := 79)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 22) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 5608) (f := 487) (cut := 83)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 23) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 6135) (f := 514) (cut := 89)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 24) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 6710) (f := 568) (cut := 101)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 26) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 7332) (f := 595) (cut := 103)
    (P := sieveFreePrimes 6) (Q := sieveTailPrimes 6 27) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_7332

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem sparseSieveCover_to_250001 : SparseSieveCover 1001 250001 := by
  refine sparseSieveRow (b := 1118) (f := 100) (cut := 43)
    (P := sieveFreePrimes 4) (Q := sieveTailPrimes 4 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1246) (f := 100) (cut := 43)
    (P := sieveFreePrimes 4) (Q := sieveTailPrimes 4 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1393) (f := 157) (cut := 43)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 14) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1555) (f := 172) (cut := 47)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 15) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1734) (f := 172) (cut := 47)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 15) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 1932) (f := 188) (cut := 53)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 16) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2144) (f := 204) (cut := 59)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 17) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2379) (f := 219) (cut := 61)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 18) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2639) (f := 219) (cut := 61)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 18) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  refine sparseSieveRow (b := 2913) (f := 235) (cut := 67)
    (P := sieveFreePrimes 5) (Q := sieveTailPrimes 5 19) sievePrimeBlocks_verified
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by rw [sieveTailPairCost]; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  exact sparseSieveCover_from_2913

end ErdosSelfridge

open Finset

namespace CubicSmoothCover

def smooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ v.primeFactors, p ≤ P)

def coprimeUpTo (M x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (M.Coprime ·)

private theorem coprime_primorial {P u : ℕ} :
    (primorial P).Coprime u ↔ ∀ q, q.Prime → q ∣ u → P < q := by
  constructor
  · intro h q hq hqu
    by_contra! hqP
    exact hq.ne_one (Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd
      (hq.dvd_primorial_iff.mpr hqP) hqu))
  · intro h
    by_contra hn
    have hg : (primorial P).gcd u ≠ 1 := hn
    let q := ((primorial P).gcd u).minFac
    have hq := Nat.minFac_prime hg
    have hd : q ∣ (primorial P).gcd u := Nat.minFac_dvd _
    exact (not_lt_of_ge (hq.dvd_primorial_iff.mp (hd.trans (Nat.gcd_dvd_left _ _))))
      (h q hq (hd.trans (Nat.gcd_dvd_right _ _)))

private theorem greedy {P B : ℕ} (u v : ℕ) (hu : 0 < u) (hv : v ∈ smooth P B)
    (horder : ∀ q, q.Prime → q ∣ u → ∀ p ∈ v.primeFactors, p ≤ q) :
    ∃ a b : ℕ, 0 < a ∧ b ∈ smooth P B ∧ a * b = u * v ∧
      ((primorial P).Coprime a ∨
        ∃ p, p.Prime ∧ p ≤ P ∧ p ∣ a ∧ B < p * b ∧
          (∀ q, q.Prime → q ∣ a → p ≤ q) ∧ ∀ q ∈ b.primeFactors, q ≤ p) := by
  by_cases hcop : (primorial P).Coprime u
  · exact ⟨u, v, hu, hv, rfl, Or.inl hcop⟩
  have hun : u ≠ 1 := by
    intro he; exact hcop (he ▸ Nat.coprime_one_right _)
  let p := u.minFac
  have hp : p.Prime := Nat.minFac_prime hun
  have hpdvd : p ∣ u := Nat.minFac_dvd u
  have hpmin (q : ℕ) (hq : q.Prime) (hqu : q ∣ u) : p ≤ q :=
    Nat.minFac_le_of_dvd hq.two_le hqu
  have hpP : p ≤ P := by
    by_contra! hlt
    exact hcop (coprime_primorial.mpr
      (fun q hq hd => hlt.trans_le (hpmin q hq hd)))
  by_cases hnext : p * v ≤ B
  · have hvpos : 0 < v := by
      have := (mem_Icc.mp (mem_filter.mp hv).1).1
      omega
    have hdivide : u / p * p = u := Nat.div_mul_cancel hpdvd
    have hu' : 0 < u / p := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, zero_mul] at hdivide
      omega
    have hv' : p * v ∈ smooth P B := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hp.pos hvpos), hnext⟩, ?_⟩
      intro q hq
      rcases (Nat.mem_primeFactors.mp hq).1.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hq)
        with hd | hd
      · have he := (Nat.dvd_prime hp).mp hd
        rcases he with he | he
        · exact ((Nat.prime_of_mem_primeFactors hq).ne_one he).elim
        · simpa [he] using hpP
      · exact (mem_filter.mp hv).2 q ((Nat.prime_of_mem_primeFactors hq).mem_primeFactors
          hd hvpos.ne')
    have horder' (q : ℕ) (hq : q.Prime) (hqu : q ∣ u / p)
        (w : ℕ) (hw : w ∈ (p * v).primeFactors) : w ≤ q := by
      have hqu' : q ∣ u := hqu.trans (show u / p ∣ u by exact ⟨p, hdivide.symm⟩)
      rcases (Nat.prime_of_mem_primeFactors hw).dvd_mul.mp (Nat.dvd_of_mem_primeFactors hw)
        with hd | hd
      · rcases (Nat.dvd_prime hp).mp hd with he | he
        · exact ((Nat.prime_of_mem_primeFactors hw).ne_one he).elim
        · simpa [he] using hpmin q hq hqu'
      · exact horder q hq hqu' w ((Nat.prime_of_mem_primeFactors hw).mem_primeFactors
          hd hvpos.ne')
    obtain ⟨a, b, ha, hb, hab, ht⟩ := greedy (u / p) (p * v) hu' hv' horder'
    exact ⟨a, b, ha, hb, hab.trans (by rw [← mul_assoc, hdivide]), ht⟩
  · exact ⟨u, v, hu, hv, rfl, Or.inr
      ⟨p, hp, hpP, hpdvd, lt_of_not_ge hnext, hpmin, horder p hp hpdvd⟩⟩
termination_by u
decreasing_by exact Nat.div_lt_self hu hp.one_lt

def multiples (x p d : ℕ) : Finset ℕ :=
  (coprimeUpTo (primorial (p - 1)) (x / (p * d))).image (p * ·)

def remaining (P : ℕ) (d : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  coprimeUpTo (primorial P) x ∪ (Nat.primesLE P).biUnion (fun p => multiples x p (d p))

theorem remaining_pos {P : ℕ} {d : ℕ → ℕ} {x a : ℕ} (ha : a ∈ remaining P d x) :
    0 < a := by
  rcases mem_union.mp ha with hr | hr
  · have := (mem_Icc.mp (mem_filter.mp hr).1).1
    omega
  · obtain ⟨p, hp, hap⟩ := mem_biUnion.mp hr
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hap
    have hp' : p.Prime := Nat.prime_of_mem_primesLE hp
    have hw' := (mem_Icc.mp (mem_filter.mp hw).1).1
    exact Nat.mul_pos hp'.pos (by omega)

theorem smooth_pos {P B v : ℕ} (hv : v ∈ smooth P B) : 0 < v := by
  have := (mem_Icc.mp (mem_filter.mp hv).1).1
  omega

theorem factor {P B a x : ℕ} {d : ℕ → ℕ} (hB : 1 ≤ B) (ha : 0 < a) (hax : a ≤ x)
    (hd : ∀ p b, p.Prime → p ≤ P → b ∈ smooth P B → B < p * b →
      (∀ q ∈ b.primeFactors, q ≤ p) → d p ≤ b)
    (hdpos : ∀ p ∈ Nat.primesLE P, 0 < d p) :
    ∃ u ∈ remaining P d x, ∃ v ∈ smooth P B, u * v = a := by
  have h1 : 1 ∈ smooth P B := by simp [smooth, hB]
  obtain ⟨u, v, hu, hv, huv, hdone⟩ :=
    greedy a 1 ha h1 (by simp)
  rw [mul_one] at huv
  have hux : u ≤ x :=
    (Nat.le_mul_of_pos_right _ (smooth_pos hv)).trans (huv ▸ hax)
  refine ⟨u, ?_, v, hv, huv⟩
  rcases hdone with hcop | ⟨p, hp, hple, hpu, hbig, hmin, hsmall⟩
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hux⟩, hcop⟩)
  · have hpmem : p ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨hple, hp⟩
    have hdiv : u / p * p = u := Nat.div_mul_cancel hpu
    have hmul : u / p * (p * d p) ≤ x := by
      rw [← mul_assoc, hdiv]
      exact (Nat.mul_le_mul_left u (hd p v hp hple hv hbig hsmall)).trans (huv ▸ hax)
    have hun : 1 ≤ u / p := by
      by_contra! hz
      have he : u / p = 0 := Nat.lt_one_iff.mp hz
      rw [he, zero_mul] at hdiv
      omega
    refine mem_union_right _ (mem_biUnion.mpr ⟨p, hpmem, mem_image.mpr
      ⟨u / p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hun, ?_⟩, ?_⟩, ?_⟩⟩)
    · exact (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos (hdpos p hpmem))).mpr hmul
    · exact coprime_primorial.mpr (fun q hq hqdiv => by
        have := hmin q hq (hqdiv.trans (show u / p ∣ u by exact ⟨p, hdiv.symm⟩))
        exact lt_of_lt_of_le (Nat.sub_lt (hp.pos) (by decide)) this)
    · rwa [mul_comm]

end CubicSmoothCover

namespace CubicSmoothCover

private theorem coprimeUpTo_period (M x : ℕ) :
    (coprimeUpTo M (x + M)).card = (coprimeUpTo M x).card + M.totient := by
  let A := Icc 1 x
  let B := Ico (x + 1) (x + 1 + M)
  have hsplit : Icc 1 (x + M) = A ∪ B := by
    ext i
    simp only [A, B, mem_union, mem_Icc, mem_Ico]
    omega
  have hdis : Disjoint A B := by
    refine disjoint_left.mpr fun i hi hj => ?_
    have hi' := (mem_Icc.mp hi).2
    have hj' := (mem_Ico.mp hj).1
    omega
  unfold coprimeUpTo
  rw [hsplit, filter_union, card_union_of_disjoint (hdis.mono
    (filter_subset _ _) (filter_subset _ _))]
  exact congrArg _ (Nat.filter_coprime_Ico_eq_totient M (x + 1))

private def prefixCount (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixCount M n + if M.Coprime (n + 1) then 1 else 0

private theorem card_coprimeUpTo (M x : ℕ) :
    (coprimeUpTo M x).card = prefixCount M x := by
  induction x with
  | zero => simp [coprimeUpTo, prefixCount]
  | succ x ih =>
    have hsplit : Icc 1 (x + 1) = insert (x + 1) (Icc 1 x) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    rw [coprimeUpTo, hsplit, filter_insert, prefixCount, ← ih]
    split
    · rw [card_insert_of_notMem]
      · rfl
      · simp [mem_filter, mem_Icc]
    · simp only [coprimeUpTo, add_zero]

private def scan (M φ D : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, t, c => decide (M * c ≤ φ * t + D)
  | n + 1, t, c => decide (M * c ≤ φ * t + D) &&
      scan M φ D n (t + 1) (c + if M.Coprime (t + 1) then 1 else 0)

private theorem scan_sound {M φ D n t : ℕ} (h : scan M φ D n t (prefixCount M t) = true)
    (r : ℕ) (ht : t ≤ r) (hr : r ≤ t + n) :
    M * prefixCount M r ≤ φ * r + D := by
  induction n generalizing t with
  | zero =>
    have he : r = t := by omega
    simpa [scan, he] using h
  | succ n ih =>
    simp only [scan, Bool.and_eq_true, decide_eq_true_eq, ← prefixCount.eq_2] at h
    by_cases he : r = t
    · simpa [he] using h.1
    · exact ih h.2 (by omega) (by omega)

private theorem card_le_of_scan {M D : ℕ} (hM : 0 < M)
    (h : scan M M.totient D (M - 1) 0 0 = true) (x : ℕ) :
    M * (coprimeUpTo M x).card ≤ M.totient * x + D := by
  have hmod : x % M ≤ M - 1 := by have := Nat.mod_lt x hM; omega
  have hpre : M * (coprimeUpTo M (x % M)).card ≤ M.totient * (x % M) + D := by
    rw [card_coprimeUpTo]
    exact scan_sound (t := 0) (n := M - 1) h _ (Nat.zero_le _) (by omega)
  suffices ∀ q : ℕ, M * (coprimeUpTo M (x % M + q * M)).card ≤
      M.totient * (x % M + q * M) + D by
    have H := this (x / M)
    rwa [mul_comm (x / M), Nat.mod_add_div] at H
  intro q
  induction q with
  | zero => simpa using hpre
  | succ q ih =>
    rw [Nat.succ_mul, ← add_assoc, coprimeUpTo_period, mul_add, mul_add, mul_comm M M.totient]
    omega

private theorem coprime_card_1 (x : ℕ) : (coprimeUpTo 1 x).card ≤ x := by
  simpa using card_le_of_scan (M := 1) (D := 0) (by decide) (by decide) x

private theorem coprime_card_2 (x : ℕ) : 2 * (coprimeUpTo 2 x).card ≤ x + 1 := by
  have hφ : Nat.totient 2 = 1 := by decide
  simpa [hφ] using card_le_of_scan (M := 2) (D := 1) (by decide) (by decide) x

private theorem coprime_card_6 (x : ℕ) : 6 * (coprimeUpTo 6 x).card ≤ 2*x + 4 := by
  have hφ : Nat.totient 6 = 2 := by decide
  simpa [hφ] using card_le_of_scan (M := 6) (D := 4) (by decide) (by decide) x

private theorem coprime_card_30 (x : ℕ) : 30 * (coprimeUpTo 30 x).card ≤ 8*x + 28 := by
  have hφ : Nat.totient 30 = 8 := by decide
  simpa [hφ] using card_le_of_scan (M := 30) (D := 28) (by decide) (by decide) x

set_option maxRecDepth 10000 in
private theorem coprime_card_210 (x : ℕ) : 210 * (coprimeUpTo 210 x).card ≤ 48*x + 318 := by
  have hφ : Nat.totient 210 = 48 := by decide
  simpa [hφ] using card_le_of_scan (M := 210) (D := 318) (by decide) (by rw [hφ]; decide) x

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1000000 in
private theorem coprime_card_2310 (x : ℕ) :
    2310 * (coprimeUpTo 2310 x).card ≤ 480*x + 5820 := by
  have hφ : Nat.totient 2310 = 480 := by decide
  simpa [hφ] using card_le_of_scan (M := 2310) (D := 5820) (by decide) (by rw [hφ]; decide) x

end CubicSmoothCover

namespace CubicSmoothCover

def cutoff100 : ℕ → ℕ
  | 2 => 64
  | 3 => 36
  | 5 => 21
  | 7 => 15
  | 11 => 10
  | _ => 1

private theorem primes_11 : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide

private def trialSmooth (P B : ℕ) : Finset ℕ :=
  (Icc 1 B).filter (fun v => ∀ p ∈ Nat.primesLE B, p ∣ v → p ≤ P)

private theorem trialSmooth_eq (P B : ℕ) : trialSmooth P B = smooth P B := by
  ext v
  simp only [trialSmooth, smooth, mem_filter]
  refine and_congr_right fun hv => ⟨?_, ?_⟩
  · intro h q hq
    exact h q (Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hq).trans
      (mem_Icc.mp hv).2, Nat.prime_of_mem_primeFactors hq⟩) (Nat.dvd_of_mem_primeFactors hq)
  · intro h q hq hdiv
    exact h q ((Nat.prime_of_mem_primesLE hq).mem_primeFactors hdiv
      (by have := (mem_Icc.mp hv).1; omega))


set_option maxRecDepth 12000 in
private theorem cutoff_100_valid {p b : ℕ} (hp : p.Prime) (hple : p ≤ 11)
    (hb : b ∈ smooth 11 100) (hbig : 100 < p * b) (hsm : ∀ q ∈ b.primeFactors, q ≤ p) :
    cutoff100 p ≤ b := by
  have hp' : p ∈ Nat.primesLE 11 := Nat.mem_primesLE.mpr ⟨hple, hp⟩
  rw [primes_11] at hp'
  simp only [mem_insert, mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · have hcheck : ∀ t : Fin 13, 51 + t.val ∉ trialSmooth 2 100 := by decide
    by_contra! hs
    change b < 64 at hs
    have hb' : 51 ≤ b := by omega
    let t : Fin 13 := ⟨b - 51, by omega⟩
    have hmem : b ∈ smooth 2 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · have hcheck : ∀ t : Fin 2, 34 + t.val ∉ trialSmooth 3 100 := by decide
    by_contra! hs
    change b < 36 at hs
    have hb' : 34 ≤ b := by omega
    let t : Fin 2 := ⟨b - 34, by omega⟩
    have hmem : b ∈ smooth 3 100 := mem_filter.mpr ⟨(mem_filter.mp hb).1, hsm⟩
    rw [← trialSmooth_eq] at hmem
    exact hcheck t (by simpa [t, Nat.add_sub_of_le hb'] using hmem)
  · change 21 ≤ b
    omega
  · change 15 ≤ b
    omega
  · change 10 ≤ b
    omega

theorem factor100 {a x : ℕ} (ha : 0 < a) (hax : a ≤ x) :
    ∃ u ∈ remaining 11 cutoff100 x, ∃ v ∈ smooth 11 100, u * v = a := by
  apply factor (by decide) ha hax
  · intro p b hp hple hb hbig hsm
    exact cutoff_100_valid hp hple hb hbig hsm
  · intro p hp
    rw [primes_11] at hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem multiples_card (x p d : ℕ) (hp : 0 < p) :
    (multiples x p d).card = (coprimeUpTo (primorial (p - 1)) (x / (p * d))).card := by
  apply card_image_of_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

private theorem aggregate_100 (x : ℕ) :
    (remaining 11 cutoff100 x).card ≤ (coprimeUpTo 2310 x).card +
      ((coprimeUpTo 1 (x / 128)).card + (coprimeUpTo 2 (x / 108)).card +
      (coprimeUpTo 6 (x / 105)).card + (coprimeUpTo 30 (x / 105)).card +
      (coprimeUpTo 210 (x / 110)).card) := by
  have hprim : primorial 11 = 2310 := by decide
  have h₂ : primorial (2 - 1) = 1 := by decide
  have h₃ : primorial (3 - 1) = 2 := by decide
  have h₅ : primorial (5 - 1) = 6 := by decide
  have h₇ : primorial (7 - 1) = 30 := by decide
  have h₁₁ : primorial (11 - 1) = 210 := by decide
  have hm (p : ℕ) (hp : 0 < p) := multiples_card x p (cutoff100 p) hp
  have h := (card_union_le (s := coprimeUpTo (primorial 11) x)
    ((Nat.primesLE 11).biUnion (fun p => multiples x p (cutoff100 p)))).trans
    (Nat.add_le_add_left (card_biUnion_le) _)
  rw [primes_11] at h
  have hf : ((remaining 11 cutoff100 x).card) ≤
      (coprimeUpTo (primorial 11) x).card +
        ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), (multiples x p (cutoff100 p)).card := by
    simpa only [remaining, primes_11] using h
  rw [hprim] at hf
  simp only [sum_insert (by decide : 2 ∉ ({3, 5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 3 ∉ ({5, 7, 11} : Finset ℕ)),
    sum_insert (by decide : 5 ∉ ({7, 11} : Finset ℕ)),
    sum_insert (by decide : 7 ∉ ({11} : Finset ℕ)), sum_singleton] at hf
  rw [hm 2 (by decide), hm 3 (by decide), hm 5 (by decide),
    hm 7 (by decide), hm 11 (by decide), h₂, h₃, h₅, h₇, h₁₁] at hf
  simp only [cutoff100] at hf
  norm_num1 at hf
  omega

theorem remaining_100_card (x : ℕ) :
    10000 * (remaining 11 cutoff100 x).card ≤ 2281 * x + 62000 := by
  have H := aggregate_100 x
  have h₁ := coprime_card_1 (x / 128)
  have h₂ := coprime_card_2 (x / 108)
  have h₆ := coprime_card_6 (x / 105)
  have h₃₀ := coprime_card_30 (x / 105)
  have h₂₁₀ := coprime_card_210 (x / 110)
  have h₂₃₁₀ := coprime_card_2310 x
  have hdiv₁ : 128 * (x / 128) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 128
  have hdiv₂ : 108 * (x / 108) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 108
  have hdiv₃ : 105 * (x / 105) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 105
  have hdiv₄ : 110 * (x / 110) ≤ x := by simpa [mul_comm] using Nat.div_mul_le_self x 110
  omega

end CubicSmoothCover

namespace CubicSmoothCover

def ratios (V : Finset ℕ) : Finset ℚ :=
  ((V ×ˢ V).filter (fun w => w.2 < w.1)).image (fun w => (w.1 : ℚ) / w.2)

/-- Bound the surplus over one factorization per first factor by distinct ratios in the
second factors, when products of two elements determine the unordered pair. -/
theorem pair_count_ratios (A U V : Finset ℕ)
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hfactor : ∀ a ∈ A, ∃ u ∈ U, ∃ v ∈ V, u * v = a)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a * b = c * d → (a ::ₘ b ::ₘ (0 : Multiset ℕ)) = c ::ₘ d ::ₘ 0) :
    A.card ≤ U.card + (ratios V).card := by
  classical
  have hchoose (a : A) : ∃ u : ℕ, u ∈ U ∧ ∃ v ∈ V, u * v = a.val := hfactor a.val a.prop
  let first (a : A) : ℕ := (hchoose a).choose
  have hfirst (a : A) := (hchoose a).choose_spec
  let N (u : ℕ) := V.filter (fun v => ∃ h : u * v ∈ A, first ⟨u * v, h⟩ = u)
  have hmem {u v : ℕ} (hv : v ∈ N u) : u * v ∈ A := (mem_filter.mp hv).2.choose
  have hlabel {u v : ℕ} (hv : v ∈ N u) : first ⟨u * v, hmem hv⟩ = u :=
    (mem_filter.mp hv).2.choose_spec
  let base (u : ℕ) := if h : (N u).Nonempty then (N u).min' h else 0
  have hbase {u : ℕ} (h : (N u).Nonempty) : base u ∈ N u := by
    simpa [base, h] using (N u).min'_mem h
  have hb_le {u v : ℕ} (hv : v ∈ N u) : base u ≤ v := by
    have h : (N u).Nonempty := ⟨v, hv⟩
    simpa [base, h] using (N u).min'_le v hv
  let E := U.sigma (fun u => (N u).erase (base u))
  let quotient (p : Sigma (fun _ : ℕ => ℕ)) : ℚ := (p.2 : ℚ) / base p.1
  have hf (p : Sigma (fun _ : ℕ => ℕ)) (hp : p ∈ E) :
      p.1 ∈ U ∧ p.2 ∈ N p.1 ∧ base p.1 ∈ N p.1 ∧ base p.1 < p.2 := by
    have h := mem_sigma.mp hp
    have h' := mem_erase.mp h.2
    exact ⟨h.1, h'.2, hbase ⟨_, h'.2⟩, lt_of_le_of_ne (hb_le h'.2) (Ne.symm h'.1)⟩
  have hquot : Set.MapsTo quotient E (ratios V) := by
    intro p hp
    obtain ⟨_, hv, hb, hlt⟩ := hf p hp
    exact mem_image.mpr ⟨(p.2, base p.1), mem_filter.mpr
      ⟨mem_product.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hb).1⟩, hlt⟩, rfl⟩
  have hinj : Set.InjOn quotient E := by
    rintro ⟨u, v⟩ hu ⟨w, z⟩ hw hq
    obtain ⟨hu, hv, hb, hlt⟩ := hf ⟨u,v⟩ hu
    obtain ⟨hw, hz, hc, hlt'⟩ := hf ⟨w,z⟩ hw
    change (v : ℚ) / (base u : ℚ) = (z : ℚ) / (base w : ℚ) at hq
    have hu0 : (base u : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hb).1).ne'
    have hw0 : (base w : ℚ) ≠ 0 := by exact_mod_cast (hV _ (mem_filter.mp hc).1).ne'
    have hr : v * base w = z * base u := by exact_mod_cast (div_eq_div_iff hu0 hw0).mp hq
    have hprod : (u * v) * (w * base w) = (w * z) * (u * base u) := by
      rw [show u * v * (w * base w) = (u * w) * (v * base w) by ring, hr]
      ring
    have he := hpair _ (hmem hv) _ (hmem hc)
      _ (hmem hz) _ (hmem hb) hprod
    have hm : u * v ∈ w * z ::ₘ u * base u ::ₘ (0 : Multiset ℕ) :=
      he ▸ Multiset.mem_cons_self _ _
    have hval : u * v = w * z := by
      rcases (by simpa using hm : u * v = w * z ∨ u * v = u * base u) with h | h
      · exact h
      · exact (ne_of_gt (Nat.mul_lt_mul_of_pos_left hlt (hU u hu)) h).elim
    have hl : (⟨u * v, hmem hv⟩ : A) = ⟨w * z, hmem hz⟩ := Subtype.ext hval
    have huw : u = w := (hlabel hv).symm.trans ((congrArg first hl).trans (hlabel hz))
    subst w
    have heq : v = z := Nat.eq_of_mul_eq_mul_left (hU u hu) hval
    subst z
    rfl
  have heCard : E.card ≤ (ratios V).card := card_le_card_of_injOn quotient hquot hinj
  have hsum : (∑ u ∈ U, (N u).card) ≤ U.card + E.card := by
    rw [card_sigma]
    calc
      (∑ u ∈ U, (N u).card) ≤ ∑ u ∈ U, (1 + ((N u).erase (base u)).card) := by
        refine sum_le_sum fun u _ => ?_
        by_cases h : (N u).Nonempty
        · rw [card_erase_of_mem (hbase h)]
          have := card_pos.mpr h
          omega
        · simp [not_nonempty_iff_eq_empty.mp h]
      _ = _ := by rw [sum_add_distrib]; simp
  let f (p : Sigma (fun _ : ℕ => ℕ)) := p.1 * p.2
  have hsubset : A ⊆ (U.sigma N).image f := by
    intro a ha
    obtain ⟨hu, v, hv, hmul⟩ := hfirst ⟨a, ha⟩
    let u := first ⟨a, ha⟩
    have ha' : u * v ∈ A := hmul ▸ ha
    have hs : (⟨u * v, ha'⟩ : A) = ⟨a, ha⟩ := Subtype.ext hmul
    exact mem_image.mpr ⟨⟨u, v⟩, mem_sigma.mpr ⟨hu,
      mem_filter.mpr ⟨hv, ⟨ha', congrArg first hs⟩⟩⟩, hmul⟩
  exact ((card_le_card hsubset).trans card_image_le).trans
    (by rw [card_sigma]; exact hsum.trans (Nat.add_le_add_left heCard _))

end CubicSmoothCover

namespace CubicSmoothCover

private def reducedPairs (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V ×ˢ V).filter (fun w => w.2 < w.1 ∧ w.1.Coprime w.2)

private theorem smooth_of_dvd {P B a b : ℕ} (hb : b ∈ smooth P B)
    (ha : 0 < a) (hdiv : a ∣ b) : a ∈ smooth P B := by
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨ha, (Nat.le_of_dvd (smooth_pos hb) hdiv).trans
    (mem_Icc.mp (mem_filter.mp hb).1).2⟩, ?_⟩
  intro p hp
  exact (mem_filter.mp hb).2 _ ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
    ((Nat.dvd_of_mem_primeFactors hp).trans hdiv) (smooth_pos hb).ne')

private theorem ratios_le_reduced (P B : ℕ) :
    (ratios (smooth P B)).card ≤ (reducedPairs (smooth P B)).card := by
  refine (card_le_card (t := (reducedPairs (smooth P B)).image
    (fun z => (z.1 : ℚ) / z.2)) ?_).trans card_image_le
  intro q hq
  obtain ⟨⟨v, w⟩, h, rfl⟩ := mem_image.mp hq
  obtain ⟨hmem, hlt⟩ := mem_filter.mp h
  obtain ⟨hv, hw⟩ := mem_product.mp hmem
  let g := v.gcd w
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (smooth_pos hv)
  have hvg : (v / g) * g = v := Nat.div_mul_cancel (Nat.gcd_dvd_left v w)
  have hwg : (w / g) * g = w := Nat.div_mul_cancel (Nat.gcd_dvd_right v w)
  have ha : 0 < v / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hvg
    exact (smooth_pos hv).ne' hvg.symm
  have hb : 0 < w / g := by
    by_contra! h0
    rw [Nat.eq_zero_of_le_zero h0, zero_mul] at hwg
    exact (smooth_pos hw).ne' hwg.symm
  refine mem_image.mpr ⟨(v / g,w / g), mem_filter.mpr ⟨mem_product.mpr
    ⟨smooth_of_dvd hv ha ⟨g,hvg.symm⟩, smooth_of_dvd hw hb ⟨g,hwg.symm⟩⟩, ?_⟩, ?_⟩
  · refine ⟨?_, Nat.coprime_div_gcd_div_gcd hg⟩
    exact Nat.lt_of_mul_lt_mul_right (show (w/g)*g < (v/g)*g by rwa [hvg,hwg])
  · apply (div_eq_div_iff (by exact_mod_cast hb.ne') (by exact_mod_cast (smooth_pos hw).ne')).mpr
    exact_mod_cast (show (v/g)*w = v*(w/g) from calc
      (v/g)*w = (v/g)*((w/g)*g) := by rw [hwg]
      _ = ((v/g)*g)*(w/g) := by ac_rfl
      _ = _ := by rw [hvg])

set_option maxRecDepth 40000 in
set_option maxHeartbeats 5000000 in
theorem ratios_100_card : (ratios (smooth 11 100)).card ≤ 513 := by
  apply (ratios_le_reduced 11 100).trans
  rw [← trialSmooth_eq]
  decide

end CubicSmoothCover

open Finset

namespace CubicPrimeCount

private theorem factorial_factorization_of_lt_sq {n p : ℕ} (hp : p.Prime)
    (hn : n < p ^ 2) : n.factorial.factorization p = n / p := by
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hn
  rw [Nat.factorization_factorial hp hlog, show Ico 1 2 = {1} by decide, sum_singleton, pow_one]

private def multinomial42 (m : ℕ) : ℕ :=
  (42*m).choose (21*m) * (21*m).choose (14*m) * (7*m).choose (6*m)

private theorem multinomial42_pos (m : ℕ) : 0 < multinomial42 m :=
  mul_pos (mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
    (Nat.choose_pos (by omega))

private theorem prime_dvd_multinomial42 {m p : ℕ} (hm : 40 ≤ m)
    (hp : p.Prime) (hmp : m < p) (hpm : p ≤ 42*m) : p ∣ multinomial42 m := by
  have h1 : (42*m).choose (21*m) * (21*m).factorial * (21*m).factorial =
      (42*m).factorial := by
    simpa only [show 42*m-21*m = 21*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 42*m) (k := 21*m) (by omega))
  have h2 : (21*m).choose (14*m) * (14*m).factorial * (7*m).factorial =
      (21*m).factorial := by
    simpa only [show 21*m-14*m = 7*m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 21*m) (k := 14*m) (by omega))
  have h3 : (7*m).choose (6*m) * (6*m).factorial * m.factorial = (7*m).factorial := by
    simpa only [show 7*m-6*m = m by omega] using
      (Nat.choose_mul_factorial_mul_factorial (n := 7*m) (k := 6*m) (by omega))
  have hM : multinomial42 m * (21*m).factorial * (14*m).factorial * (6*m).factorial *
      m.factorial = (42*m).factorial := calc
    _ = (42*m).choose (21*m) * (21*m).factorial *
        ((21*m).choose (14*m) * (14*m).factorial *
          ((7*m).choose (6*m) * (6*m).factorial * m.factorial)) := by
      unfold multinomial42
      ac_rfl
    _ = _ := by rw [h3, h2, h1]
  have hp2 : 42*m < p^2 := by
    have h := Nat.pow_le_pow_left (show m+1 ≤ p by omega) 2
    have h' : 40 * m ≤ m * m := Nat.mul_le_mul_right m hm
    nlinarith only [h, h']
  have hfac := congrArg (fun n : ℕ => n.factorization p) hM
  have hM0 := (multinomial42_pos m).ne'
  rw [Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial * (6*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (by positivity : multinomial42 m * (21*m).factorial *
      (14*m).factorial ≠ 0) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero hM0 (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    Nat.factorization_mul hM0 (Nat.factorial_ne_zero _)] at hfac
  simp only [Finsupp.add_apply] at hfac
  rw [factorial_factorization_of_lt_sq hp hp2,
    factorial_factorization_of_lt_sq hp (show 21*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 14*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show 6*m < p^2 by omega),
    factorial_factorization_of_lt_sq hp (show m < p^2 by omega), Nat.div_eq_of_lt hmp] at hfac
  have hd (j a : ℕ) (hj : (42*m)/j = a) : (42*m)/p/j = a/p := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p j, ← Nat.div_div_eq_div_mul, hj]
  rw [← hd 2 (21*m) (by omega), ← hd 3 (14*m) (by omega), ← hd 7 (6*m) (by omega)] at hfac
  have hLo : 1 ≤ (42*m)/p := (Nat.one_le_div_iff hp.pos).mpr hpm
  have hHi : (42*m)/p < 42 := (Nat.div_lt_iff_lt_mul hp.pos).mpr
    (Nat.mul_lt_mul_of_pos_left hmp (by decide))
  have hstrict : ∀ q : Fin 42, 0 < q.val → q.val/2 + q.val/3 + q.val/7 < q.val := by decide
  have hf : 0 < (multinomial42 m).factorization p := by
    have hi := hstrict ⟨(42*m)/p, hHi⟩ (by exact hLo)
    dsimp at hi
    omega
  exact Nat.dvd_of_mem_primeFactors (by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hf.ne' : p ∈ (multinomial42 m).primeFactors)

private theorem weighted_binomial (m a b : ℕ) (hb : b ≤ a) :
    (a*m).choose (b*m) * (b^b * (a-b)^(a-b))^m ≤ (a^a)^m := by
  have hm : b*m ≤ a*m := Nat.mul_le_mul_right m hb
  have hs := single_le_sum (s := range (a*m+1))
    (f := fun j => b^j * (a-b)^(a*m-j) * (a*m).choose j)
    (fun _ _ => Nat.zero_le _) (a := b*m) (mem_range.mpr (by omega))
  have hexpand : a^(a*m) = ∑ j ∈ range (a*m+1), b^j * (a-b)^(a*m-j) * (a*m).choose j := by
    simpa only [Nat.add_sub_of_le hb, Nat.cast_id] using (add_pow b (a-b) (a*m))
  rw [← hexpand] at hs
  rw [← Nat.sub_mul, pow_mul b b, pow_mul (a-b) (a-b), ← mul_pow, pow_mul a a] at hs
  simpa only [Nat.mul_comm] using hs

private theorem multinomial42_bound (m : ℕ) :
    multinomial42 m * ((21^42 * 14^14 * 7^7 * 6^6 : ℕ)^m) ≤
      ((42^42 * 21^21 * 7^7 : ℕ)^m) := by
  have h1 := weighted_binomial m 42 21 (by decide)
  have h2 := weighted_binomial m 21 14 (by decide)
  have h3 := weighted_binomial m 7 6 (by decide)
  simp only [show 42-21=21 by decide, show 21-14=7 by decide,
    show 7-6=1 by decide, one_pow, mul_one] at h1 h2 h3
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  rw [show (21^42 : ℕ) = 21^21 * 21^21 by rw [← pow_add]] 
  simp only [mul_pow] at h
  simp only [mul_pow, multinomial42]
  exact h.trans_eq' (by ring)

private theorem primorial_div (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) ∣ primorial m * multinomial42 m := by
  rw [show 42*m = m+(41*m) by omega, primorial_add]
  apply Nat.mul_dvd_mul_left
  refine prod_primes_dvd _ (fun _ h => (mem_filter.mp h).2.prime) ?_
  intro p hp
  obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂⟩ := mem_Ico.mp hpI
  exact prime_dvd_multinomial42 hm hpP (by omega) (by omega)

set_option maxRecDepth 10000 in
private theorem primorial42
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) (m : ℕ) (hm : 40 ≤ m) :
    primorial (42*m) * 100^(42*m) ≤ 304^(42*m) := by
  let den : ℕ := 21^42 * 14^14 * 7^7 * 6^6
  let num : ℕ := 42^42 * 21^21 * 7^7
  have hden : 0 < den := by dsimp [den]; positivity
  have h := Nat.le_of_dvd (mul_pos (primorial_pos _) (multinomial42_pos _))
    (primorial_div m hm)
  have hn : multinomial42 m * den^m ≤ num^m := multinomial42_bound m
  have hconst : 7*num*100^42 ≤ 2*den*304^42 := by norm_num [num, den]
  apply Nat.le_of_mul_le_mul_left _ (show 0 < (2*den)^m by positivity)
  calc
    (2*den)^m * (primorial (42*m) * 100^(42*m)) ≤
        (2*den)^m * ((primorial m * multinomial42 m) * 100^(42*m)) := by gcongr
    _ = (2^m * primorial m) * (multinomial42 m * den^m) * (100^42)^m := by
      rw [mul_pow, pow_mul 100 42]
      ring
    _ ≤ (7^m * num^m) * (100^42)^m :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (hseven m) hn)
    _ = (7*num*100^42)^m := by simp only [mul_pow]
    _ ≤ (2*den*304^42)^m := Nat.pow_le_pow_left hconst _
    _ = (2*den)^m * 304^(42*m) := by rw [mul_pow, pow_mul 304 42]

theorem theta_le
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) {x : ℝ} (hx : 1680 ≤ x) :
    Chebyshev.theta x ≤ (9/8 : ℝ) * (x + 41) := by
  let n := ⌊x⌋₊
  let m := (n+41)/42
  have hn : 1680 ≤ n := by
    dsimp [n]
    apply (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
    exact_mod_cast hx
  have hm : 40 ≤ m := by dsimp [m]; omega
  have hround : n ≤ 42*m := by dsimp [m]; omega
  have hround' : 42*m ≤ n+41 := by dsimp [m]; omega
  have hprim := primorial42 hseven m hm
  have hcast : (primorial (42*m) : ℝ) * (100:ℝ)^(42*m) ≤ (304:ℝ)^(42*m) := by
    exact_mod_cast hprim
  have hr : (primorial (42*m) : ℝ) ≤ (304/100:ℝ)^(42*m) := by
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr hcast
  have hlog : Real.log (304/100:ℝ) ≤ 9/8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact (by norm_num [Finset.sum_range_succ, Nat.factorial] : (304/100:ℝ) ≤
      ∑ i ∈ range 6, (9/8:ℝ)^i / (i.factorial : ℝ)).trans
      (Real.sum_le_exp_of_nonneg (by norm_num) 6)
  have hprimpos : 0 < (primorial (42*m) : ℝ) := by exact_mod_cast primorial_pos (42*m)
  have hpos : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hnle : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [Chebyshev.theta_eq_log_primorial]
  change Real.log (primorial n : ℝ) ≤ _
  calc
    _ ≤ Real.log (primorial (42*m) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast primorial_mono hround)
    _ ≤ Real.log ((304/100 : ℝ)^(42*m)) := Real.log_le_log hprimpos hr
    _ = (42*m : ℕ) * Real.log (304/100:ℝ) := Real.log_pow _ _
    _ ≤ (42*m : ℕ) * (9/8 : ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (9/8 : ℝ) * (x + 41) := by
      have h := (show (42*m : ℕ) ≤ n+41 from hround')
      have h' : ((42*m : ℕ) : ℝ) ≤ n+41 := by exact_mod_cast h
      linarith

end CubicPrimeCount

namespace CubicPrimeCount

open MeasureTheory

private theorem log2000_ge : (7:ℝ) ≤ Real.log 2000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 7 = Real.exp 1 ^ 7 := by
    convert Real.exp_nat_mul 1 7 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 7).trans (by norm_num)

theorem log250000_ge : (12:ℝ) ≤ Real.log 250000 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 12 = Real.exp 1 ^ 12 := by
    convert Real.exp_nat_mul 1 12 using 2; norm_num
  rw [h]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans
    (by norm_num : (2.7182818286:ℝ) ≤ 11/4)) 12).trans (by norm_num)

private theorem log250000_le : Real.log 250000 ≤ (13:ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 13 = Real.exp 1 ^ 13 := by
    convert Real.exp_nat_mul 1 13 using 2; norm_num
  rw [h]
  exact (by norm_num : (250000:ℝ) ≤ (8/3)^13).trans
    (pow_le_pow_left₀ (by norm_num) ((by norm_num : (8/3:ℝ) ≤ 2.7182818283).trans
      Real.exp_one_gt_d9.le) 13)

theorem log_div_le {x : ℝ} (hx : 250000 ≤ x) : Real.log x / x ≤ 13 / 250000 := by
  have h : 250000 ∈ Set.Ici (Real.exp 1) := by
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  exact (Real.log_div_self_antitoneOn h (h.trans hx) hx).trans
    (div_le_div_of_nonneg_right log250000_le (by norm_num))

private theorem integral_tail {x : ℝ} (hx : 2000 ≤ x) :
    (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) ≤ (7/5) * x / Real.log x ^ 2 := by
  let g (t : ℝ) := (7/5) * t / Real.log t ^ 2
  let d (t : ℝ) := (7/5) * ((Real.log t - 2) / Real.log t ^ 3)
  have hlog {t : ℝ} (ht : 2000 ≤ t) : 7 ≤ Real.log t :=
    log2000_ge.trans (Real.log_le_log (by norm_num) ht)
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc 2000 x) : HasDerivAt g (d t) t := by
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (hlog ht.1)
    have h := ((hasDerivAt_id t).const_mul (7/5:ℝ)).div
      ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl.ne')
    convert h using 1
    all_goals first | rfl | (dsimp [d, g]; field_simp [ht0.ne', hl.ne'])
  have hdc : ContinuousOn d (Set.uIcc 2000 x) := by
    dsimp [d]
    refine continuousOn_const.mul ((Real.continuousOn_log.mono ?_).sub continuousOn_const
      |>.div ((Real.continuousOn_log.mono ?_).pow _) ?_)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact fun h => by have he := Set.mem_singleton_iff.mp h; linarith [ht.1]
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num) (hlog ht.1)))
  have hInt : IntervalIntegrable d volume 2000 x := hdc.intervalIntegrable
  calc
    _ ≤ ∫ t in (2000:ℝ)..x, d t := by
      refine intervalIntegral.integral_mono_on hx
        (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith))
        hInt (fun t ht => ?_)
      have hl := hlog ht.1
      have hl0 : 0 < Real.log t := by linarith
      dsimp [d]
      rw [show Real.log t ^ 3 = Real.log t ^ 2 * Real.log t by ring, ← mul_div_assoc,
        le_div_iff₀ (mul_pos (pow_pos hl0 _) hl0)]
      field_simp [hl0.ne']
      linarith
    _ = g x - g 2000 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    _ ≤ _ := sub_le_self _ (by dsimp [g]; positivity)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1500000 in
private theorem prime_count_2000 : Nat.primeCounting 2000 ≤ 377 := by
  let R := (range 2001).filter ((510510:ℕ).Coprime ·)
  have hR : R.card ≤ 359 := by decide
  have hP : primorial 17 = 510510 := by decide
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hsub : (range 2001).filter Nat.Prime ⊆ range 18 ∪ R := by
    intro p hp
    obtain ⟨hpr, hprime⟩ := mem_filter.mp hp
    by_cases h : p < 18
    · exact mem_union_left _ (mem_range.mpr h)
    · have hcop : (primorial 17).Coprime p := by
        rw [Nat.coprime_comm, hprime.coprime_iff_not_dvd, hprime.dvd_primorial_iff]
        omega
      exact mem_union_right _ (mem_filter.mpr ⟨hpr, hP ▸ hcop⟩)
  exact (card_le_card hsub).trans ((card_union_le (range 18) R).trans (by simp only [card_range]; omega))

set_option maxHeartbeats 750000 in
theorem prime_count
    (hseven : ∀ n : ℕ, 2^n * primorial n ≤ 7^n) {k : ℕ} (hk : 250000 ≤ k) :
    (Nat.primeCounting k : ℝ) * Real.log (k : ℝ) ≤ (128/100:ℝ) * k := by
  let x : ℝ := k
  have hx : 250000 ≤ x := by dsimp [x]; exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hx2 : (2000:ℝ) ≤ x := by linarith
  have hlog : 12 ≤ Real.log x := log250000_ge.trans (Real.log_le_log (by norm_num) hx)
  have hl0 : 0 < Real.log x := by linarith
  let f (t : ℝ) := Chebyshev.theta t / (t * Real.log t ^ 2)
  have hi (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable f volume a b := by
    refine intervalIntegrable_iff.mpr ?_
    rw [Set.uIoc_of_le hab, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc_left ha)
  have hs := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := x) (by linarith)
  have hs' := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (2000:ℝ)) (by norm_num)
  have hn : ⌊x⌋₊ = k := Nat.floor_natCast k
  have hn' : ⌊(2000:ℝ)⌋₊ = 2000 := Nat.floor_natCast 2000
  rw [hn, ← intervalIntegral.integral_add_adjacent_intervals
    (hi _ _ (by norm_num) (by norm_num : (2:ℝ) ≤ 2000)) (hi _ _ (by norm_num) hx2)] at hs
  rw [hn'] at hs'
  change (Nat.primeCounting k : ℝ) = _ + ((∫ t in 2..2000, f t) + ∫ t in 2000..x, f t) at hs
  change (Nat.primeCounting 2000 : ℝ) = _ + ∫ t in 2..2000, f t at hs'
  have hfirst : (∫ t in (2:ℝ)..2000, f t) ≤ 377 := by
    have hθ : 0 ≤ Chebyshev.theta 2000 / Real.log 2000 :=
      div_nonneg (Chebyshev.theta_nonneg _) (by linarith [log2000_ge])
    have hc : (Nat.primeCounting 2000 : ℝ) ≤ 377 := by exact_mod_cast prime_count_2000
    linarith
  have hsecond : (∫ t in (2000:ℝ)..x, f t) ≤ (23/20)*(7/5)*x/Real.log x^2 := by
    have hbound (t : ℝ) (ht : t ∈ Set.Icc 2000 x) :
        f t ≤ (23/20:ℝ) * (1 / Real.log t ^ 2) := by
      have ht0 : 0 < t := by linarith [ht.1]
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have h := theta_le hseven (show 1680 ≤ t by linarith [ht.1])
      dsimp [f]
      rw [div_le_iff₀ (mul_pos ht0 (pow_pos hlogt 2))]
      field_simp [hlogt.ne']
      linarith [ht.1]
    calc
      _ ≤ ∫ t in (2000:ℝ)..x, (23/20:ℝ)*(1 / Real.log t ^ 2) :=
        intervalIntegral.integral_mono_on hx2 (hi _ _ (by norm_num) hx2)
          ((Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _)
          hbound
      _ = (23/20:ℝ) * (∫ t in (2000:ℝ)..x, 1 / Real.log t ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (integral_tail hx2) (show 0 ≤ (23/20:ℝ) by norm_num)
        simpa only [mul_div_assoc, mul_assoc] using h
  have hθ : Chebyshev.theta x ≤ (1126/1000:ℝ)*x := by
    have h := theta_le hseven (show 1680 ≤ x by linarith)
    linarith
  have hp : (Nat.primeCounting k : ℝ) ≤ 377 + (1126/1000)*x/Real.log x +
      (23/20)*(7/5)*x/Real.log x^2 := by
    linarith [div_le_div_of_nonneg_right hθ hl0.le]
  have hd := mul_le_mul_of_nonneg_right hp hl0.le
  have hr : Real.log x ≤ (13/250000)*x := (div_le_iff₀ hx0).mp (log_div_le hx)
  have ht : x / Real.log x ≤ x / 12 := div_le_div_of_nonneg_left hx0.le (by norm_num) hlog
  have he : (377 + (1126/1000)*x/Real.log x + (23/20)*(7/5)*x/Real.log x^2) *
      Real.log x = 377 * Real.log x + (1126/1000)*x + (23/20)*(7/5)*(x/Real.log x) := by
    field_simp [hl0.ne']
  rw [he] at hd
  change (Nat.primeCounting k : ℝ) * Real.log x ≤ (128/100:ℝ) * x
  linarith

end CubicPrimeCount

namespace ErdosSelfridge

private theorem scaled_prod_ge_of_card_below_shift (A : Finset ℕ) (D a b : ℕ) 
    (hA : ∀ j ∈ A, 0 < j)
    (hcount : ∀ x, a * (A.filter (· ≤ x)).card ≤ b * x + a*D) :
    a ^ (A.card - D) * (A.card - D).factorial ≤ b ^ (A.card - D) * A.prod id := by
  classical
  let e := A.orderEmbOfFin rfl
  have ranked (i : Fin A.card) : a * (i.val + 1) ≤ b * e i + a*D := by
    let f : Fin (i.val + 1) ↪ ℕ :=
      ⟨fun j => e ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩,
        fun j z h => Fin.ext (congrArg (fun z : Fin A.card => z.val) (e.injective h))⟩
    have hsub : Finset.univ.map f ⊆ A.filter (· ≤ e i) := by
      intro a ha
      obtain ⟨j, _, rfl⟩ := mem_map.mp ha
      apply mem_filter.mpr
      exact ⟨A.orderEmbOfFin_mem rfl _, e.monotone (by
        change j.val ≤ i.val
        omega)⟩
    have h := card_le_card hsub
    simp only [card_map, card_univ, Fintype.card_fin] at h
    exact (Nat.mul_le_mul_left _ h).trans (hcount _)
  let m := A.card - D
  let g : Fin m ↪ ℕ :=
    ⟨fun j => e ⟨D + j.val, by have := j.isLt; dsimp [m] at this; omega⟩,
      fun j z h => Fin.ext (by
        have h' := congrArg Fin.val (e.injective h)
        change D + j.val = D + z.val at h'
        omega)⟩
  have hmono (i : Fin m) : a * (i.val + 1) ≤ b * g i := by
    have h := ranked ⟨D + i.val, by have := i.isLt; dsimp [m] at this; omega⟩
    change a * (D + i.val + 1) ≤ b * g i + a*D at h
    rw [show a * (D + i.val + 1) = a * D + a * (i.val + 1) by ring] at h
    omega
  have hA' : Finset.univ.map g ⊆ A := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := mem_map.mp ha
    exact A.orderEmbOfFin_mem rfl _
  have hmul : (∏ i : Fin m, a * (i.val + 1)) = a ^ m * m.factorial := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), prod_range_add_one_eq_factorial]
  change a ^ m * m.factorial ≤ b ^ m * A.prod id
  rw [← hmul]
  calc
    (∏ i : Fin m, a * (i.val + 1)) ≤ ∏ i : Fin m, b * g i :=
      prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hmono i)
    _ = b ^ m * (Finset.univ.map g).prod id := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_map]
      rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (prod_le_prod_of_subset_of_one_le' hA' (fun _ hj _ => hA _ hj))


private theorem factor_cover_ratios {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hn : k ^ l < n)
    (S U V : Finset ℕ) (hSI : S ⊆ Icc (n + 1) (n + k))
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hcover : ∀ j ∈ S, ∃ u ∈ U, ∃ v ∈ V, u * v = powerFreePart l j) :
    S.card ≤ U.card + (CubicSmoothCover.ratios V).card := by
  have h0 (j : ℕ) (hj : j ∈ S) : j ≠ 0 := by have := (mem_Icc.mp (hSI hj)).1; omega
  rw [← card_image_of_injOn (powerFreePart_injOn_interval hk (by omega) hn S hSI)]
  apply CubicSmoothCover.pair_count_ratios (S.image (powerFreePart l)) U V hU hV
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    exact hcover j hj
  intro a ha b hb c hc d hd hprod
  obtain ⟨w, hw, rfl⟩ := mem_image.mp ha
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hd
  have hp (p : ℕ) : (w * x).factorization p % l = (y * z).factorization p % l := by
    rw [← powerFreePart_mul_residue (h0 w hw) (h0 x hx),
      ← powerFreePart_mul_residue (h0 y hy) (h0 z hz), hprod]
  have he := interval_products_residue_injective (r := 2) hk hn (by decide) (by omega)
    (w ::ₘ x ::ₘ 0) (y ::ₘ z ::ₘ 0) (by simp) (by simp)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hw
        · exact hSI hx)
    (by intro j hj; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hj
        rcases hj with rfl | rfl
        · exact hSI hy
        · exact hSI hz)
    (by simpa using hp)
  simpa using congrArg (Multiset.map (powerFreePart l)) he

private theorem powerFreePart_cubic_prod_lower {n k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hn : k ^ l < n) (S : Finset ℕ) (hS : S ⊆ Icc (n + 1) (n + k)) :
    10000^(S.card-520) * (S.card-520).factorial ≤
      2281^(S.card-520) * ∏ j ∈ S, powerFreePart l j := by
  let f := powerFreePart l
  have hi : Set.InjOn f S := powerFreePart_injOn_interval hk (by omega) hn S hS
  let A := S.image f
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    have hjpos := (mem_Icc.mp (hS hj)).1
    exact Nat.pos_of_ne_zero (powerFreePart_nonzero (by omega))
  have hcount (x : ℕ) : 10000 * (A.filter (· ≤ x)).card ≤ 2281*x + 10000*520 := by
    let T := S.filter (fun j => f j ≤ x)
    have he : A.filter (· ≤ x) = T.image f := by
      ext a
      simp only [A, T, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨j, hj, rfl⟩, hx⟩
        exact ⟨j, ⟨hj, hx⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hx⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, hx⟩
    rw [he, card_image_of_injOn (hi.mono (filter_subset _ _))]
    let U := CubicSmoothCover.remaining 11 CubicSmoothCover.cutoff100 x
    let V := CubicSmoothCover.smooth 11 100
    have hcover : T.card ≤ U.card + (CubicSmoothCover.ratios V).card :=
      factor_cover_ratios hk hl hn T U V ((filter_subset _ _).trans hS)
        (fun _ => CubicSmoothCover.remaining_pos) (fun _ => CubicSmoothCover.smooth_pos)
        (fun j hj => CubicSmoothCover.factor100
          (hA (f j) (mem_image.mpr ⟨j, (mem_filter.mp hj).1, rfl⟩)) (mem_filter.mp hj).2)
    have hU : 10000 * U.card ≤ 2281*x + 62000 := CubicSmoothCover.remaining_100_card x
    have hV : (CubicSmoothCover.ratios V).card ≤ 513 := CubicSmoothCover.ratios_100_card
    change 10000 * T.card ≤ 2281 * x + 10000 * 520
    omega
  have h := scaled_prod_ge_of_card_below_shift A 520 10000 2281 hA hcount
  simpa only [A, card_image_of_injOn hi, prod_image hi, id_eq] using h

private theorem log_ratio_lower : (147/100:ℝ) ≤ Real.log (10000/2281) := by
  have h := Real.le_log_one_add_of_nonneg (x := (219/2281 : ℝ)) (by norm_num)
  rw [show (10000/2281:ℝ) = 2^2*(1 + 219/2281) by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num at h ⊢
  linarith [Real.log_two_gt_d9]

private theorem explicit_factorial_ratio {k : ℕ} (hk : 250000 ≤ k) :
    let m := k - (Nat.primeCounting k + 520)
    2281^m * k.factorial < 10000^m * m.factorial := by
  let b := Nat.primeCounting k + 520
  let m := k - b
  change 2281^m * k.factorial < 10000^m * m.factorial
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : (250000 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := CubicPrimeCount.log250000_ge.trans (Real.log_le_log (by norm_num) hkR)
  have hp := CubicPrimeCount.prime_count primorial_le_seven_halves_pow hk
  have hp' : (Nat.primeCounting k : ℝ) ≤ (128/1200:ℝ)*k := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Nat.primeCounting k))
    linarith
  have hd : (520:ℝ) ≤ (520/250000:ℝ)*k := by linarith
  have hb : (b : ℝ) ≤ (128/1200 + 520/250000:ℝ)*k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hb_le : b ≤ k := by
    have hbR : (b : ℝ) ≤ k := by linarith
    exact_mod_cast hbR
  have hmR : (m : ℝ) = (k : ℝ) - b := Nat.cast_sub hb_le
  have hlogUpper := (div_le_iff₀ hk0).mp (CubicPrimeCount.log_div_le hkR)
  have hleft : (b : ℝ)*Real.log k ≤
      (128/100 + 520*13/250000:ℝ) * k := by
    simp only [b, Nat.cast_add, Nat.cast_ofNat, add_mul]
    linarith
  have hright : (147/100:ℝ)*((1-(128/1200+520/250000))*k) ≤
      (m:ℝ)*Real.log (10000/2281) := by
    have hmLower : ((1-(128/1200+520/250000):ℝ)*k) ≤ (m:ℝ) := by linarith
    refine (mul_le_mul_of_nonneg_left hmLower (by norm_num)).trans ?_
    rw [mul_comm (147/100:ℝ) (m:ℝ)]
    exact mul_le_mul_of_nonneg_left log_ratio_lower (Nat.cast_nonneg m)
  have hlogcmp : (b : ℝ) * Real.log k < (m : ℝ) * Real.log (10000/2281) := by
    linarith
  have hR : (k : ℝ)^b < (10000/2281:ℝ)^m := by
    apply (Real.log_lt_log_iff (pow_pos hk0 _) (pow_pos (by norm_num) _)).1
    simpa only [Real.log_pow] using hlogcmp
  rw [div_pow, lt_div_iff₀ (by positivity)] at hR
  have hpower : k^b * 2281^m < 10000^m := by exact_mod_cast hR
  have hfac : k.factorial ≤ m.factorial * k^b := by
    have h := Nat.ascFactorial_le_pow_add m b
    have he : m+b = k := Nat.sub_add_cancel hb_le
    rw [he] at h
    have he' := Nat.factorial_mul_ascFactorial m b
    rw [he] at he'
    exact he'.symm.le.trans (Nat.mul_le_mul_left _ h)
  calc
    _ ≤ 2281^m * (m.factorial*k^b) := Nat.mul_le_mul_left _ hfac
    _ = m.factorial * (k^b * 2281^m) := by ring
    _ < m.factorial * 10000^m := Nat.mul_lt_mul_of_pos_left hpower (Nat.factorial_pos _)
    _ = _ := mul_comm _ _

/-- A prime exponent obstruction for every width at least 250,000. -/
theorem large_prime_exponent_obstruction_explicit {n k l : ℕ} (hk : 250000 ≤ k)
    (hl : 3 ≤ l) (hn : k ^ l < n) :
    ∃ p, k ≤ p ∧ p.Prime ∧
      ¬ (l ∣ Nat.factorization (∏ m ∈ Icc (n + 1) (n + k), m) p) := by
  by_contra! hbad
  obtain ⟨S, hS, hsize, hdvd, _⟩ := reduce_to_small_prime_parts n k l (by omega) hbad
  have hcount : ((range k).filter Nat.Prime).card ≤ Nat.primeCounting k := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.monotone_primeCounting' (Nat.le_succ _)
  have hlow := powerFreePart_cubic_prod_lower (by omega) hl hn S hS
  have hd : (∏ j ∈ S, powerFreePart l j) ≤ k.factorial :=
    (Nat.le_of_dvd (Nat.factorial_pos _) hdvd).trans (Nat.factorial_le (Nat.sub_le _ _))
  let m := k - (Nat.primeCounting k + 520)
  let s := S.card - 520
  have hm : m ≤ s := by dsimp [m, s]; omega
  have hfac := explicit_factorial_ratio hk
  change 2281^m * k.factorial < 10000^m * m.factorial at hfac
  have hfac' : 2281^s * k.factorial < 10000^s * s.factorial := calc
    _ = 2281^(s-m) * (2281^m * k.factorial) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    _ < 2281^(s-m) * (10000^m * m.factorial) :=
      Nat.mul_lt_mul_of_pos_left hfac (by positivity)
    _ ≤ 10000^(s-m) * (10000^m * s.factorial) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.mul_le_mul_left _ (Nat.factorial_le hm))
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  exact (not_lt_of_ge (hlow.trans (Nat.mul_le_mul_left _ hd))) hfac'

end ErdosSelfridge

/-- Erdős and Selfridge's large-prime valuation theorem for consecutive products. -/
private theorem valuation_for_closed_interval (k l n : ℕ) (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ m ∈ Icc (n + 1) (n + k), m).factorization p := by
  by_cases heven : 2 ∣ l
  · exact ErdosSelfridge.consecutive_strong_of_even_exponent hk heven hend
  by_cases hsmall : k ≤ 1000
  · exact ErdosSelfridge.consecutive_strong_through_thousand hk hsmall hl hend
  have hlodd : l = 3 ∨ 5 ≤ l := by omega
  by_cases hmiddle : k < 250000
  · exact ErdosSelfridge.consecutive_strong_of_sparse_sieve_cover
      ErdosSelfridge.sparseSieveCover_to_250001 k l n (by omega) (by omega) hk hlodd hend
  by_cases hshort : n ≤ k
  · exact ErdosSelfridge.short_interval k l n hk hl hend hshort
  by_contra! hdiv
  obtain ⟨i, hi, p, hpk, hp, hd⟩ := SylvesterSchur.exists_large_prime
    (show k < n + 1 by omega) (show 0 < k by omega)
  have hi' := mem_range.mp hi
  have hm : n + 1 + i ∈ Icc (n + 1) (n + k) := mem_Icc.mpr ⟨by omega, by omega⟩
  have hgt := ErdosSelfridge.modulus_growth_of_large_prime (by omega) hl hpk hp hm hd
    (hdiv p hpk.le hp)
  obtain ⟨q, hqk, hq, hqnd⟩ := ErdosSelfridge.large_prime_exponent_obstruction_explicit
    (show 250000 ≤ k by omega) (show 3 ≤ l by omega) hgt
  exact hqnd (hdiv q hqk hq)

/-- If the endpoint reaches a prime at least k, one large prime has
multiplicity indivisible by the proposed exponent. -/
private theorem valuation_for_block (k n l : ℕ) (hk : 3 ≤ k) (hl : 2 ≤ l)
    (hprime : ∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime) :
    ∃ p, k ≤ p ∧ p.Prime ∧ ¬ l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p := by
  obtain ⟨q, hkq, hqend, hq⟩ := hprime
  have hend : ErdosSelfridge.firstPrimeAtLeast k ≤ n + k :=
    (Nat.find_min' (Nat.exists_infinite_primes k) ⟨hkq, hq⟩).trans hqend
  have hinterval : Icc (n + 1) (n + k) = Ioc n (n + k) := by
    ext m
    simp only [mem_Icc, mem_Ioc]
    omega
  simpa only [hinterval] using valuation_for_closed_interval k l n hk hl hend

private theorem two_consecutive_factors :
    ∀ (n x l : ℕ), 2 ≤ l → (∏ m ∈ Ioc n (n + 2), m) ≠ x ^ l := by
  intro n x l hl hp
  have hi : Ioc n (n + 2) = {n + 1, n + 2} := by
    ext i
    simp only [mem_Ioc, mem_insert, mem_singleton]
    omega
  have hmem : n + 1 ∉ ({n + 2} : Finset ℕ) := by
    simp only [mem_singleton]
    omega
  rw [hi, prod_insert hmem, prod_singleton] at hp
  have hc : Nat.Coprime (n + 1) (n + 2) := by
    change Nat.Coprime (n + 1) ((n + 1) + 1)
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  have hunit {a b : ℕ} (hab : a.Coprime b) : IsUnit (gcd a b) := by
    rw [gcd_eq_nat_gcd, hab.gcd_eq_one]
    exact isUnit_one
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (hunit hc) hp
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (hunit hc.symm) ((mul_comm _ _).trans hp)
  have hl0 : l ≠ 0 := by omega
  have ha0 : 0 < a := by
    by_contra! h
    rw [show a = 0 by omega, zero_pow hl0] at ha
    omega
  have hab : a < b := by
    by_contra! h
    have := Nat.pow_le_pow_left h l
    omega
  have hterm : 2 ≤ l * a ^ (l - 1) := by
    calc
      2 ≤ l := hl
      _ = l * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ ha0)
  have hgap : a ^ l + 2 ≤ (a + 1) ^ l := by
    calc
      a ^ l + 2 ≤ a ^ l + l * a ^ (l - 1) := Nat.add_le_add_left hterm _
      _ ≤ _ := by simpa only [Nat.cast_id, mul_one] using
        (pow_add_mul_le_add_pow (b := (1 : ℕ)) (Nat.zero_le a) (Nat.zero_le _) l)
  have hle := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) l
  omega

private theorem prime_of_multiplicity_one :
    ∀ (k n : ℕ), 3 ≤ k → (¬ ∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime) →
    ∃ p : ℕ, p.Prime ∧ (∏ m ∈ Ioc n (n + k), m).factorization p = 1 := by
  intro k n hk hNoLargePrime
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.bertrand ((n + k) / 2) (by omega)
  have hpN : p ≤ n + k := by omega
  have hpk : p < k := lt_of_not_ge fun h => hNoLargePrime ⟨p, h, hpN, hp⟩
  have hnp : n < p := by omega
  have hUnique (m : ℕ) (hm : m ∈ Ioc n (n + k)) (hmp : m ≠ p) : ¬ p ∣ m := by
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
    rintro ⟨t, rfl⟩
    have ht : 2 ≤ t := by
      by_contra! h
      interval_cases t <;> simp_all
    have ht' := Nat.mul_le_mul_left p ht
    omega
  refine ⟨p, hp, ?_⟩
  calc
    _ = ∑ m ∈ Ioc n (n + k), m.factorization p :=
      Nat.factorization_prod_apply fun m hm => by
        have h := (Finset.mem_Ioc.mp hm).1
        omega
    _ = p.factorization p := Finset.sum_eq_single_of_mem p (Finset.mem_Ioc.mpr ⟨hnp, hpN⟩)
      fun m hm hne => Nat.factorization_eq_zero_of_not_dvd (hUnique m hm hne)
    _ = 1 := by simp [hp.factorization]

/-- No block of two or more consecutive positive integers has a perfect-power product. -/
theorem OMA.consecutive_product_not_power : type_of% @Erdos137.erdos_137.variants.perfect_power := by
  intro k hk n x l hl
  by_cases htwo : k = 2
  · subst k
    exact two_consecutive_factors n x l hl
  have hk' : 3 ≤ k := by omega
  intro hpower
  have hdiv (p : ℕ) : l ∣ (∏ m ∈ Ioc n (n + k), m).factorization p := by
    rw [hpower, Nat.factorization_pow]
    exact ⟨x.factorization p, rfl⟩
  by_cases hprime : ∃ q : ℕ, k ≤ q ∧ q ≤ n + k ∧ q.Prime
  · obtain ⟨p, _, _, hbad⟩ := valuation_for_block k n l hk' hl hprime
    exact hbad (hdiv p)
  · obtain ⟨p, _, hp⟩ := prime_of_multiplicity_one k n hk' hprime
    have h := hdiv p
    rw [hp] at h
    have := Nat.le_of_dvd (by decide : 0 < 1) h
    omega

theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1_H3_R1.H2 := by
  intro k n l hk hkn _ hl
  obtain ⟨q, hq, hkq, hqk⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
  exact valuation_for_block k n l hk (by omega) ⟨q, hkq.le, by omega, hq⟩
