import FormalConjectures.OEIS.«60841»

-- Problem: Numerator of $1/\det(M)$ for $M[i,j] = 1/\operatorname{lcm}(i,j)$
-- Upstream: formal-conjectures FormalConjectures/OEIS/60841.lean:76 (declaration OeisA60841.conjecture1)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof outline.
-- (1) Smith determinant: lcmMatrix n = D * (L * diag(phi) * L^T) * D with D = diag(1/i) and
--     L the 0/1 divisibility matrix (unit lower triangular), so
--     1/det = (n!)^2 / P n with P n = prod_{k<=n} phi(k).
-- (2) So the denominator is 1 iff P n divides (n!)^2.
-- (3) n < 110: kernel computation.
-- (4) n >= 65: 2-adic valuations. For k >= 1,
--       sum_{q in S, q | k} w(q) + v2(k) <= v2(phi(k)) + [2 | k]
--     for a set S of 12 odd primes q with 2^w(q) | q - 1. Summing over k <= n gives
--       sum_{q in S} w(q) * (n / q) + v2(n!) <= v2(P n) + n / 2,
--     and sum_{q in S} w(q) * (n / q) > n + n / 2 >= v2(n!) + n / 2 for n >= 110,
--     hence v2(P n) > 2 * v2(n!).

namespace OMA

open Finset

/-- Product of the totients of 1..n. -/
def P : ℕ → ℕ
  | 0 => 1
  | n + 1 => P n * (n + 1).totient

theorem P_ne_zero (n : ℕ) : P n ≠ 0 := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    simp only [P]
    exact Nat.mul_ne_zero ih (Nat.totient_pos.mpr (Nat.succ_pos n)).ne'

/-- The odd primes used in the 2-adic count. -/
def S : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41}

/-- A power of two dividing q - 1 for q in S. -/
def w (q : ℕ) : ℕ :=
  if q = 5 ∨ q = 13 ∨ q = 29 ∨ q = 37 then 2 else if q = 17 then 4 else if q = 41 then 3 else 1

theorem S_spec : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ 2 ^ (w q) ∣ q - 1 := by
  decide

theorem two_not_mem_S : 2 ∉ S := by decide

theorem key (k : ℕ) : k ≠ 0 →
    (∑ q ∈ S, if q ∣ k then w q else 0) + padicValNat 2 k ≤
      padicValNat 2 k.totient + (if 2 ∣ k then 1 else 0) := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ k
  · intro p e hp he _
    have hsum : (∑ q ∈ S, if q ∣ p ^ e then w q else 0) = if p ∈ S then w p else 0 := by
      rw [← Finset.sum_ite_eq' S p w]
      refine Finset.sum_congr rfl ?_
      intro q hq
      have hqp := (S_spec q hq).1
      have : q ∣ p ^ e ↔ q = p := by
        constructor
        · intro h
          exact (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h)
        · intro h
          rw [h]
          exact dvd_pow_self p he.ne'
      simp only [this]
    rw [hsum, Nat.totient_prime_pow hp he]
    by_cases h2 : p = 2
    · subst h2
      rw [if_neg two_not_mem_S, if_pos (dvd_pow_self 2 he.ne')]
      have h1 : padicValNat 2 (2 ^ e) = e := padicValNat.prime_pow e
      have h3 : padicValNat 2 (2 ^ (e - 1) * (2 - 1)) = e - 1 := by
        simp
      omega
    · have hnd : ¬ 2 ∣ p ^ e := by
        intro h
        exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (Nat.prime_two.dvd_of_dvd_pow h)).symm
      rw [if_neg hnd, padicValNat.eq_zero_of_not_dvd hnd]
      have hpos : p ^ (e - 1) * (p - 1) ≠ 0 :=
        Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.sub_ne_zero_of_lt hp.one_lt)
      by_cases hmem : p ∈ S
      · rw [if_pos hmem]
        have hdvd : 2 ^ (w p) ∣ p ^ (e - 1) * (p - 1) :=
          Dvd.dvd.mul_left (S_spec p hmem).2.2 _
        have := (padicValNat_dvd_iff_le hpos).mp hdvd
        omega
      · rw [if_neg hmem]
        omega
  · intro h
    exact absurd rfl h
  · intro _
    have hsum : (∑ q ∈ S, if q ∣ 1 then w q else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro q hq
      have hqp := (S_spec q hq).1
      rw [if_neg]
      intro h
      exact hqp.one_lt.ne' (Nat.dvd_one.mp h)
    rw [hsum]
    simp
  · intro a b ha hb hab iha ihb _
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have iha' := iha ha0
    have ihb' := ihb hb0
    have hsum : (∑ q ∈ S, if q ∣ a * b then w q else 0) ≤
        (∑ q ∈ S, if q ∣ a then w q else 0) + (∑ q ∈ S, if q ∣ b then w q else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro q hq
      have hqp := (S_spec q hq).1
      by_cases h : q ∣ a * b
      · rw [if_pos h]
        rcases (Nat.Prime.dvd_mul hqp).mp h with h1 | h1
        · rw [if_pos h1]
          exact Nat.le_add_right _ _
        · rw [if_pos h1]
          exact Nat.le_add_left _ _
      · rw [if_neg h]
        exact Nat.zero_le _
    have hv : padicValNat 2 (a * b) = padicValNat 2 a + padicValNat 2 b :=
      padicValNat.mul ha0 hb0
    have hta : a.totient ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
    have htb : b.totient ≠ 0 := (Nat.totient_pos.mpr (by omega)).ne'
    have hvt : padicValNat 2 (a * b).totient = padicValNat 2 a.totient + padicValNat 2 b.totient := by
      rw [Nat.totient_mul hab]
      exact padicValNat.mul hta htb
    have hpar : (if 2 ∣ a then 1 else 0) + (if 2 ∣ b then 1 else 0) ≤
        (if 2 ∣ a * b then 1 else 0) := by
      by_cases h1 : 2 ∣ a
      · by_cases h2 : 2 ∣ b
        · exfalso
          have h3 := Nat.dvd_gcd h1 h2
          rw [Nat.Coprime.gcd_eq_one hab] at h3
          omega
        · rw [if_pos h1, if_neg h2, if_pos (Dvd.dvd.mul_right h1 b)]
      · by_cases h2 : 2 ∣ b
        · rw [if_neg h1, if_pos h2, if_pos (Dvd.dvd.mul_left h2 a)]
        · rw [if_neg h1, if_neg h2]
          exact Nat.zero_le _
    omega

theorem total (n : ℕ) :
    (∑ q ∈ S, w q * (n / q)) + padicValNat 2 n.factorial ≤ padicValNat 2 (P n) + n / 2 := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    have hk := key (n + 1) (Nat.succ_ne_zero n)
    have hsum : (∑ q ∈ S, w q * ((n + 1) / q)) =
        (∑ q ∈ S, w q * (n / q)) + (∑ q ∈ S, if q ∣ n + 1 then w q else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro q _
      rw [Nat.succ_div]
      by_cases h : q ∣ n + 1
      · rw [if_pos h, if_pos h, Nat.mul_add, Nat.mul_one]
      · rw [if_neg h, if_neg h, Nat.add_zero, Nat.add_zero]
    have hf : padicValNat 2 (n + 1).factorial = padicValNat 2 (n + 1) + padicValNat 2 n.factorial := by
      rw [Nat.factorial_succ]
      exact padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)
    have hP : padicValNat 2 (P (n + 1)) = padicValNat 2 (P n) + padicValNat 2 (n + 1).totient := by
      simp only [P]
      exact padicValNat.mul (P_ne_zero n) (Nat.totient_pos.mpr (Nat.succ_pos n)).ne'
    have h2 : (n + 1) / 2 = n / 2 + if 2 ∣ n + 1 then 1 else 0 := Nat.succ_div
    rw [hsum, hf, hP, h2]
    omega

theorem val_factorial_le (n : ℕ) : padicValNat 2 n.factorial ≤ n := by
  have h := @sub_one_mul_padicValNat_factorial 2 _ n
  simp only [Nat.add_one_sub_one, Nat.one_mul] at h
  omega

theorem sum_explicit (n : ℕ) : (∑ q ∈ S, w q * (n / q)) =
    n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19 + n / 23
      + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) := by
  simp [S, w, Finset.sum_insert]
  ring

theorem lin (n : ℕ) (hn : 110 ≤ n) : n + n / 2 <
    n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19 + n / 23
      + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) := by
  have h2 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have h3 : n + 1 ≤ 3 * (n / 3) + 3 := by omega
  have h5 : n + 1 ≤ 5 * (n / 5) + 5 := by omega
  have h7 : n + 1 ≤ 7 * (n / 7) + 7 := by omega
  have h11 : n + 1 ≤ 11 * (n / 11) + 11 := by omega
  have h13 : n + 1 ≤ 13 * (n / 13) + 13 := by omega
  have h17 : n + 1 ≤ 17 * (n / 17) + 17 := by omega
  have h19 : n + 1 ≤ 19 * (n / 19) + 19 := by omega
  have h23 : n + 1 ≤ 23 * (n / 23) + 23 := by omega
  have h29 : n + 1 ≤ 29 * (n / 29) + 29 := by omega
  have h31 : n + 1 ≤ 31 * (n / 31) + 31 := by omega
  have h37 : n + 1 ≤ 37 * (n / 37) + 37 := by omega
  have h41 : n + 1 ≤ 41 * (n / 41) + 41 := by omega
  linarith

theorem large (n : ℕ) (hn : 110 ≤ n) : ¬ P n ∣ n.factorial ^ 2 := by
  intro h
  have hne : n.factorial ^ 2 ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero n)
  have h1 : 2 ^ padicValNat 2 (P n) ∣ n.factorial ^ 2 := dvd_trans pow_padicValNat_dvd h
  have h2 := (padicValNat_dvd_iff_le hne).mp h1
  rw [padicValNat.pow] at h2
  have h3 := total n
  have h4 := val_factorial_le n
  have h5 := lin n hn
  rw [sum_explicit] at h3
  generalize n / 3 + 2 * (n / 5) + n / 7 + n / 11 + 2 * (n / 13) + 4 * (n / 17) + n / 19 + n / 23
      + 2 * (n / 29) + n / 31 + 2 * (n / 37) + 3 * (n / 41) = X at h3 h5
  generalize n / 2 = Y at h3 h5
  omega

set_option maxRecDepth 100000 in
theorem small : ∀ n < 110, 1 ≤ n → (P n ∣ n.factorial ^ 2 ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38)) := by
  decide +kernel

theorem dvd_iff (n : ℕ) (hn : 1 ≤ n) : P n ∣ n.factorial ^ 2 ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by
  by_cases h : n < 110
  · exact small n h hn
  · constructor
    · intro h1
      exact absurd h1 (large n (by omega))
    · intro h1
      omega

/-! Smith determinant -/

theorem gcd_sum (n i j : ℕ) (hi : i < n) :
    (∑ d ∈ range n, if (d + 1) ∣ (i + 1) ∧ (d + 1) ∣ (j + 1) then (d + 1).totient else 0) =
      Nat.gcd (i + 1) (j + 1) := by
  rw [← Finset.sum_filter]
  conv_rhs => rw [← Nat.sum_totient (Nat.gcd (i + 1) (j + 1))]
  have hg : 0 < Nat.gcd (i + 1) (j + 1) := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos i)
  refine Finset.sum_nbij' (fun d => d + 1) (fun d => d - 1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Nat.mem_divisors]
    exact ⟨Nat.dvd_gcd hd.2.1 hd.2.2, hg.ne'⟩
  · intro e he
    rw [Nat.mem_divisors] at he
    have he1 : 0 < e := Nat.pos_of_dvd_of_pos he.1 hg
    have he2 : e ≤ i + 1 :=
      Nat.le_of_dvd (Nat.succ_pos i) (dvd_trans he.1 (Nat.gcd_dvd_left _ _))
    have he3 : e - 1 + 1 = e := by omega
    rw [Finset.mem_filter, Finset.mem_range, he3]
    exact ⟨by omega, dvd_trans he.1 (Nat.gcd_dvd_left _ _), dvd_trans he.1 (Nat.gcd_dvd_right _ _)⟩
  · intro d _
    simp
  · intro e he
    rw [Nat.mem_divisors] at he
    have he1 : 0 < e := Nat.pos_of_dvd_of_pos he.1 hg
    show e - 1 + 1 = e
    omega
  · intro d _
    rfl

/-- The 0/1 divisibility matrix. -/
def L (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i d : Fin n => if (d.val + 1) ∣ (i.val + 1) then 1 else 0

theorem det_L (n : ℕ) : (L n).det = 1 := by
  have h : (L n).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have hlt : i.val < j.val := hij'
    simp only [L, Matrix.of_apply]
    rw [if_neg]
    intro hd
    have := Nat.le_of_dvd (Nat.succ_pos _) hd
    omega
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [L]

theorem lcm_factor (n : ℕ) : OeisA60841.lcmMatrix n =
    Matrix.diagonal (fun i : Fin n => (1 : ℚ) / ((i.val : ℚ) + 1)) *
      (L n * Matrix.diagonal (fun d : Fin n => (((d.val + 1).totient : ℕ) : ℚ)) * (L n).transpose) *
      Matrix.diagonal (fun i : Fin n => (1 : ℚ) / ((i.val : ℚ) + 1)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
  have hs : (∑ d : Fin n, (L n * Matrix.diagonal (fun d : Fin n => (((d.val + 1).totient : ℕ) : ℚ))) i d *
      (L n).transpose d j) = ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) := by
    rw [← gcd_sum n i.val j.val i.isLt, Nat.cast_sum,
      ← Fin.sum_univ_eq_sum_range (fun d => (((if (d + 1) ∣ (i.val + 1) ∧ (d + 1) ∣ (j.val + 1)
        then (d + 1).totient else 0 : ℕ)) : ℚ)) n]
    refine Finset.sum_congr rfl ?_
    intro d _
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    simp only [L, Matrix.of_apply]
    by_cases h1 : (d.val + 1) ∣ (i.val + 1)
    · by_cases h2 : (d.val + 1) ∣ (j.val + 1)
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  rw [hs]
  simp only [OeisA60841.lcmMatrix, Matrix.of_apply]
  have hgl := Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  have hg : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos _)).ne'
  have hl : ((Nat.lcm (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _)).ne'
  have hi : ((i.val : ℚ) + 1) ≠ 0 := by positivity
  have hj : ((j.val : ℚ) + 1) ≠ 0 := by positivity
  have hq : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) * ((Nat.lcm (i.val + 1) (j.val + 1) : ℕ) : ℚ)
      = ((i.val : ℚ) + 1) * ((j.val : ℚ) + 1) := by
    exact_mod_cast hgl
  field_simp
  linarith [hq]

theorem prod_fact (n : ℕ) : (∏ i : Fin n, ((i.val : ℚ) + 1)) = (n.factorial : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((i : ℚ) + 1)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

theorem prod_tot (n : ℕ) : (∏ d : Fin n, (((d.val + 1).totient : ℕ) : ℚ)) = (P n : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun d => (((d + 1).totient : ℕ) : ℚ)) n]
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [P]
    push_cast
    ring

theorem det_inv (n : ℕ) :
    ((OeisA60841.lcmMatrix n).det)⁻¹ = ((n.factorial ^ 2 : ℕ) : ℚ) / (P n : ℚ) := by
  rw [lcm_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_L, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [one_div, Finset.prod_inv_distrib]
  rw [prod_fact, prod_tot]
  have h1 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (P n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (P_ne_zero n)
  push_cast
  field_simp

theorem den_iff (a b : ℕ) (hb : b ≠ 0) : ((a : ℚ) / (b : ℚ)).den = 1 ↔ b ∣ a := by
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  constructor
  · intro h
    have h1 : (((a : ℚ) / (b : ℚ)).num : ℚ) = (a : ℚ) / (b : ℚ) := Rat.coe_int_num_of_den_eq_one h
    have h2 : (a : ℚ) = ((((a : ℚ) / (b : ℚ)).num * (b : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [h1]
      field_simp
    have h3 : (a : ℤ) = ((a : ℚ) / (b : ℚ)).num * (b : ℤ) := by exact_mod_cast h2
    have h4 : (b : ℤ) ∣ (a : ℤ) := Dvd.intro_left _ h3.symm
    exact Int.natCast_dvd_natCast.mp h4
  · rintro ⟨c, rfl⟩
    have : ((b * c : ℕ) : ℚ) / (b : ℚ) = ((c : ℕ) : ℚ) := by
      push_cast
      field_simp
    rw [this]
    exact Rat.den_natCast c

end OMA

theorem OMA.solution : type_of% @OeisA60841.conjecture1 := by
  intro n hn
  rw [OMA.det_inv, OMA.den_iff _ _ (OMA.P_ne_zero n), OMA.dvd_iff n hn]
  simp only [OeisA60841.integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  omega
