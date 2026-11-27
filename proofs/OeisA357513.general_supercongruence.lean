import FormalConjectures.OEIS.«357513»
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity

/-!
Adapted for the Left to Solve target and its pinned mathlib version.
Original proof by Claude Fable 5.2 (mathematics) and Claude Opus 5.5 (Lean),
under Felix Pernegger’s direction, from felixpernegger/oeis-a357513-supercongruence, commit
15ac7d538051d0d06d5f74e159b14a0242860ff3, distributed under the Apache License, Version 2.0.
Submitted by @rleshner.

# Proof of the supercongruence $u_m(p-1) \equiv 0 \pmod{p^4}$ for $p \ge 2m + 6$

Write $T_k = \binom{p-1}{k} \binom{p-1+k}{k}$ and $H(s) = \sum_{k=1}^{p-1} k^{-s}$, with $k^{-1}$
read modulo $p^4$. The proof has four steps.

1. `choose_mul_choose_sq`: $T_k^2 \equiv p^2/k^2 - 2p^3/k^3 \pmod{p^4}$, from the identity
   $k!^2 T_k = p (p - k) \prod_{j=1}^{k-1} (p^2 - j^2)$.
2. `p_cube_mul_sum_inv_pow`: $H(t) \equiv 0 \pmod{p}$ for $0 < t < p - 1$, from the power sums
   of the finite field $\mathbb{F}_p$.
3. `p_sq_mul_sum_inv_pow_odd`: $H(s) \equiv 0 \pmod{p^2}$ for odd $s$ with $s + 1 < p - 1$, by
   pairing $k$ with $p - k$.
4. `sum_choose_sq_mul_inv_pow` and `p_pow_four_dvd_num`: the sum is
   $p^2 H(2m+3) - 2p^3 H(2m+4) \equiv 0 \pmod{p^4}$. Clearing the denominator
   $((p-1)!)^{2m+1}$, which is prime to $p$, shows that $p^4$ divides the numerator.
-/

namespace OeisA357513

open Nat Finset

/-- With $p = n + 1$ and $k = i + 1$:
$k!^2 \binom{p-1}{k} \binom{p-1+k}{k} = p (p - k) \prod_{j=1}^{k-1} (p^2 - j^2)$. -/
private lemma factorial_sq_mul_choose_mul_choose (n i : ℕ) (hi : i + 1 ≤ n) :
    (((i + 1)! : ℕ) : ℤ) ^ 2 * ((n.choose (i + 1) : ℤ) * ((n + (i + 1)).choose (i + 1) : ℤ)) =
      ((n : ℤ) + 1) * ((n : ℤ) - i) *
        ∏ j ∈ range i, (((n : ℤ) + 1) ^ 2 - ((j : ℤ) + 1) ^ 2) := by
  induction i with
  | zero => simp; ring
  | succ i ih =>
    have ih := ih (by omega)
    have h1 := Nat.choose_succ_right_eq n (i + 1)
    zify [show i + 1 ≤ n by omega] at h1
    have h2 := Nat.add_one_mul_choose_eq (n + (i + 1)) (i + 1)
    zify at h2
    rw [show n + (i + 1 + 1) = n + (i + 1) + 1 by ring, Nat.factorial_succ, prod_range_succ]
    push_cast at ih h1 h2 ⊢
    linear_combination
      ((((i + 1)! : ℕ) : ℤ)) ^ 2 * (((n + (i + 1) + 1).choose (i + 1 + 1) : ℕ) : ℤ) *
          ((i : ℤ) + 1 + 1) * h1 -
        ((((i + 1)! : ℕ) : ℤ)) ^ 2 * ((n.choose (i + 1) : ℕ) : ℤ) * ((n : ℤ) - (i + 1)) * h2 +
        ((n : ℤ) - i - 1) * ((n : ℤ) + i + 2) * ih

/-- $\prod_{j \in s} (c - g_j) \equiv \prod_{j \in s} (-g_j) \pmod{c}$. -/
private lemma prod_sub_eq {R ι : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι) (c : R)
    (g : ι → R) : ∃ r, ∏ j ∈ s, (c - g j) = ∏ j ∈ s, (-g j) + c * r := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨∏ j ∈ s, (-g j) + c * r - g a * r, ?_⟩
    rw [prod_insert ha, prod_insert ha, hr]
    ring

/-- $(a + b)^{s+1} \equiv a^{s+1} + (s + 1) a^s b \pmod{b^2}$. -/
private lemma add_pow_eq {R : Type*} [CommRing R] (a b : R) (s : ℕ) :
    ∃ r, (a + b) ^ (s + 1) = a ^ (s + 1) + (s + 1) * a ^ s * b + b ^ 2 * r := by
  induction s with
  | zero => exact ⟨0, by ring⟩
  | succ s ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨(s + 1) * a ^ s + r * (a + b), ?_⟩
    rw [pow_succ, hr]
    push_cast
    ring

variable {p : ℕ}

/-- A natural number coprime to $p$ is invertible modulo $p^4$. -/
private lemma natCast_mul_inv {x : ℕ} (hx : x.Coprime p) :
    (x : ZMod (p ^ 4)) * (x : ZMod (p ^ 4))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one x (hx.pow_right 4)

/-- $p^4 = 0$ in `ZMod (p ^ 4)`. -/
private lemma p_pow_four : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- Every $k$ with $1 \le k < p$ is coprime to the prime $p$. -/
private lemma coprime_of_pos_of_lt (hp : p.Prime) {k : ℕ} (hk0 : 1 ≤ k) (hk : k < p) :
    k.Coprime p :=
  (Nat.coprime_of_lt_prime (by omega) hk hp).symm

/-- For $1 \le k \le p - 1$:
$\left(\binom{p-1}{k} \binom{p-1+k}{k}\right)^2 \equiv p^2/k^2 - 2p^3/k^3 \pmod{p^4}$. -/
private lemma choose_mul_choose_sq (hp : p.Prime) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ p - 1) :
    (((p - 1).choose k : ZMod (p ^ 4)) * ((p - 1 + k).choose k)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 2 -
        2 * (p : ZMod (p ^ 4)) ^ 3 * ((k : ZMod (p ^ 4))⁻¹) ^ 3 := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hid := congrArg (Int.cast : ℤ → ZMod (p ^ 4))
    (factorial_sq_mul_choose_mul_choose (p - 1) i (by omega))
  push_cast [Nat.cast_sub hp.one_le] at hid
  simp only [sub_add_cancel] at hid
  obtain ⟨r, hr⟩ :=
    prod_sub_eq (range i) ((p : ZMod (p ^ 4)) ^ 2) (fun j => ((j : ZMod (p ^ 4)) + 1) ^ 2)
  rw [hr] at hid
  set P0 := ∏ j ∈ range i, (-((j : ZMod (p ^ 4)) + 1) ^ 2)
  have hP0 : P0 ^ 2 = ((i ! : ℕ) : ZMod (p ^ 4)) ^ 4 := by
    rw [← prod_range_add_one_eq_factorial]
    push_cast
    rw [← prod_pow, ← prod_pow]
    exact prod_congr rfl fun j _ => by ring
  have hk := natCast_mul_inv (coprime_of_pos_of_lt hp (k := i + 1) (by omega) (by omega))
  have hg := natCast_mul_inv (p := p)
    ((Nat.Prime.coprime_iff_not_dvd hp).2
      (by rw [Nat.Prime.dvd_factorial (n := i) hp]; omega)).symm
  set ι := ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹
  set g' := ((i ! : ℕ) : ZMod (p ^ 4))⁻¹
  set g := ((i ! : ℕ) : ZMod (p ^ 4))
  set T := ((p - 1).choose (i + 1) : ZMod (p ^ 4)) * ((p - 1 + (i + 1)).choose (i + 1))
  have p4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := p_pow_four
  rw [Nat.factorial_succ] at hid
  push_cast at hid hk
  have e1 : (((i : ZMod (p ^ 4)) + 1) * g) ^ 4 * T ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 * ((p : ZMod (p ^ 4)) - ((i : ZMod (p ^ 4)) + 1)) ^ 2 * g ^ 4 := by
    linear_combination
      ((((i : ZMod (p ^ 4)) + 1) * g) ^ 2 * T +
          (p : ZMod (p ^ 4)) * ((p : ZMod (p ^ 4)) - 1 - i) * (P0 + (p : ZMod (p ^ 4)) ^ 2 * r)) *
        hid +
      ((p : ZMod (p ^ 4)) - 1 - i) ^ 2 * (2 * P0 * r + (p : ZMod (p ^ 4)) ^ 2 * r ^ 2) * p4 +
      (p : ZMod (p ^ 4)) ^ 2 * ((p : ZMod (p ^ 4)) - 1 - i) ^ 2 * hP0
  have hU : (ι * g') ^ 4 * (((i : ZMod (p ^ 4)) + 1) * g) ^ 4 = 1 := by
    rw [show (ι * g') ^ 4 * (((i : ZMod (p ^ 4)) + 1) * g) ^ 4 =
      ((((i : ZMod (p ^ 4)) + 1) * ι) * (g * g')) ^ 4 by ring, hk, hg]
    simp
  have hV : (g * g') ^ 4 = 1 := by rw [hg, one_pow]
  have e2 : T ^ 2 = (p : ZMod (p ^ 4)) ^ 2 *
      ((p : ZMod (p ^ 4)) - ((i : ZMod (p ^ 4)) + 1)) ^ 2 * ι ^ 4 := by
    linear_combination (-T ^ 2) * hU + (ι * g') ^ 4 * e1 +
      (p : ZMod (p ^ 4)) ^ 2 * ((p : ZMod (p ^ 4)) - ((i : ZMod (p ^ 4)) + 1)) ^ 2 * ι ^ 4 * hV
  rw [e2]
  linear_combination
    (-(p : ZMod (p ^ 4)) ^ 2 * ι ^ 2 *
      (2 * p * ι - ((i : ZMod (p ^ 4)) + 1) * ι - 1)) * hk + ι ^ 4 * p4

/-- $\sum_{k=1}^{p-1} k^{-t} = 0$ in $\mathbb{F}_p$ for $0 < t < p - 1$. -/
private lemma sum_inv_pow_zmod_eq_zero (hp : p.Prime) (t : ℕ) (ht0 : 0 < t) (ht : t < p - 1) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ t = 0 := by
  have := Fact.mk hp
  have h0 : ((0 : ZMod p)⁻¹) ^ t = 0 := by simp [ht0.ne']
  have hb : ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ t =
      ∑ x ∈ univ.erase (0 : ZMod p), x⁻¹ ^ t := by
    refine Finset.sum_nbij' (fun k => (k : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_Icc] at hk
      simp only [mem_erase, mem_univ, and_true, ne_eq]
      rw [ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · intro x hx
      simp only [mem_erase, mem_univ, and_true, ne_eq] at hx
      simp only [mem_Icc]
      have := ZMod.val_lt x
      have : x.val ≠ 0 := (ZMod.val_ne_zero x).2 hx
      omega
    · intro k hk
      simp only [mem_Icc] at hk
      exact ZMod.val_cast_of_lt (by omega)
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro k _
      rfl
  rw [hb, sum_erase (f := fun x : ZMod p => x⁻¹ ^ t) univ h0]
  exact (Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ t)).trans
    (FiniteField.sum_pow_lt_card_sub_one (ZMod p) t (by rw [ZMod.card]; omega))

/-- $p^3 \sum_{k=1}^{p-1} k^{-t} \equiv 0 \pmod{p^4}$ for $0 < t < p - 1$. -/
private lemma p_cube_mul_sum_inv_pow (hp : p.Prime) (t : ℕ) (ht0 : 0 < t) (ht : t < p - 1) :
    (p : ZMod (p ^ 4)) ^ 3 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ t = 0 := by
  have : NeZero (p ^ 4) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have := Fact.mk hp
  set x := ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ t
  let g : ZMod (p ^ 4) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by norm_num)) (ZMod p)
  have hg : g x = 0 := by
    simp only [x, map_sum, map_pow]
    rw [← sum_inv_pow_zmod_eq_zero hp t ht0 ht]
    refine sum_congr rfl fun k hk => ?_
    simp only [mem_Icc] at hk
    have h2 := congrArg g (natCast_mul_inv (coprime_of_pos_of_lt hp (k := k) hk.1 (by omega)))
    rw [map_mul, map_one, map_natCast] at h2
    have h3 := inv_eq_of_mul_eq_one_right h2
    exact (congrArg (· ^ t) h3).symm
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hg
  obtain ⟨y, hy⟩ := hg
  rw [← ZMod.natCast_zmod_val x, hy]
  push_cast
  rw [← mul_assoc, ← pow_succ, p_pow_four, zero_mul]

/-- $p^2 \sum_{k=1}^{p-1} k^{-s} \equiv 0 \pmod{p^4}$ for odd $s$ with $s + 1 < p - 1$. -/
private lemma p_sq_mul_sum_inv_pow_odd (hp : p.Prime) (hp2 : p ≠ 2) (s : ℕ) (hs : Odd s)
    (ht : s + 1 < p - 1) :
    (p : ZMod (p ^ 4)) ^ 2 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ s = 0 := by
  set H := ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ s
  have hrefl : H = ∑ k ∈ Icc 1 (p - 1), (((p - k : ℕ) : ZMod (p ^ 4))⁻¹) ^ s := by
    refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_ <;>
      intro k hk <;> simp only [mem_Icc] at hk ⊢
    · omega
    · omega
    · omega
    · omega
    · rw [show p - (p - k) = k by omega]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by obtain ⟨j, hj⟩ := hs; omega⟩
  have hs' : Even s' := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, by omega⟩
  have p4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := p_pow_four
  have hterm : ∀ k ∈ Icc 1 (p - 1), (p : ZMod (p ^ 4)) ^ 2 *
      (((k : ZMod (p ^ 4))⁻¹) ^ (s' + 1) + (((p - k : ℕ) : ZMod (p ^ 4))⁻¹) ^ (s' + 1)) =
      -(s' + 1) * ((p : ZMod (p ^ 4)) ^ 3 * ((k : ZMod (p ^ 4))⁻¹) ^ (s' + 1 + 1)) := by
    intro k hk
    simp only [mem_Icc] at hk
    have hk1 := natCast_mul_inv (coprime_of_pos_of_lt hp (k := k) hk.1 (by omega))
    have hk2 := natCast_mul_inv (coprime_of_pos_of_lt hp (k := p - k) (by omega) (by omega))
    set ι := (k : ZMod (p ^ 4))⁻¹
    set ι' := ((p - k : ℕ) : ZMod (p ^ 4))⁻¹
    push_cast [Nat.cast_sub (show k ≤ p by omega)] at hk2
    have hι' : ι' = -ι + p * (ι * ι') := by
      linear_combination (-ι') * hk1 + (-ι) * hk2
    obtain ⟨r, hr⟩ := add_pow_eq (-ι) (p * (ι * ι')) s'
    rw [← hι', Odd.neg_pow (by exact Even.add_one hs'), Even.neg_pow hs'] at hr
    linear_combination (p : ZMod (p ^ 4)) ^ 2 * hr +
      (s' + 1) * (p : ZMod (p ^ 4)) ^ 3 * ι ^ (s' + 1) * hι' +
      ((s' + 1) * ι ^ (s' + 2) * ι' + ι ^ 2 * ι' ^ 2 * r) * p4
  have h2H : 2 * ((p : ZMod (p ^ 4)) ^ 2 * H) = -(s' + 1) * ((p : ZMod (p ^ 4)) ^ 3 *
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ (s' + 1 + 1)) := by
    calc 2 * ((p : ZMod (p ^ 4)) ^ 2 * H) = (p : ZMod (p ^ 4)) ^ 2 * (H + H) := by ring
      _ = ∑ k ∈ Icc 1 (p - 1), (p : ZMod (p ^ 4)) ^ 2 *
          (((k : ZMod (p ^ 4))⁻¹) ^ (s' + 1) + (((p - k : ℕ) : ZMod (p ^ 4))⁻¹) ^ (s' + 1)) := by
        rw [← mul_sum, sum_add_distrib, ← hrefl]
      _ = _ := by rw [sum_congr rfl hterm, mul_sum, mul_sum]
  rw [p_cube_mul_sum_inv_pow hp (s' + 1 + 1) (by omega) ht, mul_zero] at h2H
  have h2 := natCast_mul_inv (p := p) ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  push_cast at h2
  linear_combination (-((p : ZMod (p ^ 4)) ^ 2 * H)) * h2 + (2 : ZMod (p ^ 4))⁻¹ * h2H

/-- The sum defining $u_m(p-1)$, read in `ZMod (p ^ 4)`, vanishes when $p \ge 2m + 6$. -/
private lemma sum_choose_sq_mul_inv_pow (m : ℕ) (hp : p.Prime) (hpm : 2 * m + 6 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), (((p - 1).choose k : ZMod (p ^ 4)) * ((p - 1 + k).choose k)) ^ 2 *
      ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) = 0 := by
  rw [sum_congr rfl fun k hk => by rw [choose_mul_choose_sq hp k (mem_Icc.1 hk).1 (mem_Icc.1 hk).2]]
  have h1 := p_cube_mul_sum_inv_pow hp (2 * m + 4) (by omega) (by omega)
  have h2 := p_sq_mul_sum_inv_pow_odd hp (by omega) (2 * m + 3) ⟨m + 1, by ring⟩ (by omega)
  calc _ = (p : ZMod (p ^ 4)) ^ 2 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 3) -
        2 * ((p : ZMod (p ^ 4)) ^ 3 *
          ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 4)) := by
        rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h1, h2]; ring

/-- $p^4$ divides the numerator of the sum defining $u_m(p-1)$ when $p \ge 2m + 6$. -/
private lemma p_pow_four_dvd_num (m : ℕ) (hp : p.Prime) (hpm : 2 * m + 6 ≤ p) :
    p ^ 4 ∣ (∑ k ∈ Icc 1 (p - 1), (((p - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ) ^ 2) /
      k ^ (2 * m + 1)).num.natAbs := by
  set S : ℚ := ∑ k ∈ Icc 1 (p - 1),
    (((p - 1).choose k : ℚ) ^ 2 * ((p - 1 + k).choose k : ℚ) ^ 2) / k ^ (2 * m + 1)
  set L : ℕ := (p - 1)! ^ (2 * m + 1)
  have hdvd : ∀ k ∈ Icc 1 (p - 1), k ^ (2 * m + 1) ∣ L := fun k hk =>
    pow_dvd_pow_of_dvd (Nat.dvd_factorial (mem_Icc.1 hk).1 (mem_Icc.1 hk).2) _
  set M : ℕ := ∑ k ∈ Icc 1 (p - 1),
    (p - 1).choose k ^ 2 * (p - 1 + k).choose k ^ 2 * (L / k ^ (2 * m + 1))
  have hSM : S * L = M := by
    simp only [S, M, sum_mul, Nat.cast_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℚ) ≠ 0 := by
      have := (mem_Icc.1 hk).1
      positivity
    rw [Nat.cast_mul, Nat.cast_div (hdvd k hk) (by push_cast; exact pow_ne_zero _ hk0)]
    push_cast
    field_simp
  have hM : p ^ 4 ∣ M := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (M : ZMod (p ^ 4)) = (L : ZMod (p ^ 4)) *
        ∑ k ∈ Icc 1 (p - 1), (((p - 1).choose k : ZMod (p ^ 4)) * ((p - 1 + k).choose k)) ^ 2 *
          ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) := by
      simp only [M, Nat.cast_sum, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hkι := natCast_mul_inv (coprime_of_pos_of_lt hp (k := k) (mem_Icc.1 hk).1
        (by have := (mem_Icc.1 hk).2; omega))
      obtain ⟨c, hc⟩ := hdvd k hk
      have hk0 : 0 < k := (mem_Icc.1 hk).1
      have hkιe :
          (k : ZMod (p ^ 4)) ^ (2 * m + 1) * ((k : ZMod (p ^ 4))⁻¹) ^ (2 * m + 1) = 1 := by
        rw [← mul_pow, hkι, one_pow]
      rw [hc, Nat.mul_div_cancel_left _ (by positivity)]
      push_cast
      linear_combination
        (-((p - 1).choose k : ZMod (p ^ 4)) ^ 2 * ((p - 1 + k).choose k : ZMod (p ^ 4)) ^ 2 *
          (c : ZMod (p ^ 4))) * hkιe
    rw [this, sum_choose_sq_mul_inv_pow m hp hpm, mul_zero]
  have hnum : S.num.natAbs * L = M * S.den := by
    have h : (S.num : ℚ) * L = (M : ℚ) * S.den := by
      rw [← Rat.mul_den_eq_num, ← hSM]
      ring
    have h' : S.num * (L : ℤ) = (M : ℤ) * (S.den : ℤ) := by exact_mod_cast h
    have := congrArg Int.natAbs h'
    simpa [Int.natAbs_mul] using this
  have hcop : (p ^ 4).Coprime L :=
    Nat.Coprime.pow 4 _
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by rw [Nat.Prime.dvd_factorial hp]; omega))
  exact hcop.dvd_of_dvd_mul_right (hnum ▸ dvd_mul_of_dvd_left hM _)

/-- $u_m(p-1) \equiv 0 \pmod{p^4}$ for every prime $p \ge 2m + 6$. -/
theorem supercongruence (m : ℕ) (hp : p.Prime) (hpm : 2 * m + 6 ≤ p) :
    (u m (p - 1) : ZMod (p ^ 4)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact p_pow_four_dvd_num m hp hpm

end OeisA357513

theorem OMA.solution : type_of% @OeisA357513.general_supercongruence := by
  intro m
  refine ⟨Finset.range (2 * m + 6), ?_⟩
  intro p hp hpe
  exact OeisA357513.supercongruence m hp (by simpa using hpe)

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
