import FormalConjectures.OEIS.«212334»
import Mathlib

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Tanner Clary.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Ported to Left to Solve by @rleshner from commit
a44dee67cab478f440f3162e0a4bedce73b1b918 of tanclary/oeis-a212334-palomar.
The adaptation reuses the upstream sequence and retains the prime-power proof.

Author of the proof: Tanner Clary. The definition `a` and the statements of `conjecture_1`
and `conjecture_2` are copied verbatim from `FormalConjectures/OEIS/212334.lean`
(The Formal Conjectures Authors).
-/

/-!
# Prime-power lifting for OEIS A212334

This adapts Tanner Clary's binomial-sum argument to the pinned mathlib version.
The summands are grouped according to their index modulo powers of the prime.
-/

namespace OMA.PrimePowerLift

open Finset OeisA212334

private def termZ (n k : ℕ) : ℤ :=
  (n.choose k : ℤ) * ((n - 1).choose k : ℤ) * ((n + k - 1).choose k : ℤ) ^ 2

private lemma choose_succ_succ_mul (m k : ℕ) :
    (m + 1).choose (k + 1) * (k + 1) = m.choose k * (m + 1) := by
  rcases lt_or_ge m k with hlt | hle
  · simp [Nat.choose_eq_zero_of_lt (by omega : m + 1 < k + 1), Nat.choose_eq_zero_of_lt hlt]
  · rw [Nat.choose_succ_succ, add_mul, Nat.choose_succ_right_eq, ← mul_add]
    congr 1; omega

private lemma factorial_pow_four_mul_termZ {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((k.factorial : ℤ) ^ 4) * termZ n k =
      (n : ℤ) ^ 3 * ((n : ℤ) - (k : ℤ)) *
        ∏ j ∈ Finset.Ico 1 k, ((n : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
    · simp only [zero_add, Nat.factorial_one, Finset.Ico_self, Finset.prod_empty,
        mul_one, termZ, Nat.choose_one_right, Nat.add_sub_cancel]
      rw [Int.ofNat_sub hkn]; ring
    · have hk_le : k ≤ n := Nat.le_of_succ_le hkn
      have ih_val := ih hk_pos hk_le
      have hc1 : ((n.choose (k + 1) : ℤ)) * (k + 1 : ℤ) = (n.choose k : ℤ) * ((n : ℤ) - (k : ℤ)) := by
        have hZ : ((n.choose (k + 1) * (k + 1) : ℕ) : ℤ) = ((n.choose k * (n - k) : ℕ) : ℤ) :=
          congrArg Nat.cast (Nat.choose_succ_right_eq n k)
        push_cast at hZ; rw [Int.ofNat_sub hk_le] at hZ; exact hZ
      have hc2 : (((n - 1).choose (k + 1) : ℤ)) * (k + 1 : ℤ) =
          ((n - 1).choose k : ℤ) * ((n : ℤ) - 1 - (k : ℤ)) := by
        have hZ : ((((n - 1).choose (k + 1) * (k + 1)) : ℕ) : ℤ) =
            ((((n - 1).choose k * (n - 1 - k)) : ℕ) : ℤ) :=
          congrArg Nat.cast (Nat.choose_succ_right_eq (n - 1) k)
        push_cast at hZ
        rw [Int.ofNat_sub (by omega : k ≤ n - 1), Int.ofNat_sub (by omega : 1 ≤ n)] at hZ
        exact hZ
      have hc3 : (((n + k).choose (k + 1) : ℤ)) * (k + 1 : ℤ) =
          ((n + k - 1).choose k : ℤ) * ((n : ℤ) + (k : ℤ)) := by
        have hnk1 : n + k = (n + k - 1) + 1 := by omega
        have h : (n + k).choose (k + 1) * (k + 1) = (n + k - 1).choose k * (n + k) := by
          conv_lhs => rw [hnk1]
          rw [choose_succ_succ_mul (n + k - 1) k, ← hnk1]
        exact_mod_cast h
      have hfac : (((k + 1).factorial : ℤ) ^ 4) * termZ n (k + 1) =
          (((k + 1 : ℤ) ^ 4 * termZ n (k + 1))) * ((k.factorial : ℤ) ^ 4) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hstep : ((k + 1 : ℤ) ^ 4) * termZ n (k + 1) =
          termZ n k * ((n : ℤ) - (k : ℤ)) * ((n : ℤ) - 1 - (k : ℤ)) * ((n : ℤ) + (k : ℤ)) ^ 2 := by
        unfold termZ
        rw [show n + (k + 1) - 1 = n + k by omega]
        calc ((k + 1 : ℤ) ^ 4) * ((n.choose (k + 1) : ℤ) * ((n - 1).choose (k + 1) : ℤ) *
                ((n + k).choose (k + 1) : ℤ) ^ 2)
            = ((n.choose (k + 1) : ℤ) * (k + 1 : ℤ)) *
                (((n - 1).choose (k + 1) : ℤ) * (k + 1 : ℤ)) *
                (((n + k).choose (k + 1) : ℤ) * (k + 1 : ℤ)) ^ 2 := by ring
          _ = ((n.choose k : ℤ) * ((n : ℤ) - (k : ℤ))) *
                (((n - 1).choose k : ℤ) * ((n : ℤ) - 1 - (k : ℤ))) *
                (((n + k - 1).choose k : ℤ) * ((n : ℤ) + (k : ℤ))) ^ 2 := by rw [hc1, hc2, hc3]
          _ = _ := by ring
      rw [hfac, hstep, Finset.prod_Ico_succ_top hk_pos]
      calc termZ n k * ((n : ℤ) - (k : ℤ)) * ((n : ℤ) - 1 - (k : ℤ)) *
              ((n : ℤ) + (k : ℤ)) ^ 2 * ((k.factorial : ℤ) ^ 4)
          = (((k.factorial : ℤ) ^ 4) * termZ n k) *
              (((n : ℤ) - (k : ℤ)) * ((n : ℤ) - 1 - (k : ℤ)) * ((n : ℤ) + (k : ℤ)) ^ 2) := by ring
        _ = ((n : ℤ) ^ 3 * ((n : ℤ) - (k : ℤ)) *
              ∏ j ∈ Finset.Ico 1 k, ((n : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2) *
              (((n : ℤ) - (k : ℤ)) * ((n : ℤ) - 1 - (k : ℤ)) * ((n : ℤ) + (k : ℤ)) ^ 2) := by
            rw [ih_val]
        _ = (n : ℤ) ^ 3 * ((n : ℤ) - ((k + 1 : ℕ) : ℤ)) *
              ((∏ j ∈ Finset.Ico 1 k, ((n : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2) *
                ((n : ℤ) ^ 2 - (k : ℤ) ^ 2) ^ 2) := by
            push_cast; ring

private lemma sum_inv_pow_zmod_eq_zero {p m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hm : 1 ≤ m)
    (hnotdvd : ¬ (p ∣ 2 ^ m - 1)) :
    ∑ u ∈ Finset.Ico 1 p, ((u : ZMod p)⁻¹) ^ m = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h_eq_univ : ∑ u ∈ Finset.Ico 1 p, ((u : ZMod p)⁻¹) ^ m =
      ∑ x : ZMod p, (x⁻¹) ^ m := by
    have hbij : ∑ u ∈ Finset.range p, ((u : ZMod p)⁻¹) ^ m = ∑ x : ZMod p, (x⁻¹) ^ m := by
      refine Finset.sum_bij (fun u _ => (u : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_
        (fun _ _ => rfl)
      · intro a ha b hb hab
        rw [Finset.mem_range] at ha hb
        have h1 := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
      · intro x _
        exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    rw [← hbij]
    have hsplit : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext u; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp [Nat.ne_of_gt hm]
  rw [h_eq_univ]
  set S : ZMod p := ∑ x : ZMod p, (x⁻¹) ^ m
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
    omega
  have hscale : S = ((2 : ZMod p)⁻¹ ^ m) * S := by
    have hreindex : ∑ x : ZMod p, (((2 : ZMod p) * x)⁻¹) ^ m = S := by
      dsimp [S]
      exact Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2ne)
        (fun x => (((2 : ZMod p) * x)⁻¹) ^ m) (fun y => (y⁻¹) ^ m) (fun _ => rfl)
    conv_lhs => rw [← hreindex]
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_inv_rev, mul_pow, mul_comm]
  have hmul : ((2 : ZMod p) ^ m - 1) * S = 0 := by
    have h1 : (2 : ZMod p) ^ m * S = S := by
      conv_lhs => rw [hscale]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h2ne, one_pow, one_mul]
    linear_combination h1
  have hcoeff_ne : ((2 : ZMod p) ^ m - 1) ≠ 0 := by
    intro h0
    apply hnotdvd
    have h1pow : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    have hcast : (((2 ^ m - 1 : ℕ) : ZMod p)) = 0 := by
      rw [Nat.cast_sub h1pow]
      simpa using h0
    exact (ZMod.natCast_eq_zero_iff (2 ^ m - 1) p).mp hcast
  exact (mul_eq_zero.mp hmul).resolve_left hcoeff_ne

private lemma prod_Ico_div_nondiv {M : Type*} [CommMonoid M] {p K : ℕ} (hp : 0 < p) (hK : 1 ≤ K)
    (f : ℕ → M) :
    ∏ j ∈ Finset.Ico 1 K, f j =
      (∏ i ∈ Finset.Ico 1 ((K - 1) / p + 1), f (p * i)) *
        (∏ j ∈ (Finset.Ico 1 K).filter (fun j => ¬ (p ∣ j)), f j) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 K) (fun j => p ∣ j) f]
  congr 1
  symm
  refine Finset.prod_bij (fun i _ => p * i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hi_le : i ≤ (K - 1) / p := by omega
    have hpi_le : p * i ≤ K - 1 := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp).mp hi_le
    exact ⟨⟨Nat.mul_pos hp (by omega), by omega⟩, dvd_mul_right p i⟩
  · intro i₁ _ i₂ _ h
    exact Nat.mul_left_cancel hp h
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hj1, hjK⟩, i, rfl⟩ := hj
    have hi_pos : 0 < i := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp at hj1
      · exact hpos
    have hi_le : i ≤ (K - 1) / p := by
      rw [Nat.le_div_iff_mul_le hp, mul_comm]
      omega
    exact ⟨i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, rfl⟩

private lemma factorial_sub_one_pow_four {K : ℕ} (hK : 1 ≤ K) :
    (((K - 1).factorial : ℤ) ^ 4) = ∏ j ∈ Finset.Ico 1 K, (j : ℤ) ^ 4 := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases eq_or_lt_of_le (Nat.zero_le K) with rfl | hK_pos
    · simp
    · rw [Finset.prod_Ico_succ_top hK_pos, ← ih hK_pos]
      rw [show K + 1 - 1 = K by omega]
      rcases K with _ | K'
      · omega
      · simp only [Nat.factorial_succ, Nat.add_sub_cancel]
        push_cast; ring

private lemma factorial_split_pos {t : ℕ} (ht : 1 ≤ t) :
    (t.factorial : ℤ) = (t : ℤ) * (((t - 1).factorial : ℤ)) := by
  rcases t with _ | t'
  · omega
  · simp [Nat.factorial_succ]

private def U1Nat (p K : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Ico 1 K).filter (fun j => ¬ (p ∣ j)), j ^ 4

private def V1 (p N K : ℕ) : ℤ :=
  ∏ j ∈ (Finset.Ico 1 K).filter (fun j => ¬ (p ∣ j)), ((N : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2

private lemma coprime_U1Nat {p K : ℕ} (hp : p.Prime) : (U1Nat p K).Coprime p := by
  unfold U1Nat
  refine Nat.Coprime.prod_left fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_left 4

private lemma pm_sub_one_div_p {p m : ℕ} (hp : 0 < p) (hm : 1 ≤ m) :
    (p * m - 1) / p + 1 = m := by
  have heq : p * m - 1 = (p - 1) + p * (m - 1) := by
    have h1 : p * m = p + p * (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm]
      ring
    omega
  rw [heq, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega : p - 1 < p)]
  omega

private lemma U1_mul_termZ_mul_p {p n m : ℕ} (hp : 0 < p) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (U1Nat p (p * m) : ℤ) * termZ (p * n) (p * m) =
      termZ n m * V1 p (p * n) (p * m) := by
  have hpm1 : 1 ≤ p * m := Nat.mul_pos hp hm1
  have hpm_le : p * m ≤ p * n := Nat.mul_le_mul_left p hmn
  have hid_big := factorial_pow_four_mul_termZ hpm1 hpm_le
  have hid_small := factorial_pow_four_mul_termZ hm1 hmn
  have hfac_pm : (((p * m).factorial : ℤ) ^ 4) =
      ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) * (U1Nat p (p * m) : ℤ) := by
    have h1 : (((p * m).factorial : ℤ) ^ 4) =
        (((p * m : ℕ) : ℤ) ^ 4) * (((p * m - 1).factorial : ℤ) ^ 4) := by
      rw [factorial_split_pos hpm1]; ring
    rw [h1, factorial_sub_one_pow_four hpm1, prod_Ico_div_nondiv hp hpm1,
      pm_sub_one_div_p hp hm1]
    have hmul_p : ∏ i ∈ Finset.Ico 1 m, ((p * i : ℕ) : ℤ) ^ 4 =
        ((p : ℤ) ^ (4 * (m - 1))) * ∏ i ∈ Finset.Ico 1 m, (i : ℤ) ^ 4 := by
      trans (∏ i ∈ Finset.Ico 1 m, (p : ℤ) ^ 4 * (i : ℤ) ^ 4)
      · refine Finset.prod_congr rfl fun i _ => by push_cast; ring
      · rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← pow_mul]
    rw [hmul_p, ← factorial_sub_one_pow_four hm1]
    have hU : (∏ j ∈ (Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)), (j : ℤ) ^ 4) =
        (U1Nat p (p * m) : ℤ) := by unfold U1Nat; push_cast; rfl
    rw [hU]
    have hm_fac := factorial_split_pos hm1
    have hp_pow : (p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1)) = (p : ℤ) ^ (4 * m) := by
      rw [← pow_add]; congr 1; omega
    calc ((p * m : ℕ) : ℤ) ^ 4 *
            (((p : ℤ) ^ (4 * (m - 1)) * (((m - 1).factorial : ℤ) ^ 4)) * (U1Nat p (p * m) : ℤ))
        = ((p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1))) *
            (((m : ℤ) * ((m - 1).factorial : ℤ)) ^ 4) * (U1Nat p (p * m) : ℤ) := by
          push_cast; ring
      _ = ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) * (U1Nat p (p * m) : ℤ) := by
          rw [hp_pow, ← hm_fac]
  have hrhs_pm : ∏ j ∈ Finset.Ico 1 (p * m), (((p * n : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2 =
      ((p : ℤ) ^ (4 * (m - 1)) * ∏ i ∈ Finset.Ico 1 m, ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) *
        V1 p (p * n) (p * m) := by
    rw [prod_Ico_div_nondiv hp hpm1, pm_sub_one_div_p hp hm1]
    congr 1
    trans (∏ i ∈ Finset.Ico 1 m, (p : ℤ) ^ 4 * (((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2))
    · refine Finset.prod_congr rfl fun i _ => by push_cast; ring
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← pow_mul]
  rw [hfac_pm, hrhs_pm] at hid_big
  have hp_pow : (p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1)) = (p : ℤ) ^ (4 * m) := by
    rw [← pow_add]; congr 1; omega
  have h_eq : ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) *
      ((U1Nat p (p * m) : ℤ) * termZ (p * n) (p * m)) =
      ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) *
        (termZ n m * V1 p (p * n) (p * m)) := by
    calc ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) *
            ((U1Nat p (p * m) : ℤ) * termZ (p * n) (p * m))
        = ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4) * (U1Nat p (p * m) : ℤ)) *
            termZ (p * n) (p * m) := by ring
      _ = ((p * n : ℕ) : ℤ) ^ 3 * (((p * n : ℕ) : ℤ) - ((p * m : ℕ) : ℤ)) *
            (((p : ℤ) ^ (4 * (m - 1)) * ∏ i ∈ Finset.Ico 1 m, ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) *
              V1 p (p * n) (p * m)) := hid_big
      _ = ((p : ℤ) ^ 4 * (p : ℤ) ^ (4 * (m - 1))) *
            ((n : ℤ) ^ 3 * ((n : ℤ) - (m : ℤ)) *
              ∏ i ∈ Finset.Ico 1 m, ((n : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2) *
            V1 p (p * n) (p * m) := by push_cast; ring
      _ = (p : ℤ) ^ (4 * m) * (((m.factorial : ℤ) ^ 4) * termZ n m) * V1 p (p * n) (p * m) := by
            rw [hp_pow, ← hid_small]
      _ = _ := by ring
  have h_pos : ((p : ℤ) ^ (4 * m) * ((m.factorial : ℤ) ^ 4)) ≠ 0 := by
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp
    have hmfac : (0 : ℤ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    positivity
  exact mul_left_cancel₀ h_pos h_eq

private def unitProdNat (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | a + 1, K => if K ≤ 1 then 1 else U1Nat p K * unitProdNat p a ((K - 1) / p + 1)

private def numProd (p : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 1
  | a + 1, K => if K ≤ 1 then 1 else V1 p (p ^ (a + 1)) K * numProd p a ((K - 1) / p + 1)

private lemma coprime_unitProdNat {p : ℕ} (hp : p.Prime) (a K : ℕ) :
    (unitProdNat p a K).Coprime p := by
  induction a generalizing K with
  | zero => simp [unitProdNat]
  | succ a ih =>
    unfold unitProdNat
    split_ifs
    · simp
    · exact Nat.Coprime.mul_left (coprime_U1Nat hp) (ih _)

private lemma cancel_pow_p {p : ℕ} (hp : 0 < p) :
    ∀ (a K : ℕ), 1 ≤ K → K ≤ p ^ a →
      ∃ P : ℤ, 0 < P ∧
        (((K - 1).factorial : ℤ) ^ 4) = P * (unitProdNat p a K : ℤ) ∧
        (∏ j ∈ Finset.Ico 1 K, (((p ^ a : ℕ) : ℤ) ^ 2 - (j : ℤ) ^ 2) ^ 2) =
          P * numProd p a K
  | 0, K, hK1, hKle => by
    have hK_eq : K = 1 := by simp at hKle; omega
    subst hK_eq
    exact ⟨1, zero_lt_one, by simp [unitProdNat], by simp [numProd]⟩
  | a + 1, K, hK1, hKle => by
    rcases eq_or_lt_of_le hK1 with rfl | hK_gt1
    · exact ⟨1, zero_lt_one, by simp [unitProdNat], by simp [numProd]⟩
    · set K' := (K - 1) / p + 1
      have hK'_ge1 : 1 ≤ K' := Nat.le_add_left 1 ((K - 1) / p)
      have hK'_le : K' ≤ p ^ a := by
        have hlt : (K - 1) / p < p ^ a := by
          rw [Nat.div_lt_iff_lt_mul hp]
          have hpow : p ^ a * p = p ^ (a + 1) := by ring
          omega
        exact Nat.succ_le_of_lt hlt
      obtain ⟨P', hP'_pos, hP'_fac, hP'_prod⟩ := cancel_pow_p hp a K' hK'_ge1 hK'_le
      refine ⟨(p : ℤ) ^ (4 * (K' - 1)) * P', ?_, ?_, ?_⟩
      · have hpz : (0 : ℤ) < p := by exact_mod_cast hp
        positivity
      · have hnot1 : ¬ (K ≤ 1) := by omega
        simp only [unitProdNat, if_neg hnot1, Nat.cast_mul]
        rw [factorial_sub_one_pow_four hK1, prod_Ico_div_nondiv hp hK1]
        have hmul_p : ∏ i ∈ Finset.Ico 1 K', ((p * i : ℕ) : ℤ) ^ 4 =
            ((p : ℤ) ^ (4 * (K' - 1))) * ∏ i ∈ Finset.Ico 1 K', (i : ℤ) ^ 4 := by
          trans (∏ i ∈ Finset.Ico 1 K', (p : ℤ) ^ 4 * (i : ℤ) ^ 4)
          · refine Finset.prod_congr rfl fun i _ => by push_cast; ring
          · rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← pow_mul]
        have hU : (∏ j ∈ (Finset.Ico 1 K).filter (fun j => ¬ (p ∣ j)), (j : ℤ) ^ 4) =
            (U1Nat p K : ℤ) := by unfold U1Nat; push_cast; rfl
        rw [hmul_p, ← factorial_sub_one_pow_four hK'_ge1, hP'_fac, hU]
        ring
      · have hnot1 : ¬ (K ≤ 1) := by omega
        simp only [numProd, if_neg hnot1]
        rw [prod_Ico_div_nondiv hp hK1]
        have hmul_p : ∏ i ∈ Finset.Ico 1 K', (((p ^ (a + 1) : ℕ) : ℤ) ^ 2 - ((p * i : ℕ) : ℤ) ^ 2) ^ 2 =
            ((p : ℤ) ^ (4 * (K' - 1))) *
              ∏ i ∈ Finset.Ico 1 K', (((p ^ a : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2 := by
          trans (∏ i ∈ Finset.Ico 1 K', (p : ℤ) ^ 4 * ((((p ^ a : ℕ) : ℤ) ^ 2 - (i : ℤ) ^ 2) ^ 2))
          · refine Finset.prod_congr rfl fun i _ => by
              have hpa : ((p ^ (a + 1) : ℕ) : ℤ) = (p : ℤ) * ((p ^ a : ℕ) : ℤ) := by
                rw [Nat.pow_succ']; push_cast; rfl
              rw [hpa]; push_cast; ring
          · rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← pow_mul]
        rw [hmul_p, hP'_prod]
        dsimp [V1]
        ring

private lemma termZ_pow_eq {p a k : ℕ} (hp : 0 < p) (hk1 : 1 ≤ k) (hkle : k ≤ p ^ a) :
    (((k ^ 4 * unitProdNat p a k : ℕ) : ℤ)) * termZ (p ^ a) k =
      ((p ^ a : ℕ) : ℤ) ^ 3 * (((p ^ a : ℕ) : ℤ) - (k : ℤ)) * numProd p a k := by
  obtain ⟨P, hP_pos, hP_fac, hP_prod⟩ := cancel_pow_p hp a k hk1 hkle
  have hid := factorial_pow_four_mul_termZ hk1 hkle
  have hk_fac : ((k.factorial : ℤ) ^ 4) = (k : ℤ) ^ 4 * (((k - 1).factorial : ℤ) ^ 4) := by
    rw [factorial_split_pos hk1]; ring
  rw [hk_fac, hP_fac, hP_prod] at hid
  have heq : P * ((((k ^ 4 * unitProdNat p a k : ℕ) : ℤ)) * termZ (p ^ a) k) =
      P * (((p ^ a : ℕ) : ℤ) ^ 3 * (((p ^ a : ℕ) : ℤ) - (k : ℤ)) * numProd p a k) := by
    push_cast at hid ⊢
    linear_combination hid
  exact mul_left_cancel₀ (ne_of_gt hP_pos) heq

private lemma dvd_termZ_pow_nondiv {p a m : ℕ} (hp : p.Prime) (hm1 : 1 ≤ m) (hmle : m ≤ p ^ a)
    (hndvd : ¬ (p ∣ m)) :
    ((p : ℤ) ^ (3 * a)) ∣ termZ (p ^ a) m := by
  have heq := termZ_pow_eq hp.pos hm1 hmle
  have hcop_m : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
  have hcop_prod : (m ^ 4 * unitProdNat p a m).Coprime (p ^ (3 * a)) :=
    (Nat.Coprime.mul_left (hcop_m.pow_left 4) (coprime_unitProdNat hp a m)).pow_right (3 * a)
  have hiscop : IsCoprime ((p ^ (3 * a) : ℕ) : ℤ) (((m ^ 4 * unitProdNat p a m : ℕ) : ℤ)) :=
    hcop_prod.symm.isCoprime
  have hdvd_mul : ((p ^ (3 * a) : ℕ) : ℤ) ∣
      (((m ^ 4 * unitProdNat p a m : ℕ) : ℤ)) * termZ (p ^ a) m := by
    rw [heq]
    refine ⟨(((p ^ a : ℕ) : ℤ) - (m : ℤ)) * numProd p a m, ?_⟩
    push_cast; ring
  simpa using hiscop.dvd_of_dvd_mul_left hdvd_mul

private lemma dvd_termZ_mul_p {p n m d : ℕ} (hp : p.Prime) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hdvd : ((p : ℤ) ^ d) ∣ termZ n m) :
    ((p : ℤ) ^ d) ∣ termZ (p * n) (p * m) := by
  have heq := U1_mul_termZ_mul_p hp.pos hm1 hmn
  have hcop : (U1Nat p (p * m)).Coprime (p ^ d) := (coprime_U1Nat hp).pow_right d
  have hiscop : IsCoprime ((p ^ d : ℕ) : ℤ) (U1Nat p (p * m) : ℤ) := hcop.symm.isCoprime
  obtain ⟨q, hq⟩ := hdvd
  have hdvd_mul : ((p ^ d : ℕ) : ℤ) ∣ (U1Nat p (p * m) : ℤ) * termZ (p * n) (p * m) := by
    rw [heq, hq]
    refine ⟨q * V1 p (p * n) (p * m), ?_⟩
    push_cast; ring
  simpa using hiscop.dvd_of_dvd_mul_left hdvd_mul

private lemma extract_pow_p {p : ℕ} (hp : 1 < p) :
    ∀ m : ℕ, 1 ≤ m → ∃ s w : ℕ, 1 ≤ w ∧ ¬ (p ∣ w) ∧ m = p ^ s * w := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm1
    by_cases hd : p ∣ m
    · obtain ⟨m', rfl⟩ := hd
      have hm'1 : 1 ≤ m' := by
        rcases Nat.eq_zero_or_pos m' with rfl | hpos
        · simp at hm1
        · exact hpos
      have hm'_lt : m' < p * m' := lt_mul_of_one_lt_left hm'1 hp
      obtain ⟨s, w, hw1, hnd, rfl⟩ := ih m' hm'_lt hm'1
      exact ⟨s + 1, w, hw1, hnd, by rw [Nat.pow_succ', mul_assoc]⟩
    · exact ⟨0, m, hm1, hd, by simp⟩

private lemma dvd_termZ_pow_general {p a s w : ℕ} (hp : p.Prime) (hw1 : 1 ≤ w)
    (hndvd : ¬ (p ∣ w)) (hle : p ^ s * w ≤ p ^ a) (hsa : s ≤ a) :
    ((p : ℤ) ^ (3 * (a - s))) ∣ termZ (p ^ a) (p ^ s * w) := by
  induction s generalizing a with
  | zero =>
    simp only [Nat.sub_zero, pow_zero, one_mul] at hle ⊢
    exact dvd_termZ_pow_nondiv hp hw1 hle hndvd
  | succ s ih =>
    rcases a with _ | a
    · omega
    · rw [Nat.succ_sub_succ]
      have hpa : p ^ (a + 1) = p * p ^ a := Nat.pow_succ'
      have hps : p ^ (s + 1) * w = p * (p ^ s * w) := by rw [Nat.pow_succ', mul_assoc]
      have hle' : p ^ s * w ≤ p ^ a := by
        rw [hpa, hps] at hle
        exact Nat.le_of_mul_le_mul_left hle hp.pos
      have hpos_psw : 1 ≤ p ^ s * w := Nat.mul_pos (Nat.pow_pos hp.pos) hw1
      rw [hpa, hps]
      exact dvd_termZ_mul_p hp hpos_psw hle' (ih hle' (by omega))

private lemma dvd_three_termZ_pow {p a m : ℕ} (hp : p.Prime) (hm1 : 1 ≤ m) (hmlt : m < p ^ a) :
    ((p : ℤ) ^ 3) ∣ termZ (p ^ a) m := by
  obtain ⟨s, w, hw1, hnd, rfl⟩ := extract_pow_p hp.one_lt m hm1
  have hsa : s < a := by
    by_contra hge
    have hpow : p ^ a ≤ p ^ s := Nat.pow_le_pow_right hp.pos (by omega)
    have hmul : p ^ a ≤ p ^ s * w := le_trans hpow (Nat.le_mul_of_pos_right _ hw1)
    omega
  have hdvd := dvd_termZ_pow_general hp hw1 hnd (Nat.le_of_lt hmlt) (Nat.le_of_lt hsa)
  exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega : 3 ≤ 3 * (a - s))) hdvd

private lemma prod_sq_sub_linear_zmod {M : ℕ} (S : Finset ℕ) (A : ZMod M) (hA2 : A ^ 2 = 0)
    (hcop : ∀ j ∈ S, j.Coprime M) :
    ∏ j ∈ S, (A - (j : ZMod M) ^ 2) ^ 2 =
      (∏ j ∈ S, (j : ZMod M) ^ 4) * (1 - 2 * A * ∑ j ∈ S, ((j : ZMod M)⁻¹) ^ 2) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hcop_a : a.Coprime M := hcop a (Finset.mem_cons_self a s)
    have hcop_s : ∀ j ∈ s, j.Coprime M := fun j hj => hcop j (Finset.mem_cons.mpr (Or.inr hj))
    rw [Finset.prod_cons, Finset.prod_cons, Finset.sum_cons, ih hcop_s]
    set u : ZMod M := (a : ZMod M)⁻¹
    have hau : (a : ZMod M) * u = 1 := ZMod.coe_mul_inv_eq_one a hcop_a
    have hsingle : (A - (a : ZMod M) ^ 2) ^ 2 = (a : ZMod M) ^ 4 * (1 - 2 * A * u ^ 2) := by
      have hdiff : (A - (a : ZMod M) ^ 2) ^ 2 - (a : ZMod M) ^ 4 * (1 - 2 * A * u ^ 2) =
          A ^ 2 + 2 * A * (a : ZMod M) ^ 2 * (((a : ZMod M) * u) ^ 2 - 1) := by ring
      rw [hA2, hau] at hdiff
      linear_combination hdiff
    rw [hsingle]
    set B : ZMod M := ∑ j ∈ s, ((j : ZMod M)⁻¹) ^ 2
    have hlin : (1 - 2 * A * u ^ 2) * (1 - 2 * A * B) = 1 - 2 * A * (u ^ 2 + B) := by
      have hdiff : (1 - 2 * A * u ^ 2) * (1 - 2 * A * B) - (1 - 2 * A * (u ^ 2 + B)) =
          4 * A ^ 2 * u ^ 2 * B := by ring
      rw [hA2] at hdiff
      linear_combination hdiff
    calc (a : ZMod M) ^ 4 * (1 - 2 * A * u ^ 2) *
            ((∏ j ∈ s, (j : ZMod M) ^ 4) * (1 - 2 * A * B))
        = ((a : ZMod M) ^ 4 * ∏ j ∈ s, (j : ZMod M) ^ 4) *
            ((1 - 2 * A * u ^ 2) * (1 - 2 * A * B)) := by ring
      _ = ((a : ZMod M) ^ 4 * ∏ j ∈ s, (j : ZMod M) ^ 4) *
            (1 - 2 * A * (u ^ 2 + B)) := by rw [hlin]

private lemma zmod_mul_congr_of_dvd {c d : ℕ} {C X Y : ℤ} (hC : (c : ℤ) ∣ C)
    (hXY : (X : ZMod d) = (Y : ZMod d)) :
    ((C * X : ℤ) : ZMod (c * d)) = ((C * Y : ℤ) : ZMod (c * d)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hXY ⊢
  obtain ⟨q₁, hq₁⟩ := hC
  obtain ⟨q₂, hq₂⟩ := hXY
  refine ⟨q₁ * q₂, ?_⟩
  have hsub : C * Y - C * X = C * (Y - X) := by ring
  rw [hsub, hq₁, hq₂]
  push_cast
  ring

private lemma val_inv_cast_eq_inv {M d k : ℕ} [NeZero M] (hdM : d ∣ M) (hcop : k.Coprime M) :
    ((((k : ZMod M)⁻¹).val : ZMod d)) = (k : ZMod d)⁻¹ := by
  have hcop_d : k.Coprime d := hcop.coprime_dvd_right hdM
  have hunit_d : IsUnit (k : ZMod d) := (ZMod.isUnit_iff_coprime k d).mpr hcop_d
  apply hunit_d.mul_left_cancel
  have hmulM : (k : ZMod M) * (((k : ZMod M)⁻¹).val : ZMod M) = 1 := by
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one k hcop
  let f : ZMod M →+* ZMod d := ZMod.castHom hdM (ZMod d)
  have hf := congrArg f hmulM
  simp only [map_mul, map_natCast, map_one] at hf
  rw [hf, ZMod.coe_mul_inv_eq_one k hcop_d]

private lemma sum_nondiv_inv_sq_pow_eq_zero {p s : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ j ∈ (Finset.Ico 1 (p ^ s)).filter (fun j => ¬ (p ∣ j)),
      ((j : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  set Q := p ^ s
  have hQ_gt1 : 1 < Q := one_lt_pow₀ hp.one_lt (by omega)
  have : NeZero Q := ⟨by omega⟩
  set U : Finset (ZMod Q) := Finset.univ.filter IsUnit
  have hbij : ∑ j ∈ (Finset.Ico 1 Q).filter (fun j => ¬ (p ∣ j)), ((j : ZMod Q)⁻¹) ^ 2 =
      ∑ x ∈ U, (x⁻¹) ^ 2 := by
    refine Finset.sum_bij (fun j _ => (j : ZMod Q)) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Ico] at hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime j Q).mpr ?_⟩
      exact ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_right s
    · intro j₁ hj₁ j₂ hj₂ h
      rw [Finset.mem_filter, Finset.mem_Ico] at hj₁ hj₂
      have hm := (ZMod.natCast_eq_natCast_iff' j₁ j₂ Q).mp h
      rwa [Nat.mod_eq_of_lt hj₁.1.2, Nat.mod_eq_of_lt hj₂.1.2] at hm
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hcop_x : x.val.Coprime Q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
        exact hx.2
      have hcop_p : x.val.Coprime p :=
        hcop_x.coprime_dvd_right (dvd_pow_self p (by omega : s ≠ 0))
      have hndvd : ¬ (p ∣ x.val) := by
        intro hd
        have h1 : p ∣ 1 := by
          rw [← hcop_p.gcd_eq_one]
          exact Nat.dvd_gcd hd (dvd_refl p)
        have := Nat.le_of_dvd (by decide) h1
        omega
      have hx_pos : 1 ≤ x.val := by
        rcases Nat.eq_zero_or_pos x.val with h0 | hpos
        · exfalso; exact hndvd (by simp [h0])
        · exact hpos
      exact ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hx_pos, ZMod.val_lt x⟩, hndvd⟩,
        ZMod.natCast_zmod_val x⟩
  rw [hbij]
  set S : ZMod Q := ∑ x ∈ U, (x⁻¹) ^ 2
  have hcop2 : (2 : ℕ).Coprime Q :=
    ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by decide) hd; omega)).symm).pow_right s
  have hu2 : IsUnit (2 : ZMod Q) := (ZMod.isUnit_iff_coprime 2 Q).mpr hcop2
  have h2_inv : (2 : ZMod Q) * (2 : ZMod Q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one 2 hcop2
  have hu2_inv : IsUnit ((2 : ZMod Q)⁻¹) :=
    ⟨⟨(2 : ZMod Q)⁻¹, (2 : ZMod Q), mul_comm (2 : ZMod Q) ((2 : ZMod Q)⁻¹) ▸ h2_inv, h2_inv⟩, rfl⟩
  have hreindex : ∑ x ∈ U, (((2 : ZMod Q) * x)⁻¹) ^ 2 = S := by
    dsimp [S]
    refine Finset.sum_bij (fun x _ => (2 : ZMod Q) * x) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hu2.mul hx.2⟩
    · intro x₁ _ x₂ _ h
      exact hu2.mul_left_cancel h
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨(2 : ZMod Q)⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2_inv.mul hy.2⟩, ?_⟩
      calc (2 : ZMod Q) * ((2 : ZMod Q)⁻¹ * y) = ((2 : ZMod Q) * (2 : ZMod Q)⁻¹) * y := by ring
        _ = y := by rw [h2_inv, one_mul]
  have hscale : S = ((2 : ZMod Q)⁻¹ ^ 2) * S := by
    conv_lhs => rw [← hreindex]
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_filter] at hx
    have hx_inv : x * x⁻¹ = 1 := mul_comm x x⁻¹ ▸ ZMod.inv_mul_of_unit x hx.2
    have h2x_unit : IsUnit ((2 : ZMod Q) * x) := hu2.mul hx.2
    have h2x_inv : ((2 : ZMod Q) * x)⁻¹ = (2 : ZMod Q)⁻¹ * x⁻¹ := by
      apply h2x_unit.mul_left_cancel
      have h1 : ((2 : ZMod Q) * x) * ((2 : ZMod Q) * x)⁻¹ = 1 :=
        mul_comm ((2 : ZMod Q) * x) _ ▸ ZMod.inv_mul_of_unit _ h2x_unit
      rw [h1]
      symm
      calc ((2 : ZMod Q) * x) * ((2 : ZMod Q)⁻¹ * x⁻¹)
          = ((2 : ZMod Q) * (2 : ZMod Q)⁻¹) * (x * x⁻¹) := by ring
        _ = 1 := by rw [h2_inv, hx_inv, one_mul]
    rw [h2x_inv]; ring
  have h3S : (3 : ZMod Q) * S = 0 := by
    have h4S : (4 : ZMod Q) * S = S := by
      conv_lhs => rw [hscale]
      calc (4 : ZMod Q) * ((2 : ZMod Q)⁻¹ ^ 2 * S)
          = ((2 : ZMod Q) * (2 : ZMod Q)⁻¹) ^ 2 * S := by ring
        _ = S := by rw [h2_inv, one_pow, one_mul]
    linear_combination h4S
  have hcop3 : (3 : ℕ).Coprime Q :=
    ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by decide) hd; omega)).symm).pow_right s
  have hu3 : IsUnit (3 : ZMod Q) := (ZMod.isUnit_iff_coprime 3 Q).mpr hcop3
  exact hu3.mul_left_cancel (h3S.trans (mul_zero (3 : ZMod Q)).symm)

private lemma sum_nondiv_inv_sq_mul_pow_eq_zero {p s w : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 1 ≤ s) :
    ∑ j ∈ (Finset.Ico 1 (p ^ s * w)).filter (fun j => ¬ (p ∣ j)),
      ((j : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  induction w with
  | zero => simp
  | succ w ih =>
    set Q := p ^ s
    have hQ_pos : 1 ≤ Q := Nat.pow_pos hp.pos
    rcases Nat.eq_zero_or_pos w with rfl | hw_pos
    · simpa using sum_nondiv_inv_sq_pow_eq_zero hp hp5 hs
    · have hle : Q * w ≤ Q * (w + 1) := Nat.mul_le_mul_left Q (by omega)
      have h1le : 1 ≤ Q * w := Nat.mul_pos hQ_pos hw_pos
      have hunion : Finset.Ico 1 (Q * (w + 1)) =
          Finset.Ico 1 (Q * w) ∪ Finset.Ico (Q * w) (Q * (w + 1)) :=
        (Finset.Ico_union_Ico_eq_Ico h1le hle).symm
      have hdisj : Disjoint ((Finset.Ico 1 (Q * w)).filter (fun j => ¬ (p ∣ j)))
          ((Finset.Ico (Q * w) (Q * (w + 1))).filter (fun j => ¬ (p ∣ j))) :=
        Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 1 (Q * w) (Q * (w + 1)))
      rw [hunion, Finset.filter_union, Finset.sum_union hdisj, ih, zero_add]
      have hshift : ∑ j ∈ (Finset.Ico (Q * w) (Q * (w + 1))).filter (fun j => ¬ (p ∣ j)),
          ((j : ZMod Q)⁻¹) ^ 2 =
          ∑ r ∈ (Finset.Ico 1 Q).filter (fun r => ¬ (p ∣ r)), ((r : ZMod Q)⁻¹) ^ 2 := by
        have hp_dvd_Qw : p ∣ Q * w :=
          dvd_mul_of_dvd_left (dvd_pow_self p (by omega : s ≠ 0)) w
        refine Finset.sum_bij (fun j _ => j - Q * w) ?_ ?_ ?_ ?_
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
          have hj_gt : Q * w < j := by
            rcases eq_or_lt_of_le hj.1.1 with rfl | hlt
            · exfalso; exact hj.2 hp_dvd_Qw
            · exact hlt
          have hqw1 : Q * (w + 1) = Q * w + Q := by ring
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro hd_sub
          apply hj.2
          have hj_eq : j = Q * w + (j - Q * w) := by omega
          rw [hj_eq]
          exact dvd_add hp_dvd_Qw hd_sub
        · intro j₁ hj₁ j₂ hj₂ h
          rw [Finset.mem_filter, Finset.mem_Ico] at hj₁ hj₂; omega
        · intro r hr
          rw [Finset.mem_filter, Finset.mem_Ico] at hr
          refine ⟨Q * w + r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩, by omega⟩
          · have hqw1 : Q * (w + 1) = Q * w + Q := by ring
            omega
          · intro hd_add
            exact hr.2 ((Nat.dvd_add_right hp_dvd_Qw).mp hd_add)
        · intro j hj
          rw [Finset.mem_filter, Finset.mem_Ico] at hj
          have hj_eq : (j : ZMod Q) = (((j - Q * w : ℕ) : ZMod Q)) := by
            have hnat : j = Q * w + (j - Q * w) := by omega
            conv_lhs => rw [hnat]
            push_cast
            have hQ0 : (Q : ZMod Q) = 0 := ZMod.natCast_self Q
            rw [hQ0, zero_mul, zero_add]
          rw [hj_eq]
      rw [hshift]
      exact sum_nondiv_inv_sq_pow_eq_zero hp hp5 hs

private lemma sum_nondiv_inv_cube_zmod_p_eq_zero {p s : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hs : 1 ≤ s) :
    ∑ v ∈ (Finset.Ico 1 (p ^ s)).filter (fun v => ¬ (p ∣ v)),
      ((v : ZMod p)⁻¹) ^ 3 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set S : ZMod p := ∑ v ∈ (Finset.Ico 1 (p ^ s)).filter (fun v => ¬ (p ∣ v)), ((v : ZMod p)⁻¹) ^ 3
  have hp_dvd_ps : p ∣ p ^ s := dvd_pow_self p (by omega : s ≠ 0)
  have hrefl : S = -S := by
    dsimp [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun v _ => p ^ s - v) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_filter, Finset.mem_Ico] at hv ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd
      apply hv.2
      have heq : p ^ s = (p ^ s - v) + v := by omega
      exact (Nat.dvd_add_right hd).mp (heq ▸ hp_dvd_ps)
    · intro v₁ hv₁ v₂ hv₂ h
      rw [Finset.mem_filter, Finset.mem_Ico] at hv₁ hv₂; omega
    · intro v hv
      rw [Finset.mem_filter, Finset.mem_Ico] at hv
      refine ⟨p ^ s - v, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd
      apply hv.2
      have heq : p ^ s = (p ^ s - v) + v := by omega
      exact (Nat.dvd_add_right hd).mp (heq ▸ hp_dvd_ps)
    · intro v hv
      rw [Finset.mem_filter, Finset.mem_Ico] at hv
      have hcast' : (((p ^ s - v : ℕ) : ZMod p)) = -(v : ZMod p) := by
        rw [Nat.cast_sub (Nat.le_of_lt hv.1.2)]
        have hps0 : (((p ^ s : ℕ) : ZMod p)) = 0 :=
          (ZMod.natCast_eq_zero_iff (p ^ s) p).mpr hp_dvd_ps
        rw [hps0, zero_sub]
      rw [hcast', inv_neg]
      ring
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
    omega
  have h2S : (2 : ZMod p) * S = 0 := by linear_combination hrefl
  exact (mul_eq_zero.mp h2S).resolve_left h2ne

private lemma sum_nondiv_inv_sq_top_slice {p r u : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hr2 : 2 ≤ r) :
    ∑ j ∈ (Finset.Ico 1 (p ^ (r - 1) * u)).filter (fun j => ¬ (p ∣ j)),
      ((j : ZMod (p ^ r))⁻¹) ^ 2 =
      (u : ZMod (p ^ r)) *
        ∑ v ∈ (Finset.Ico 1 (p ^ (r - 1))).filter (fun v => ¬ (p ∣ v)),
          ((v : ZMod (p ^ r))⁻¹) ^ 2 := by
  set Q := p ^ (r - 1)
  set R := p ^ r
  have hR_gt1 : 1 < R := one_lt_pow₀ hp.one_lt (by omega)
  have : NeZero R := ⟨by omega⟩
  have hQ_pos : 1 ≤ Q := Nat.pow_pos hp.pos
  have hp_dvd_Q : p ∣ Q := dvd_pow_self p (by omega : r - 1 ≠ 0)
  have hR0 : (p : ZMod R) ^ r = 0 := by
    calc (p : ZMod R) ^ r = ((p ^ r : ℕ) : ZMod R) := by norm_cast
      _ = 0 := ZMod.natCast_self R
  have hQ2_zero : (Q : ZMod R) ^ 2 = 0 := by
    have h2 : 2 * (r - 1) = r + (r - 2) := by omega
    calc (Q : ZMod R) ^ 2 = (p : ZMod R) ^ (2 * (r - 1)) := by dsimp [Q]; push_cast; ring
      _ = (p : ZMod R) ^ r * (p : ZMod R) ^ (r - 2) := by rw [h2, pow_add]
      _ = 0 := by rw [hR0, zero_mul]
  have hQ_cube_zero : (Q : ZMod R) *
      ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod R)⁻¹) ^ 3 = 0 := by
    let S3_nat : ℕ := ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod R)⁻¹).val ^ 3
    have hcast : (S3_nat : ZMod R) =
        ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod R)⁻¹) ^ 3 := by
      dsimp [S3_nat]; push_cast
      refine Finset.sum_congr rfl fun v _ => by rw [ZMod.natCast_zmod_val]
    have hmod_p : (S3_nat : ZMod p) = 0 := by
      dsimp [S3_nat]; push_cast
      have hcongr : ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)),
          ((((v : ZMod R)⁻¹).val : ZMod p)) ^ 3 =
          ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod p)⁻¹) ^ 3 := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [Finset.mem_filter] at hv
        have hcop_v : v.Coprime R := ((hp.coprime_iff_not_dvd.mpr hv.2).symm).pow_right r
        rw [val_inv_cast_eq_inv (dvd_pow_self p (by omega : r ≠ 0)) hcop_v]
      rw [hcongr]
      exact sum_nondiv_inv_cube_zmod_p_eq_zero hp hp2 (by omega)
    obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff S3_nat p).mp hmod_p
    rw [← hcast, ht]
    have hQp : Q * p = R := by
      dsimp [Q, R]
      rw [← pow_succ]
      congr 1; omega
    calc (Q : ZMod R) * ((p * t : ℕ) : ZMod R)
        = (((Q * p : ℕ) : ZMod R)) * (t : ZMod R) := by push_cast; ring
      _ = 0 := by rw [hQp, ZMod.natCast_self R, zero_mul]
  induction u with
  | zero => simp
  | succ u ih =>
    rcases Nat.eq_zero_or_pos u with rfl | hu_pos
    · simp
    · have hle : Q * u ≤ Q * (u + 1) := Nat.mul_le_mul_left Q (by omega)
      have h1le : 1 ≤ Q * u := Nat.mul_pos hQ_pos hu_pos
      have hunion : Finset.Ico 1 (Q * (u + 1)) =
          Finset.Ico 1 (Q * u) ∪ Finset.Ico (Q * u) (Q * (u + 1)) :=
        (Finset.Ico_union_Ico_eq_Ico h1le hle).symm
      have hdisj : Disjoint ((Finset.Ico 1 (Q * u)).filter (fun j => ¬ (p ∣ j)))
          ((Finset.Ico (Q * u) (Q * (u + 1))).filter (fun j => ¬ (p ∣ j))) :=
        Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 1 (Q * u) (Q * (u + 1)))
      rw [hunion, Finset.filter_union, Finset.sum_union hdisj, ih]
      have hblock : ∑ j ∈ (Finset.Ico (Q * u) (Q * (u + 1))).filter (fun j => ¬ (p ∣ j)),
          ((j : ZMod R)⁻¹) ^ 2 =
          ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod R)⁻¹) ^ 2 := by
        have hp_dvd_Qu : p ∣ Q * u := dvd_mul_of_dvd_left hp_dvd_Q u
        have hbij : ∑ j ∈ (Finset.Ico (Q * u) (Q * (u + 1))).filter (fun j => ¬ (p ∣ j)),
            ((j : ZMod R)⁻¹) ^ 2 =
            ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)),
              (((Q * u + v : ℕ) : ZMod R)⁻¹) ^ 2 := by
          refine Finset.sum_bij (fun j _ => j - Q * u) ?_ ?_ ?_ ?_
          · intro j hj
            rw [Finset.mem_filter, Finset.mem_Ico] at hj ⊢
            have hj_gt : Q * u < j := by
              rcases eq_or_lt_of_le hj.1.1 with rfl | hlt
              · exfalso; exact hj.2 hp_dvd_Qu
              · exact hlt
            have hqu1 : Q * (u + 1) = Q * u + Q := by ring
            refine ⟨⟨by omega, by omega⟩, ?_⟩
            intro hd_sub
            apply hj.2
            have hj_eq : j = Q * u + (j - Q * u) := by omega
            rw [hj_eq]
            exact dvd_add hp_dvd_Qu hd_sub
          · intro j₁ hj₁ j₂ hj₂ h
            rw [Finset.mem_filter, Finset.mem_Ico] at hj₁ hj₂; omega
          · intro v hv
            rw [Finset.mem_filter, Finset.mem_Ico] at hv
            refine ⟨Q * u + v, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩, by omega⟩
            · have hqu1 : Q * (u + 1) = Q * u + Q := by ring
              omega
            · intro hd_add
              exact hv.2 ((Nat.dvd_add_right hp_dvd_Qu).mp hd_add)
          · intro j hj
            rw [Finset.mem_filter, Finset.mem_Ico] at hj
            rw [show Q * u + (j - Q * u) = j by omega]
        rw [hbij]
        have hterm_expand : ∀ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)),
            (((Q * u + v : ℕ) : ZMod R)⁻¹) ^ 2 =
              ((v : ZMod R)⁻¹) ^ 2 - 2 * (u : ZMod R) * (Q : ZMod R) * ((v : ZMod R)⁻¹) ^ 3 := by
          intro v hv
          rw [Finset.mem_filter] at hv
          set x : ZMod R := (v : ZMod R)⁻¹
          set B : ZMod R := (Q : ZMod R) * (u : ZMod R)
          have hB2 : B ^ 2 = 0 := by
            calc B ^ 2 = (Q : ZMod R) ^ 2 * (u : ZMod R) ^ 2 := by dsimp [B]; ring
              _ = 0 := by rw [hQ2_zero, zero_mul]
          have hcop_v : v.Coprime R := ((hp.coprime_iff_not_dvd.mpr hv.2).symm).pow_right r
          have hvx : (v : ZMod R) * x = 1 := ZMod.coe_mul_inv_eq_one v hcop_v
          have hcop_Quv : (Q * u + v).Coprime R := by
            refine ((hp.coprime_iff_not_dvd.mpr ?_).symm).pow_right r
            intro hd_add
            exact hv.2 ((Nat.dvd_add_right hp_dvd_Qu).mp hd_add)
          have hunit_Quv : IsUnit (((Q * u + v : ℕ) : ZMod R)) :=
            (ZMod.isUnit_iff_coprime (Q * u + v) R).mpr hcop_Quv
          have hinv_Quv : (((Q * u + v : ℕ) : ZMod R))⁻¹ = x - B * x ^ 2 := by
            apply hunit_Quv.mul_left_cancel
            rw [ZMod.coe_mul_inv_eq_one (Q * u + v) hcop_Quv]
            have hcast : (((Q * u + v : ℕ) : ZMod R)) = B + (v : ZMod R) := by
              dsimp [B]; push_cast; ring
            rw [hcast]
            symm
            calc (B + (v : ZMod R)) * (x - B * x ^ 2)
                = (v : ZMod R) * x + B * x * (1 - (v : ZMod R) * x) - B ^ 2 * x ^ 2 := by ring
              _ = 1 := by rw [hvx, hB2]; ring
          rw [hinv_Quv]
          have hsq : (x - B * x ^ 2) ^ 2 = x ^ 2 - 2 * B * x ^ 3 := by
            have hdiff : (x - B * x ^ 2) ^ 2 - (x ^ 2 - 2 * B * x ^ 3) = B ^ 2 * x ^ 4 := by ring
            rw [hB2, zero_mul, sub_eq_zero] at hdiff
            exact hdiff
          rw [hsq]; dsimp [B]; ring
        rw [Finset.sum_congr rfl hterm_expand, Finset.sum_sub_distrib]
        have htail0 : ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)),
            2 * (u : ZMod R) * (Q : ZMod R) * ((v : ZMod R)⁻¹) ^ 3 = 0 := by
          trans (2 * (u : ZMod R) * ((Q : ZMod R) *
              ∑ v ∈ (Finset.Ico 1 Q).filter (fun v => ¬ (p ∣ v)), ((v : ZMod R)⁻¹) ^ 3))
          · rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => by ring
          · rw [hQ_cube_zero, mul_zero]
        rw [htail0, sub_zero]
      rw [hblock]
      push_cast; ring

private lemma numProd_mod_p3 {p : ℕ} (hp : p.Prime) :
    ∀ (a K : ℕ), 1 ≤ a → 1 ≤ K → K ≤ p ^ a →
      (numProd p a K : ZMod (p ^ 3)) =
        (unitProdNat p a K : ZMod (p ^ 3)) *
          (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
            ∑ c ∈ Finset.Ico 1 ((K - 1) / p ^ (a - 1) + 1), ((c : ZMod (p ^ 3))⁻¹) ^ 2)
  | 0, _, ha, _, _ => by omega
  | 1, K, _, hK1, hKle => by
    simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.sub_add_cancel hK1]
    rcases eq_or_lt_of_le hK1 with rfl | hK_gt1
    · simp [numProd, unitProdNat]
    · have hnot1 : ¬ (K ≤ 1) := by omega
      have hnum_1 : numProd p 1 K = V1 p p K := by
        rw [numProd, if_neg hnot1, zero_add, pow_one]; simp [numProd]
      have hunit_1 : unitProdNat p 1 K = U1Nat p K := by
        rw [unitProdNat, if_neg hnot1]; simp [unitProdNat]
      have hfilt : (Finset.Ico 1 K).filter (fun j => ¬ (p ∣ j)) = Finset.Ico 1 K := by
        refine Finset.filter_true_of_mem fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        simp at hKle
        exact Nat.not_dvd_of_pos_of_lt hj.1 (lt_of_lt_of_le hj.2 hKle)
      have hA2 : (((p : ZMod (p ^ 3)) ^ 2) ^ 2) = 0 := by
        have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
          calc (p : ZMod (p ^ 3)) ^ 3 = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by norm_cast
            _ = 0 := ZMod.natCast_self (p ^ 3)
        calc ((p : ZMod (p ^ 3)) ^ 2) ^ 2 = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) := by ring
          _ = 0 := by rw [hp3, zero_mul]
      have hcop : ∀ j ∈ Finset.Ico 1 K, j.Coprime (p ^ 3) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        simp at hKle
        exact ((hp.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt hj.1 (lt_of_lt_of_le hj.2 hKle))).symm).pow_right 3
      have hV : (V1 p p K : ZMod (p ^ 3)) =
          ∏ j ∈ Finset.Ico 1 K, ((p : ZMod (p ^ 3)) ^ 2 - (j : ZMod (p ^ 3)) ^ 2) ^ 2 := by
        unfold V1; rw [hfilt]; push_cast; rfl
      have hU : (U1Nat p K : ZMod (p ^ 3)) = ∏ j ∈ Finset.Ico 1 K, (j : ZMod (p ^ 3)) ^ 4 := by
        unfold U1Nat; rw [hfilt]; push_cast; rfl
      rw [hnum_1, hunit_1, hV, hU]
      simpa using prod_sq_sub_linear_zmod (Finset.Ico 1 K) ((p : ZMod (p ^ 3)) ^ 2) hA2 hcop
  | a + 2, K, _, hK1, hKle => by
    rcases eq_or_lt_of_le hK1 with rfl | hK_gt1
    · simp [numProd, unitProdNat]
    · have hnot1 : ¬ (K ≤ 1) := by omega
      set K' := (K - 1) / p + 1
      have hK'_ge1 : 1 ≤ K' := Nat.le_add_left 1 _
      have hK'_le : K' ≤ p ^ (a + 1) := by
        have hlt : (K - 1) / p < p ^ (a + 1) := by
          rw [Nat.div_lt_iff_lt_mul hp.pos, ← pow_succ]
          change K - 1 < p ^ (a + 2)
          omega
        exact Nat.succ_le_of_lt hlt
      have ih := numProd_mod_p3 hp (a + 1) K' (by omega) hK'_ge1 hK'_le
      have hV_eq_U : (V1 p (p ^ (a + 2)) K : ZMod (p ^ 3)) = (U1Nat p K : ZMod (p ^ 3)) := by
        unfold V1 U1Nat
        push_cast
        refine Finset.prod_congr rfl fun j _ => ?_
        have hpa0 : ((p : ZMod (p ^ 3)) ^ (a + 2)) ^ 2 = 0 := by
          have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
            calc (p : ZMod (p ^ 3)) ^ 3 = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by norm_cast
              _ = 0 := ZMod.natCast_self (p ^ 3)
          have hexp : 2 * (a + 2) = 3 + (2 * a + 1) := by omega
          calc ((p : ZMod (p ^ 3)) ^ (a + 2)) ^ 2
              = (p : ZMod (p ^ 3)) ^ (2 * (a + 2)) := by ring
            _ = (p : ZMod (p ^ 3)) ^ 3 * (p : ZMod (p ^ 3)) ^ (2 * a + 1) := by rw [hexp, pow_add]
            _ = 0 := by rw [hp3, zero_mul]
        rw [hpa0, zero_sub]; ring
      have hdiv_eq : (K' - 1) / p ^ a = (K - 1) / p ^ (a + 1) := by
        have hK'sub : K' - 1 = (K - 1) / p := rfl
        rw [hK'sub, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      have hnum_step : numProd p (a + 2) K = V1 p (p ^ (a + 2)) K * numProd p (a + 1) K' := by
        rw [numProd, if_neg hnot1]
      have hunit_step : unitProdNat p (a + 2) K = U1Nat p K * unitProdNat p (a + 1) K' := by
        rw [unitProdNat, if_neg hnot1]
      rw [hnum_step, hunit_step, Int.cast_mul, Nat.cast_mul]
      simp only [Nat.add_sub_cancel] at ih
      change _ = _ * (1 - 2 * (p : ZMod (p ^ 3)) ^ 2 *
        ∑ c ∈ Finset.Ico 1 ((K - 1) / p ^ (a + 1) + 1), ((c : ZMod (p ^ 3))⁻¹) ^ 2)
      rw [hV_eq_U, ih, hdiv_eq]
      ring

private lemma top_slice_termZ_mod_p4 {p : ℕ} (hp : p.Prime) :
    ∀ (a u : ℕ), 1 ≤ a → 1 ≤ u → u < p →
      (termZ (p ^ a) (p ^ (a - 1) * u) : ZMod (p ^ 4)) =
        -(p : ZMod (p ^ 4)) ^ 3 * ((u : ZMod (p ^ 4))⁻¹) ^ 3
  | 0, _, ha, _, _ => by omega
  | 1, u, _, hu1, hup => by
    simp only [Nat.sub_self, pow_zero, pow_one, one_mul]
    have heq := congrArg (Int.cast : ℤ → ZMod (p ^ 4))
      (termZ_pow_eq hp.pos hu1 (show u ≤ p ^ 1 by simpa using Nat.le_of_lt hup))
    push_cast at heq
    simp only [pow_one] at heq
    have hp4_0 : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
      calc (p : ZMod (p ^ 4)) ^ 4 = ((p ^ 4 : ℕ) : ZMod (p ^ 4)) := by norm_cast
        _ = 0 := ZMod.natCast_self (p ^ 4)
    have hp3_num : (p : ZMod (p ^ 4)) ^ 3 * (numProd p 1 u : ZMod (p ^ 4)) =
        (p : ZMod (p ^ 4)) ^ 3 * (unitProdNat p 1 u : ZMod (p ^ 4)) := by
      rcases eq_or_lt_of_le hu1 with rfl | hu_gt1
      · simp [numProd, unitProdNat]
      · have hnot1 : ¬ (u ≤ 1) := by omega
        have hnum_1 : numProd p 1 u = V1 p p u := by
          rw [numProd, if_neg hnot1, zero_add, pow_one]; simp [numProd]
        have hunit_1 : unitProdNat p 1 u = U1Nat p u := by
          rw [unitProdNat, if_neg hnot1]; simp [unitProdNat]
        rw [hnum_1, hunit_1]
        unfold V1 U1Nat
        push_cast
        -- Induct over the filtered finset using `p^3 * (p^2 - j^2)^2 = p^3 * j^4` in `ZMod (p^4)`.
        set S := (Finset.Ico 1 u).filter (fun j => ¬ (p ∣ j))
        induction S using Finset.cons_induction with
        | empty => simp
        | cons j s hj ih =>
          rw [Finset.prod_cons, Finset.prod_cons, ← mul_assoc]
          have hstep : (p : ZMod (p ^ 4)) ^ 3 * ((p : ZMod (p ^ 4)) ^ 2 - (j : ZMod (p ^ 4)) ^ 2) ^ 2 =
              (p : ZMod (p ^ 4)) ^ 3 * (j : ZMod (p ^ 4)) ^ 4 := by
            have hdiff : (p : ZMod (p ^ 4)) ^ 3 * ((p : ZMod (p ^ 4)) ^ 2 - (j : ZMod (p ^ 4)) ^ 2) ^ 2 -
                (p : ZMod (p ^ 4)) ^ 3 * (j : ZMod (p ^ 4)) ^ 4 =
                (p : ZMod (p ^ 4)) ^ 4 * ((p : ZMod (p ^ 4)) ^ 3 - 2 * (p : ZMod (p ^ 4)) * (j : ZMod (p ^ 4)) ^ 2) := by
              ring
            rw [hp4_0, zero_mul, sub_eq_zero] at hdiff
            exact hdiff
          calc (p : ZMod (p ^ 4)) ^ 3 * ((p : ZMod (p ^ 4)) ^ 2 - (j : ZMod (p ^ 4)) ^ 2) ^ 2 *
                  ∏ x ∈ s, ((p : ZMod (p ^ 4)) ^ 2 - (x : ZMod (p ^ 4)) ^ 2) ^ 2
              = (j : ZMod (p ^ 4)) ^ 4 * ((p : ZMod (p ^ 4)) ^ 3 *
                  ∏ x ∈ s, ((p : ZMod (p ^ 4)) ^ 2 - (x : ZMod (p ^ 4)) ^ 2) ^ 2) := by
                rw [hstep]; ring
            _ = (p : ZMod (p ^ 4)) ^ 3 * ((j : ZMod (p ^ 4)) ^ 4 * ∏ x ∈ s, (x : ZMod (p ^ 4)) ^ 4) := by
                rw [ih]; ring
    have hcop_u : u.Coprime (p ^ 4) :=
      ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hu1 hup)).symm).pow_right 4
    have hu_inv : (u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one u hcop_u
    have hcop_tot : (u ^ 4 * unitProdNat p 1 u).Coprime (p ^ 4) :=
      Nat.Coprime.mul_left (hcop_u.pow_left 4) ((coprime_unitProdNat hp 1 u).pow_right 4)
    have hunit_tot : IsUnit (((u : ZMod (p ^ 4)) ^ 4 * (unitProdNat p 1 u : ZMod (p ^ 4)))) := by
      have hu := (ZMod.isUnit_iff_coprime (u ^ 4 * unitProdNat p 1 u) (p ^ 4)).mpr hcop_tot
      simpa using hu
    apply hunit_tot.mul_left_cancel
    rw [heq]
    calc (p : ZMod (p ^ 4)) ^ 3 * ((p : ZMod (p ^ 4)) - (u : ZMod (p ^ 4))) *
            (numProd p 1 u : ZMod (p ^ 4))
        = ((p : ZMod (p ^ 4)) - (u : ZMod (p ^ 4))) *
            ((p : ZMod (p ^ 4)) ^ 3 * (numProd p 1 u : ZMod (p ^ 4))) := by ring
      _ = ((p : ZMod (p ^ 4)) - (u : ZMod (p ^ 4))) *
            ((p : ZMod (p ^ 4)) ^ 3 * (unitProdNat p 1 u : ZMod (p ^ 4))) := by rw [hp3_num]
      _ = (p : ZMod (p ^ 4)) ^ 4 * (unitProdNat p 1 u : ZMod (p ^ 4)) -
            (p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)) * 1 ^ 3 *
              (unitProdNat p 1 u : ZMod (p ^ 4)) := by ring
      _ = 0 - (p : ZMod (p ^ 4)) ^ 3 * (u : ZMod (p ^ 4)) *
            ((u : ZMod (p ^ 4)) * (u : ZMod (p ^ 4))⁻¹) ^ 3 *
              (unitProdNat p 1 u : ZMod (p ^ 4)) := by rw [hp4_0, zero_mul, hu_inv]
      _ = ((u : ZMod (p ^ 4)) ^ 4 * (unitProdNat p 1 u : ZMod (p ^ 4))) *
            (-(p : ZMod (p ^ 4)) ^ 3 * ((u : ZMod (p ^ 4))⁻¹) ^ 3) := by ring
  | a + 2, u, _, hu1, hup => by
    change (termZ (p ^ (a + 2)) (p ^ (a + 1) * u) : ZMod (p ^ 4)) = _
    set m := p ^ a * u
    have hm1 : 1 ≤ m := Nat.mul_pos (Nat.pow_pos hp.pos) hu1
    have hmlt : m < p ^ (a + 1) := by
      dsimp [m]; rw [Nat.pow_succ]; exact Nat.mul_lt_mul_of_pos_left hup (Nat.pow_pos hp.pos)
    have hpa2 : p ^ (a + 2) = p * p ^ (a + 1) := Nat.pow_succ'
    have hpm : p ^ (a + 1) * u = p * m := by dsimp [m]; rw [Nat.pow_succ', mul_assoc]
    rw [hpm]
    have hstep := congrArg (Int.cast : ℤ → ZMod (p ^ 4))
      (U1_mul_termZ_mul_p hp.pos hm1 (Nat.le_of_lt hmlt))
    push_cast at hstep
    rw [← hpa2] at hstep
    have hV_eq_U : (V1 p (p ^ (a + 2)) (p * m) : ZMod (p ^ 4)) =
        (U1Nat p (p * m) : ZMod (p ^ 4)) := by
      unfold V1 U1Nat; push_cast
      refine Finset.prod_congr rfl fun j _ => ?_
      have hpa0 : ((p : ZMod (p ^ 4)) ^ (a + 2)) ^ 2 = 0 := by
        have hp4_0 : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
          calc (p : ZMod (p ^ 4)) ^ 4 = ((p ^ 4 : ℕ) : ZMod (p ^ 4)) := by norm_cast
            _ = 0 := ZMod.natCast_self (p ^ 4)
        have hexp : 2 * (a + 2) = 4 + 2 * a := by omega
        calc ((p : ZMod (p ^ 4)) ^ (a + 2)) ^ 2
            = (p : ZMod (p ^ 4)) ^ (2 * (a + 2)) := by ring
          _ = (p : ZMod (p ^ 4)) ^ 4 * (p : ZMod (p ^ 4)) ^ (2 * a) := by rw [hexp, pow_add]
          _ = 0 := by rw [hp4_0, zero_mul]
      rw [hpa0, zero_sub]; ring
    rw [hV_eq_U] at hstep
    have hcop_U : (U1Nat p (p * m)).Coprime (p ^ 4) := (coprime_U1Nat hp).pow_right 4
    have hunit_U : IsUnit (U1Nat p (p * m) : ZMod (p ^ 4)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hcop_U
    have heq_m : (termZ (p ^ (a + 2)) (p * m) : ZMod (p ^ 4)) =
        (termZ (p ^ (a + 1)) m : ZMod (p ^ 4)) := by
      apply hunit_U.mul_left_cancel
      rw [hstep, mul_comm]
    rw [heq_m]
    exact top_slice_termZ_mod_p4 hp (a + 1) u (by omega) hu1 hup

private theorem prime_power_lift (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr2 : 2 ≤ r) :
    a (p ^ r) % (p ^ (3 * r + 3)) = a (p ^ (r - 1)) % (p ^ (3 * r + 3)) := by
  set M := p ^ (3 * r + 3)
  set N := p ^ r
  set N' := p ^ (r - 1)
  have hM_gt1 : 1 < M := one_lt_pow₀ hp.one_lt (by omega)
  have : NeZero M := ⟨by omega⟩
  have hpM_zero : (p : ZMod M) ^ (3 * r + 3) = 0 := by
    calc (p : ZMod M) ^ (3 * r + 3) = ((p ^ (3 * r + 3) : ℕ) : ZMod M) := by norm_cast
      _ = 0 := ZMod.natCast_self M
  have hp_zero_ge : ∀ e : ℕ, 3 * r + 3 ≤ e → (p : ZMod M) ^ e = 0 := by
    intro e he
    rw [show e = (3 * r + 3) + (e - (3 * r + 3)) by omega, pow_add, hpM_zero, zero_mul]
  -- Part A: Show `∑_{1 ≤ k < p^r, ¬ p ∣ k} termZ (p^r) k = 0` in `ZMod M`.
  have hPartA : ∑ k ∈ (Finset.Ico 1 N).filter (fun k => ¬ (p ∣ k)),
      (termZ N k : ZMod M) = 0 := by
    let H2M (q : ℕ) : ZMod M := ∑ c ∈ Finset.Ico 1 (q + 1), ((c : ZMod M)⁻¹) ^ 2
    have htermA : ∀ k ∈ (Finset.Ico 1 N).filter (fun k => ¬ (p ∣ k)),
        (termZ N k : ZMod M) =
          (p : ZMod M) ^ (4 * r) * ((k : ZMod M)⁻¹) ^ 4 -
            (p : ZMod M) ^ (3 * r) * ((k : ZMod M)⁻¹) ^ 3 +
            2 * (p : ZMod M) ^ (3 * r + 2) * H2M (k / N') * ((k : ZMod M)⁻¹) ^ 3 := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      -- Note `(k - 1) / N' = k / N'` since `¬ (p ∣ k)` and `p ∣ N'`.
      have hk_div_eq : (k - 1) / N' = k / N' := by
        have hp_dvd_N' : p ∣ N' := dvd_pow_self p (by omega : r - 1 ≠ 0)
        have hmod_pos : 0 < k % N' := by
          rcases Nat.eq_zero_or_pos (k % N') with h0 | hpos
          · exfalso; exact hk.2 (dvd_trans hp_dvd_N' (Nat.dvd_of_mod_eq_zero h0))
          · exact hpos
        have hdiv_mod := (Nat.div_add_mod k N').symm
        have hk_sub1 : k - 1 = (k % N' - 1) + N' * (k / N') := by omega
        have hlt_N' : k % N' - 1 < N' :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt k (Nat.pow_pos hp.pos))
        rw [hk_sub1, Nat.add_mul_div_left _ _ (Nat.pow_pos hp.pos), Nat.div_eq_of_lt hlt_N', zero_add]
      -- Integer proxy matching `numProd p r k` in `ZMod (p^3)`.
      let H2_nat : ℕ := ∑ c ∈ Finset.Ico 1 (k / N' + 1), ((c : ZMod M)⁻¹).val ^ 2
      let W_Z : ℤ := (unitProdNat p r k : ℤ) * (1 - 2 * (p : ℤ) ^ 2 * (H2_nat : ℤ))
      have hW_mod_p3 : (numProd p r k : ZMod (p ^ 3)) = (W_Z : ZMod (p ^ 3)) := by
        rw [numProd_mod_p3 hp r k (by omega) hk.1.1 (Nat.le_of_lt hk.1.2)]
        dsimp [W_Z, H2_nat]
        rw [show p ^ (r - 1) = N' from rfl, hk_div_eq]
        push_cast
        congr 3
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [Finset.mem_Ico] at hc
        have hc_lt_p : c < p := by
          have hN'_pos : 0 < N' := Nat.pow_pos hp.pos
          have hq_lt : k / N' < p := by
            rw [Nat.div_lt_iff_lt_mul hN'_pos]
            have hNp : p * N' = N := by dsimp [N', N]; rw [← Nat.pow_succ']; congr 1; omega
            rw [hNp]; exact hk.1.2
          omega
        have hcop_c : c.Coprime M :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hc.1 hc_lt_p)).symm).pow_right (3 * r + 3)
        have hdvd3M : p ^ 3 ∣ M := pow_dvd_pow p (by omega)
        rw [val_inv_cast_eq_inv hdvd3M hcop_c]
      have hC_dvd : ((p ^ (3 * r) : ℕ) : ℤ) ∣ (((p ^ r : ℕ) : ℤ) ^ 3 * (((p ^ r : ℕ) : ℤ) - (k : ℤ))) := by
        refine ⟨((p ^ r : ℕ) : ℤ) - (k : ℤ), ?_⟩
        push_cast; ring
      have hM_split : p ^ (3 * r) * p ^ 3 = M := by
        dsimp [M]; rw [← pow_add]
      have hbridge := zmod_mul_congr_of_dvd hC_dvd hW_mod_p3
      rw [hM_split] at hbridge
      have heq_M := congrArg (Int.cast : ℤ → ZMod M) (termZ_pow_eq hp.pos hk.1.1 (Nat.le_of_lt hk.1.2))
      have hrhs_eq : ((((((p ^ r : ℕ) : ℤ) ^ 3 * (((p ^ r : ℕ) : ℤ) - (k : ℤ))) * numProd p r k) : ℤ) : ZMod M) =
          ((((((p ^ r : ℕ) : ℤ) ^ 3 * (((p ^ r : ℕ) : ℤ) - (k : ℤ))) * W_Z) : ℤ) : ZMod M) := hbridge
      push_cast at heq_M hrhs_eq
      rw [hrhs_eq] at heq_M
      have hH2_cast : (H2_nat : ZMod M) = H2M (k / N') := by
        dsimp [H2_nat, H2M]; push_cast
        refine Finset.sum_congr rfl fun c _ => by rw [ZMod.natCast_zmod_val]
      have hW_cast : (W_Z : ZMod M) =
          (unitProdNat p r k : ZMod M) * (1 - 2 * (p : ZMod M) ^ 2 * H2M (k / N')) := by
        dsimp [W_Z]; push_cast; rw [hH2_cast]
      rw [hW_cast] at heq_M
      have hcop_k : k.Coprime M := ((hp.coprime_iff_not_dvd.mpr hk.2).symm).pow_right (3 * r + 3)
      have hk_inv : (k : ZMod M) * (k : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one k hcop_k
      have hcop_tot : (k ^ 4 * unitProdNat p r k).Coprime M :=
        Nat.Coprime.mul_left (hcop_k.pow_left 4) ((coprime_unitProdNat hp r k).pow_right (3 * r + 3))
      have hunit_tot : IsUnit (((k : ZMod M) ^ 4 * (unitProdNat p r k : ZMod M))) := by
        simpa using (ZMod.isUnit_iff_coprime (k ^ 4 * unitProdNat p r k) M).mpr hcop_tot
      apply hunit_tot.mul_left_cancel
      dsimp [N]
      rw [heq_M]
      set P : ZMod M := (p : ZMod M) ^ r
      have hp4 : P ^ 4 = (p : ZMod M) ^ (4 * r) := by dsimp [P]; rw [← pow_mul, mul_comm]
      have hp3 : P ^ 3 = (p : ZMod M) ^ (3 * r) := by dsimp [P]; rw [← pow_mul, mul_comm]
      have hp42 : P ^ 4 * (p : ZMod M) ^ 2 = 0 := by
        rw [hp4, ← pow_add]; exact hp_zero_ge (4 * r + 2) (by omega)
      have hp32 : P ^ 3 * (p : ZMod M) ^ 2 = (p : ZMod M) ^ (3 * r + 2) := by
        rw [hp3, ← pow_add]
      calc P ^ 3 * (P - (k : ZMod M)) *
              ((unitProdNat p r k : ZMod M) * (1 - 2 * (p : ZMod M) ^ 2 * H2M (k / N')))
          = (unitProdNat p r k : ZMod M) *
              (P ^ 4 * 1 ^ 4 -
                2 * (P ^ 4 * (p : ZMod M) ^ 2) * H2M (k / N') -
                P ^ 3 * (k : ZMod M) * 1 ^ 3 +
                2 * (P ^ 3 * (p : ZMod M) ^ 2) * H2M (k / N') * (k : ZMod M) * 1 ^ 3) := by ring
        _ = (unitProdNat p r k : ZMod M) *
              ((p : ZMod M) ^ (4 * r) * ((k : ZMod M) * (k : ZMod M)⁻¹) ^ 4 -
                0 -
                (p : ZMod M) ^ (3 * r) * (k : ZMod M) * ((k : ZMod M) * (k : ZMod M)⁻¹) ^ 3 +
                2 * (p : ZMod M) ^ (3 * r + 2) * H2M (k / N') * (k : ZMod M) *
                  ((k : ZMod M) * (k : ZMod M)⁻¹) ^ 3) := by
            rw [hp42, hp4, hp32, hp3, mul_zero, zero_mul, hk_inv]
        _ = ((k : ZMod M) ^ 4 * (unitProdNat p r k : ZMod M)) *
              ((p : ZMod M) ^ (4 * r) * ((k : ZMod M)⁻¹) ^ 4 -
                (p : ZMod M) ^ (3 * r) * ((k : ZMod M)⁻¹) ^ 3 +
                2 * (p : ZMod M) ^ (3 * r + 2) * H2M (k / N') * ((k : ZMod M)⁻¹) ^ 3) := by ring
    -- Sub-sum A1: `p^(4r) * ∑ (k⁻¹)^4 = 0` in `ZMod M`.
    set S_nondiv := (Finset.Ico 1 N).filter (fun k => ¬ (p ∣ k))
    have hA1 : (p : ZMod M) ^ (4 * r) * ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 4 = 0 := by
      let A1_nat : ℕ := ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹).val ^ 4
      have hcast : (A1_nat : ZMod M) = ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 4 := by
        dsimp [A1_nat]; push_cast
        refine Finset.sum_congr rfl fun k _ => by rw [ZMod.natCast_zmod_val]
      have hmod_p : (A1_nat : ZMod p) = 0 := by
        dsimp [A1_nat]; push_cast
        have hcongr : ∑ k ∈ S_nondiv, ((((k : ZMod M)⁻¹).val : ZMod p)) ^ 4 =
            ∑ k ∈ S_nondiv, ((k : ZMod p)⁻¹) ^ 4 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_filter] at hk
          have hcop_k : k.Coprime M := ((hp.coprime_iff_not_dvd.mpr hk.2).symm).pow_right (3 * r + 3)
          rw [val_inv_cast_eq_inv (dvd_pow_self p (by omega : 3 * r + 3 ≠ 0)) hcop_k]
        rw [hcongr]
        -- Biject `k ∈ S_nondiv` with `(b, v) ∈ range N' ×ˢ Ico 1 p` via `b * p + v`.
        have hbij : ∑ k ∈ S_nondiv, ((k : ZMod p)⁻¹) ^ 4 =
            ∑ bv ∈ Finset.range N' ×ˢ Finset.Ico 1 p, (((bv.1 * p + bv.2 : ℕ) : ZMod p)⁻¹) ^ 4 := by
          symm
          refine Finset.sum_bij (fun bv _ => bv.1 * p + bv.2) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro ⟨b, v⟩ hbv
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hbv
            rw [Finset.mem_filter, Finset.mem_Ico]
            have hNp : N' * p = N := by dsimp [N', N]; rw [← pow_succ]; congr 1; omega
            refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
            intro hd
            have hdv : p ∣ v := (Nat.dvd_add_right (dvd_mul_left p b)).mp hd
            exact Nat.not_dvd_of_pos_of_lt hbv.2.1 hbv.2.2 hdv
          · intro ⟨b₁, v₁⟩ h₁ ⟨b₂, v₂⟩ h₂ h
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at h₁ h₂
            dsimp at h₁ h₂ h
            have hmod : (b₁ * p + v₁) % p = (b₂ * p + v₂) % p := congrArg (· % p) h
            rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
              Nat.mod_eq_of_lt h₁.2.2, Nat.mod_eq_of_lt h₂.2.2] at hmod
            subst hmod
            have hbp : b₁ * p = b₂ * p := Nat.add_right_cancel h
            have hb : b₁ = b₂ := Nat.mul_right_cancel hp.pos hbp
            subst hb; rfl
          · intro k hk
            rw [Finset.mem_filter, Finset.mem_Ico] at hk
            refine ⟨(k / p, k % p), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_Ico.mpr ⟨?_, Nat.mod_lt k hp.pos⟩⟩, ?_⟩
            · rw [Nat.div_lt_iff_lt_mul hp.pos]
              have hNp : p * N' = N := by dsimp [N', N]; rw [← Nat.pow_succ']; congr 1; omega
              rw [mul_comm, hNp]; exact hk.1.2
            · rcases Nat.eq_zero_or_pos (k % p) with h0 | hpos
              · exfalso; exact hk.2 (Nat.dvd_of_mod_eq_zero h0)
              · exact hpos
            · have := Nat.div_add_mod k p
              linarith
        rw [hbij, Finset.sum_product]
        have hinner : ∀ b ∈ Finset.range N',
            ∑ v ∈ Finset.Ico 1 p, (((b * p + v : ℕ) : ZMod p)⁻¹) ^ 4 =
              ∑ v ∈ Finset.Ico 1 p, ((v : ZMod p)⁻¹) ^ 4 := by
          intro b _
          refine Finset.sum_congr rfl fun v _ => ?_
          have hbp : (((b * p + v : ℕ) : ZMod p)) = (v : ZMod p) := by
            push_cast; simp
          rw [hbp]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hN'0 : (N' : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff N' p).mpr (dvd_pow_self p (by omega : r - 1 ≠ 0))
        rw [hN'0, zero_mul]
      obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff A1_nat p).mp hmod_p
      rw [← hcast, ht]
      calc (p : ZMod M) ^ (4 * r) * ((p * t : ℕ) : ZMod M)
          = (p : ZMod M) ^ (4 * r + 1) * (t : ZMod M) := by push_cast; ring
        _ = 0 := by rw [hp_zero_ge (4 * r + 1) (by omega), zero_mul]
    -- Sub-sum A2: `p^(3r) * ∑ (k⁻¹)^3 = 0` in `ZMod M` by pairing `k` with `N - k`.
    have hA2 : (p : ZMod M) ^ (3 * r) * ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 3 = 0 := by
      set SA2 : ZMod M := (p : ZMod M) ^ (3 * r) * ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 3
      have hp_dvd_N : p ∣ N := dvd_pow_self p (by omega : r ≠ 0)
      have hrefl : ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 3 =
          ∑ k ∈ S_nondiv, (((N - k : ℕ) : ZMod M)⁻¹) ^ 3 := by
        refine Finset.sum_bij (fun k _ => N - k) ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro hd; apply hk.2
          have heq : N = (N - k) + k := by omega
          exact (Nat.dvd_add_right hd).mp (heq ▸ hp_dvd_N)
        · intro k₁ hk₁ k₂ hk₂ h
          rw [Finset.mem_filter, Finset.mem_Ico] at hk₁ hk₂; omega
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_Ico] at hk
          refine ⟨N - k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
          intro hd; apply hk.2
          have heq : N = (N - k) + k := by omega
          exact (Nat.dvd_add_right hd).mp (heq ▸ hp_dvd_N)
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_Ico] at hk
          rw [show N - (N - k) = k by omega]
      have hp5r_0 : (p : ZMod M) ^ (5 * r) = 0 := hp_zero_ge (5 * r) (by omega)
      have hN_pow : (N : ZMod M) = (p : ZMod M) ^ r := by dsimp [N]; push_cast; rfl
      have hpair : ∀ k ∈ S_nondiv,
          (p : ZMod M) ^ (3 * r) * (((k : ZMod M)⁻¹) ^ 3 + (((N - k : ℕ) : ZMod M)⁻¹) ^ 3) =
            -3 * ((p : ZMod M) ^ (4 * r) * ((k : ZMod M)⁻¹) ^ 4) := by
        intro k hk
        rw [Finset.mem_filter, Finset.mem_Ico] at hk
        set u : ZMod M := (k : ZMod M)⁻¹
        set v : ZMod M := ((N - k : ℕ) : ZMod M)⁻¹
        have hcop_k : k.Coprime M := ((hp.coprime_iff_not_dvd.mpr hk.2).symm).pow_right (3 * r + 3)
        have hndvd_Nk : ¬ (p ∣ N - k) := by
          intro hd; apply hk.2
          have heq : N = (N - k) + k := by omega
          exact (Nat.dvd_add_right hd).mp (heq ▸ hp_dvd_N)
        have hcop_Nk : (N - k).Coprime M := ((hp.coprime_iff_not_dvd.mpr hndvd_Nk).symm).pow_right (3 * r + 3)
        have hku : (k : ZMod M) * u = 1 := ZMod.coe_mul_inv_eq_one k hcop_k
        have hNkv : ((N : ZMod M) - (k : ZMod M)) * v = 1 := by
          have h : (((N - k : ℕ) : ZMod M)) * v = 1 := ZMod.coe_mul_inv_eq_one (N - k) hcop_Nk
          rwa [Nat.cast_sub (Nat.le_of_lt hk.1.2)] at h
        have hp4r_rel : (p : ZMod M) ^ (4 * r) * v = -((p : ZMod M) ^ (4 * r) * u) := by
          have h1 : (p : ZMod M) ^ (4 * r) * (((N : ZMod M) - (k : ZMod M)) * v) = (p : ZMod M) ^ (4 * r) := by
            rw [hNkv, mul_one]
          have h2 : (p : ZMod M) ^ (4 * r) * ((k : ZMod M) * v) = -(p : ZMod M) ^ (4 * r) := by
            have hexp : (p : ZMod M) ^ (4 * r) * (((p : ZMod M) ^ r - (k : ZMod M)) * v) +
                (p : ZMod M) ^ (4 * r) * ((k : ZMod M) * v) = (p : ZMod M) ^ (5 * r) * v := by ring
            rw [← hN_pow, h1, hp5r_0, zero_mul] at hexp
            linear_combination hexp
          calc (p : ZMod M) ^ (4 * r) * v
              = ((k : ZMod M) * u) * ((p : ZMod M) ^ (4 * r) * v) := by rw [hku, one_mul]
            _ = u * ((p : ZMod M) ^ (4 * r) * ((k : ZMod M) * v)) := by ring
            _ = u * (-(p : ZMod M) ^ (4 * r)) := by rw [h2]
            _ = -((p : ZMod M) ^ (4 * r) * u) := by ring
        have hp3r_sum : (p : ZMod M) ^ (3 * r) *
            ((k : ZMod M) ^ 3 + ((N : ZMod M) - (k : ZMod M)) ^ 3) =
            3 * (p : ZMod M) ^ (4 * r) * (k : ZMod M) ^ 2 := by
          rw [hN_pow]
          have hexp : (p : ZMod M) ^ (3 * r) *
              ((k : ZMod M) ^ 3 + ((p : ZMod M) ^ r - (k : ZMod M)) ^ 3) -
              3 * (p : ZMod M) ^ (4 * r) * (k : ZMod M) ^ 2 =
              (p : ZMod M) ^ (5 * r) * ((p : ZMod M) ^ r - 3 * (k : ZMod M)) := by ring
          rw [hp5r_0, zero_mul, sub_eq_zero] at hexp
          exact hexp
        calc (p : ZMod M) ^ (3 * r) * (u ^ 3 + v ^ 3)
            = (p : ZMod M) ^ (3 * r) * ((((N : ZMod M) - (k : ZMod M)) * v) ^ 3 * u ^ 3 +
                ((k : ZMod M) * u) ^ 3 * v ^ 3) := by rw [hNkv, hku]; ring
          _ = ((p : ZMod M) ^ (3 * r) * ((k : ZMod M) ^ 3 + ((N : ZMod M) - (k : ZMod M)) ^ 3)) *
                (u ^ 3 * v ^ 3) := by ring
          _ = (3 * (p : ZMod M) ^ (4 * r) * (k : ZMod M) ^ 2) * (u ^ 3 * v ^ 3) := by rw [hp3r_sum]
          _ = 3 * ((k : ZMod M) * u) ^ 2 * u * ((p : ZMod M) ^ (4 * r) * v) * v ^ 2 := by ring
          _ = 3 * 1 ^ 2 * u * (-((p : ZMod M) ^ (4 * r) * u)) * v ^ 2 := by rw [hku, hp4r_rel]
          _ = -3 * u ^ 2 * ((p : ZMod M) ^ (4 * r) * v) * v := by ring
          _ = -3 * u ^ 2 * (-((p : ZMod M) ^ (4 * r) * u)) * v := by rw [hp4r_rel]
          _ = 3 * u ^ 3 * ((p : ZMod M) ^ (4 * r) * v) := by ring
          _ = 3 * u ^ 3 * (-((p : ZMod M) ^ (4 * r) * u)) := by rw [hp4r_rel]
          _ = -3 * ((p : ZMod M) ^ (4 * r) * u ^ 4) := by ring
      have h2SA2 : (2 : ZMod M) * SA2 = 0 := by
        calc (2 : ZMod M) * SA2
            = (p : ZMod M) ^ (3 * r) * ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 3 +
                (p : ZMod M) ^ (3 * r) * ∑ k ∈ S_nondiv, (((N - k : ℕ) : ZMod M)⁻¹) ^ 3 := by
              dsimp [SA2]; rw [← hrefl]; ring
          _ = ∑ k ∈ S_nondiv,
                (p : ZMod M) ^ (3 * r) * (((k : ZMod M)⁻¹) ^ 3 + (((N - k : ℕ) : ZMod M)⁻¹) ^ 3) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun _ _ => by ring
          _ = ∑ k ∈ S_nondiv, (-3 * ((p : ZMod M) ^ (4 * r) * ((k : ZMod M)⁻¹) ^ 4)) :=
              Finset.sum_congr rfl hpair
          _ = -3 * ((p : ZMod M) ^ (4 * r) * ∑ k ∈ S_nondiv, ((k : ZMod M)⁻¹) ^ 4) := by
              rw [Finset.mul_sum, Finset.mul_sum]
          _ = 0 := by rw [hA1, mul_zero]
      have hcop2 : (2 : ℕ).Coprime M :=
        ((hp.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by decide) hd; omega)).symm).pow_right (3 * r + 3)
      have hu2 : IsUnit (2 : ZMod M) := (ZMod.isUnit_iff_coprime 2 M).mpr hcop2
      exact hu2.mul_left_cancel (h2SA2.trans (mul_zero (2 : ZMod M)).symm)
    -- Sub-sum A3: `2 * p^(3r+2) * ∑ H2M(k / N') * (k⁻¹)^3 = 0` in `ZMod M`.
    have hA3 : ∑ k ∈ S_nondiv,
        2 * (p : ZMod M) ^ (3 * r + 2) * H2M (k / N') * ((k : ZMod M)⁻¹) ^ 3 = 0 := by
      let H2_val (q : ℕ) : ℕ := (H2M q).val
      let A3_nat : ℕ := ∑ k ∈ S_nondiv, H2_val (k / N') * ((k : ZMod M)⁻¹).val ^ 3
      have hcast : (A3_nat : ZMod M) = ∑ k ∈ S_nondiv, H2M (k / N') * ((k : ZMod M)⁻¹) ^ 3 := by
        dsimp [A3_nat, H2_val]; push_cast
        refine Finset.sum_congr rfl fun k _ => by
          rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      have hmod_p : (A3_nat : ZMod p) = 0 := by
        dsimp [A3_nat]; push_cast
        have hcongr : ∑ k ∈ S_nondiv, (H2_val (k / N') : ZMod p) * ((((k : ZMod M)⁻¹).val : ZMod p)) ^ 3 =
            ∑ k ∈ S_nondiv, (H2_val (k / N') : ZMod p) * ((k : ZMod p)⁻¹) ^ 3 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_filter] at hk
          have hcop_k : k.Coprime M := ((hp.coprime_iff_not_dvd.mpr hk.2).symm).pow_right (3 * r + 3)
          rw [val_inv_cast_eq_inv (dvd_pow_self p (by omega : 3 * r + 3 ≠ 0)) hcop_k]
        rw [hcongr]
        -- Biject `k ∈ S_nondiv` with `(q, w) ∈ range p ×ˢ ((Ico 1 N').filter (¬ p ∣ ·))` via `q * N' + w`.
        set W_set := (Finset.Ico 1 N').filter (fun w => ¬ (p ∣ w))
        have hp_dvd_N' : p ∣ N' := dvd_pow_self p (by omega : r - 1 ≠ 0)
        have hbij : ∑ k ∈ S_nondiv, (H2_val (k / N') : ZMod p) * ((k : ZMod p)⁻¹) ^ 3 =
            ∑ qw ∈ Finset.range p ×ˢ W_set,
              (H2_val ((qw.1 * N' + qw.2) / N') : ZMod p) * (((qw.1 * N' + qw.2 : ℕ) : ZMod p)⁻¹) ^ 3 := by
          symm
          refine Finset.sum_bij (fun qw _ => qw.1 * N' + qw.2) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro ⟨q, w⟩ hqw
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hqw
            rw [Finset.mem_filter, Finset.mem_Ico]
            dsimp at hqw ⊢
            have hNp : p * N' = N := by dsimp [N', N]; rw [← Nat.pow_succ']; congr 1; omega
            have hlt : q * N' + w < N := by
              have hlt' : q * N' + w < p * N' := by nlinarith [hqw.1, hqw.2.1.2]
              rwa [hNp] at hlt'
            refine ⟨⟨by omega, hlt⟩, ?_⟩
            intro hd
            exact hqw.2.2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right hp_dvd_N' q)).mp hd)
          · intro ⟨q₁, w₁⟩ h₁ ⟨q₂, w₂⟩ h₂ h
            rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at h₁ h₂
            dsimp at h₁ h₂ h
            have hmod : (q₁ * N' + w₁) % N' = (q₂ * N' + w₂) % N' := congrArg (· % N') h
            rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
              Nat.mod_eq_of_lt h₁.2.1.2, Nat.mod_eq_of_lt h₂.2.1.2] at hmod
            subst hmod
            have hqN : q₁ * N' = q₂ * N' := Nat.add_right_cancel h
            have hq : q₁ = q₂ := Nat.mul_right_cancel (Nat.pow_pos hp.pos) hqN
            subst hq; rfl
          · intro k hk
            rw [Finset.mem_filter, Finset.mem_Ico] at hk
            have hN'_pos : 0 < N' := Nat.pow_pos hp.pos
            refine ⟨(k / N', k % N'), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, Nat.mod_lt k hN'_pos⟩, ?_⟩⟩, ?_⟩
            · rw [Nat.div_lt_iff_lt_mul hN'_pos]
              have hNp : p * N' = N := by dsimp [N', N]; rw [← Nat.pow_succ']; congr 1; omega
              rw [hNp]; exact hk.1.2
            · rcases Nat.eq_zero_or_pos (k % N') with h0 | hpos
              · exfalso; exact hk.2 (dvd_trans hp_dvd_N' (Nat.dvd_of_mod_eq_zero h0))
              · exact hpos
            · intro hd
              apply hk.2
              have := (Nat.div_add_mod k N').symm
              rw [this]
              exact dvd_add (dvd_mul_of_dvd_left hp_dvd_N' (k / N')) hd
            · have := Nat.div_add_mod k N'
              linarith
        rw [hbij, Finset.sum_product]
        refine Finset.sum_eq_zero fun q _ => ?_
        have hq_inner : ∑ w ∈ W_set,
            (H2_val ((q * N' + w) / N') : ZMod p) * (((q * N' + w : ℕ) : ZMod p)⁻¹) ^ 3 =
            (H2_val q : ZMod p) * ∑ w ∈ W_set, ((w : ZMod p)⁻¹) ^ 3 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [Finset.mem_filter, Finset.mem_Ico] at hw
          have hdiv_q : (q * N' + w) / N' = q := by
            rw [add_comm, mul_comm, Nat.add_mul_div_left _ _ (Nat.pow_pos hp.pos),
              Nat.div_eq_of_lt hw.1.2, zero_add]
          have hcast_w : (((q * N' + w : ℕ) : ZMod p)) = (w : ZMod p) := by
            push_cast
            have hN'0 : (N' : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N' p).mpr hp_dvd_N'
            rw [hN'0, mul_zero, zero_add]
          rw [hdiv_q, hcast_w]
        rw [hq_inner, sum_nondiv_inv_cube_zmod_p_eq_zero hp (by omega) (by omega), mul_zero]
      obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff A3_nat p).mp hmod_p
      trans (2 * (p : ZMod M) ^ (3 * r + 2) * ∑ k ∈ S_nondiv, H2M (k / N') * ((k : ZMod M)⁻¹) ^ 3)
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      · rw [← hcast, ht]
        calc 2 * (p : ZMod M) ^ (3 * r + 2) * ((p * t : ℕ) : ZMod M)
            = 2 * (p : ZMod M) ^ (3 * r + 3) * (t : ZMod M) := by push_cast; ring
          _ = 0 := by rw [hpM_zero, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl htermA, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hA1, hA2, hA3, sub_self, add_zero]
  -- Part B: Show `∑_{1 ≤ m < p^(r-1)} (termZ (p^r) (p*m) - termZ (p^(r-1)) m) = 0` in `ZMod M`.
  have hPartB : ∑ m ∈ Finset.Ico 1 N',
      ((termZ N (p * m) : ZMod M) - (termZ N' m : ZMod M)) = 0 := by
    let invSqSumM (m : ℕ) : ZMod M :=
      ∑ j ∈ (Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)), ((j : ZMod M)⁻¹) ^ 2
    have htermB : ∀ m ∈ Finset.Ico 1 N',
        (termZ N (p * m) : ZMod M) - (termZ N' m : ZMod M) =
          -2 * (p : ZMod M) ^ (2 * r) * (termZ N' m : ZMod M) * invSqSumM m := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      set M3r := p ^ (3 * r)
      have hA2 : (((p : ZMod M3r) ^ (2 * r)) ^ 2) = 0 := by
        have hM3r0 : (p : ZMod M3r) ^ (3 * r) = 0 := by
          calc (p : ZMod M3r) ^ (3 * r) = ((p ^ (3 * r) : ℕ) : ZMod M3r) := by norm_cast
            _ = 0 := ZMod.natCast_self M3r
        have hexp : 2 * (2 * r) = 3 * r + r := by omega
        calc ((p : ZMod M3r) ^ (2 * r)) ^ 2 = (p : ZMod M3r) ^ (2 * (2 * r)) := by ring
          _ = (p : ZMod M3r) ^ (3 * r) * (p : ZMod M3r) ^ r := by rw [hexp, pow_add]
          _ = 0 := by rw [hM3r0, zero_mul]
      have hcop_S : ∀ j ∈ (Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)), j.Coprime M3r := by
        intro j hj; rw [Finset.mem_filter] at hj
        exact ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_right (3 * r)
      have hV_mod := prod_sq_sub_linear_zmod ((Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)))
        ((p : ZMod M3r) ^ (2 * r)) hA2 hcop_S
      let S_pm_nat : ℕ := ∑ j ∈ (Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)),
        ((j : ZMod M)⁻¹).val ^ 2
      let WB_Z : ℤ := (U1Nat p (p * m) : ℤ) * (1 - 2 * (p : ℤ) ^ (2 * r) * (S_pm_nat : ℤ))
      have hV_eq_WB : (V1 p N (p * m) : ZMod M3r) = (WB_Z : ZMod M3r) := by
        have hV_lhs : (V1 p N (p * m) : ZMod M3r) =
            ∏ j ∈ (Finset.Ico 1 (p * m)).filter (fun j => ¬ (p ∣ j)),
              ((p : ZMod M3r) ^ (2 * r) - (j : ZMod M3r) ^ 2) ^ 2 := by
          unfold V1; dsimp [N]; push_cast
          refine Finset.prod_congr rfl fun _ _ => by ring
        rw [hV_lhs, hV_mod]
        dsimp [WB_Z, S_pm_nat]; unfold U1Nat
        push_cast
        congr 3
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_filter] at hj
        have hcop_j : j.Coprime M := ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_right (3 * r + 3)
        rw [val_inv_cast_eq_inv (pow_dvd_pow p (by omega : 3 * r ≤ 3 * r + 3)) hcop_j]
      have hdvd3_tm : ((p ^ 3 : ℕ) : ℤ) ∣ termZ N' m := by
        simpa using dvd_three_termZ_pow hp hm.1 hm.2
      have hM_split : p ^ 3 * M3r = M := by dsimp [M3r, M]; rw [← pow_add]; congr 1; omega
      have hbridge := zmod_mul_congr_of_dvd hdvd3_tm hV_eq_WB
      rw [hM_split] at hbridge
      have hNp : p * N' = N := by dsimp [N', N]; rw [← pow_succ']; congr 1; omega
      have hstep := congrArg (Int.cast : ℤ → ZMod M)
        (U1_mul_termZ_mul_p hp.pos hm.1 (Nat.le_of_lt hm.2))
      rw [hNp] at hstep
      have hrhs_eq : (((termZ N' m * V1 p N (p * m)) : ℤ) : ZMod M) =
          (((termZ N' m * WB_Z) : ℤ) : ZMod M) := hbridge
      push_cast at hstep hrhs_eq
      rw [hrhs_eq] at hstep
      have hS_cast : (S_pm_nat : ZMod M) = invSqSumM m := by
        dsimp [S_pm_nat, invSqSumM]; push_cast
        refine Finset.sum_congr rfl fun j _ => by rw [ZMod.natCast_zmod_val]
      have hWB_cast : (WB_Z : ZMod M) =
          (U1Nat p (p * m) : ZMod M) * (1 - 2 * (p : ZMod M) ^ (2 * r) * invSqSumM m) := by
        dsimp [WB_Z]; push_cast; rw [hS_cast]
      rw [hWB_cast] at hstep
      have hcop_U : (U1Nat p (p * m)).Coprime M := (coprime_U1Nat hp).pow_right (3 * r + 3)
      have hunit_U : IsUnit (U1Nat p (p * m) : ZMod M) :=
        (ZMod.isUnit_iff_coprime _ _).mpr hcop_U
      have htm_eq : (termZ N (p * m) : ZMod M) =
          (termZ N' m : ZMod M) * (1 - 2 * (p : ZMod M) ^ (2 * r) * invSqSumM m) := by
        apply hunit_U.mul_left_cancel
        rw [hstep]; ring
      rw [htm_eq]; ring
    rw [Finset.sum_congr rfl htermB]
    -- Split `m ∈ Ico 1 N'` by whether `p ^ (r - 2) ∣ m` (top slice vs lower slices).
    set P_top := p ^ (r - 2)
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 N') (fun m => P_top ∣ m)]
    -- Lower slices (`¬ P_top ∣ m`): each individual term vanishes in `ZMod M`!
    have hLower : ∑ m ∈ (Finset.Ico 1 N').filter (fun m => ¬ (P_top ∣ m)),
        (-2 * (p : ZMod M) ^ (2 * r) * (termZ N' m : ZMod M) * invSqSumM m) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter, Finset.mem_Ico] at hm
      obtain ⟨s, w, hw1, hnd, rfl⟩ := extract_pow_p hp.one_lt m hm.1.1
      have hs_lt : s < r - 2 := by
        by_contra hge
        exact hm.2 (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) w)
      have hdvd_tm := dvd_termZ_pow_general hp hw1 hnd (Nat.le_of_lt hm.1.2) (by omega)
      -- Also `p^(s+1)` divides `(invSqSumM (p^s * w)).val`.
      let S_val : ℕ := ∑ j ∈ (Finset.Ico 1 (p * (p ^ s * w))).filter (fun j => ¬ (p ∣ j)),
        ((j : ZMod M)⁻¹).val ^ 2
      have hS_cast : (S_val : ZMod M) = invSqSumM (p ^ s * w) := by
        dsimp [S_val, invSqSumM]; push_cast
        refine Finset.sum_congr rfl fun _ _ => by rw [ZMod.natCast_zmod_val]
      have hS_mod : (S_val : ZMod (p ^ (s + 1))) = 0 := by
        dsimp [S_val]; push_cast
        have hcongr : ∑ j ∈ (Finset.Ico 1 (p * (p ^ s * w))).filter (fun j => ¬ (p ∣ j)),
            ((((j : ZMod M)⁻¹).val : ZMod (p ^ (s + 1)))) ^ 2 =
            ∑ j ∈ (Finset.Ico 1 (p ^ (s + 1) * w)).filter (fun j => ¬ (p ∣ j)),
              ((j : ZMod (p ^ (s + 1)))⁻¹) ^ 2 := by
          rw [show p * (p ^ s * w) = p ^ (s + 1) * w by rw [Nat.pow_succ', mul_assoc]]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_filter] at hj
          have hcop_j : j.Coprime M := ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_right (3 * r + 3)
          rw [val_inv_cast_eq_inv (pow_dvd_pow p (by omega : s + 1 ≤ 3 * r + 3)) hcop_j]
        rw [hcongr]
        exact sum_nondiv_inv_sq_mul_pow_eq_zero hp hp5 (by omega)
      obtain ⟨q₁, hq₁⟩ := hdvd_tm
      obtain ⟨q₂, hq₂⟩ := (ZMod.natCast_eq_zero_iff S_val (p ^ (s + 1))).mp hS_mod
      rw [← hS_cast, hq₁, hq₂]
      push_cast
      have hexp : 2 * r + 3 * (r - 1 - s) + (s + 1) = 5 * r - 2 - 2 * s := by omega
      calc -2 * (p : ZMod M) ^ (2 * r) * ((p : ZMod M) ^ (3 * (r - 1 - s)) * (q₁ : ZMod M)) *
              ((p : ZMod M) ^ (s + 1) * (q₂ : ZMod M))
          = -2 * ((p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ (3 * (r - 1 - s)) *
              (p : ZMod M) ^ (s + 1)) * (q₁ : ZMod M) * (q₂ : ZMod M) := by ring
        _ = -2 * (p : ZMod M) ^ (5 * r - 2 - 2 * s) * (q₁ : ZMod M) * (q₂ : ZMod M) := by
            rw [← pow_add, ← pow_add, hexp]
        _ = 0 := by rw [hp_zero_ge (5 * r - 2 - 2 * s) (by omega)]; ring
    rw [hLower, add_zero]
    -- Top slice (`P_top ∣ m`): biject `u ∈ Ico 1 p` with `P_top * u`.
    have hTopBij : ∑ m ∈ (Finset.Ico 1 N').filter (fun m => P_top ∣ m),
        (-2 * (p : ZMod M) ^ (2 * r) * (termZ N' m : ZMod M) * invSqSumM m) =
        ∑ u ∈ Finset.Ico 1 p,
          (-2 * (p : ZMod M) ^ (2 * r) * (termZ N' (P_top * u) : ZMod M) * invSqSumM (P_top * u)) := by
      symm
      have hP_pos : 0 < P_top := Nat.pow_pos hp.pos
      have hP_mul : P_top * p = N' := by dsimp [P_top, N']; rw [← pow_succ]; congr 1; omega
      refine Finset.sum_bij (fun u _ => P_top * u) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro u hu
        rw [Finset.mem_Ico] at hu
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨Nat.mul_pos hP_pos hu.1, by rw [← hP_mul]; exact Nat.mul_lt_mul_of_pos_left hu.2 hP_pos⟩,
          dvd_mul_right P_top u⟩
      · intro u₁ _ u₂ _ h; exact Nat.mul_left_cancel hP_pos h
      · intro m hm
        rw [Finset.mem_filter, Finset.mem_Ico] at hm
        obtain ⟨⟨hm1, hmN'⟩, u, rfl⟩ := hm
        have hu_pos : 1 ≤ u := by
          rcases Nat.eq_zero_or_pos u with rfl | hpos
          · simp at hm1
          · exact hpos
        have hu_lt : u < p := by
          rw [← hP_mul] at hmN'
          exact lt_of_mul_lt_mul_left hmN' (Nat.zero_le P_top)
        exact ⟨u, Finset.mem_Ico.mpr ⟨hu_pos, hu_lt⟩, rfl⟩
    rw [hTopBij]
    -- Constant `C` from `S_base = ∑_{1 ≤ v < N', ¬ p ∣ v} ((v : ZMod (p^r))⁻¹)^2`.
    let S_base_nat : ℕ := ∑ v ∈ (Finset.Ico 1 N').filter (fun v => ¬ (p ∣ v)),
      ((v : ZMod N)⁻¹).val ^ 2
    have hS_base_mod : (S_base_nat : ZMod N') = 0 := by
      dsimp [S_base_nat]; push_cast
      have hcongr : ∑ v ∈ (Finset.Ico 1 N').filter (fun v => ¬ (p ∣ v)),
          ((((v : ZMod N)⁻¹).val : ZMod N')) ^ 2 =
          ∑ v ∈ (Finset.Ico 1 N').filter (fun v => ¬ (p ∣ v)), ((v : ZMod N')⁻¹) ^ 2 := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [Finset.mem_filter] at hv
        have : NeZero N := ⟨by positivity⟩
        have hcop_v : v.Coprime N := ((hp.coprime_iff_not_dvd.mpr hv.2).symm).pow_right r
        rw [val_inv_cast_eq_inv (pow_dvd_pow p (by omega : r - 1 ≤ r)) hcop_v]
      rw [hcongr]
      exact sum_nondiv_inv_sq_pow_eq_zero hp hp5 (by omega)
    obtain ⟨C, hC⟩ := (ZMod.natCast_eq_zero_iff S_base_nat N').mp hS_base_mod
    have hTopTerm : ∀ u ∈ Finset.Ico 1 p,
        -2 * (p : ZMod M) ^ (2 * r) * (termZ N' (P_top * u) : ZMod M) * invSqSumM (P_top * u) =
          2 * (C : ZMod M) * (p : ZMod M) ^ (3 * r + 2) * ((u : ZMod M)⁻¹) ^ 2 := by
      intro u hu
      rw [Finset.mem_Ico] at hu
      have hcop_u : u.Coprime M :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hu.1 hu.2)).symm).pow_right (3 * r + 3)
      -- 1) `termZ N' (P_top * u) = -p^3 * inv_u^3 + p^4 * E₁` over `ℤ`.
      let inv_u_nat : ℕ := ((u : ZMod M)⁻¹).val
      have htm_mod4 : (termZ N' (P_top * u) : ZMod (p ^ 4)) =
          ((-(p : ℤ) ^ 3 * (inv_u_nat : ℤ) ^ 3 : ℤ) : ZMod (p ^ 4)) := by
        have htop := top_slice_termZ_mod_p4 hp (r - 1) u (by omega) hu.1 hu.2
        have hrsub : r - 1 - 1 = r - 2 := by omega
        rw [hrsub] at htop
        rw [htop]
        push_cast
        rw [val_inv_cast_eq_inv (pow_dvd_pow p (by omega : 4 ≤ 3 * r + 3)) hcop_u]
      obtain ⟨E₁, hE₁⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ 4)).mp htm_mod4.symm
      have htm_Z : termZ N' (P_top * u) = -(p : ℤ) ^ 3 * (inv_u_nat : ℤ) ^ 3 + (p : ℤ) ^ 4 * E₁ := by
        push_cast at hE₁; linear_combination hE₁
      -- 2) `invSqSumM (P_top * u)` matches `u * N' * C + N * E₂`.
      let S_u_nat : ℕ := ∑ j ∈ (Finset.Ico 1 (p * (P_top * u))).filter (fun j => ¬ (p ∣ j)),
        ((j : ZMod M)⁻¹).val ^ 2
      have hSu_cast : (S_u_nat : ZMod M) = invSqSumM (P_top * u) := by
        dsimp [S_u_nat, invSqSumM]; push_cast
        refine Finset.sum_congr rfl fun _ _ => by rw [ZMod.natCast_zmod_val]
      have hSu_modN : ((S_u_nat : ℤ) : ZMod N) =
          (((u : ℤ) * (N' : ℤ) * (C : ℤ) : ℤ) : ZMod N) := by
        push_cast
        have hpP : p * (P_top * u) = p ^ (r - 1) * u := by
          dsimp [P_top]
          rw [← mul_assoc, ← Nat.pow_succ']
          congr 1; congr 1; omega
        have hSu_val : (S_u_nat : ZMod (p ^ r)) =
            ∑ j ∈ (Finset.Ico 1 (p * (P_top * u))).filter (fun j => ¬ (p ∣ j)),
              ((((j : ZMod M)⁻¹).val : ZMod (p ^ r))) ^ 2 := by
          dsimp [S_u_nat]; push_cast; rfl
        have hcongr : ∑ j ∈ (Finset.Ico 1 (p * (P_top * u))).filter (fun j => ¬ (p ∣ j)),
            ((((j : ZMod M)⁻¹).val : ZMod (p ^ r))) ^ 2 =
            ∑ j ∈ (Finset.Ico 1 (p ^ (r - 1) * u)).filter (fun j => ¬ (p ∣ j)), ((j : ZMod (p ^ r))⁻¹) ^ 2 := by
          rw [hpP]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_filter] at hj
          have hcop_j : j.Coprime M := ((hp.coprime_iff_not_dvd.mpr hj.2).symm).pow_right (3 * r + 3)
          rw [val_inv_cast_eq_inv (pow_dvd_pow p (by omega : r ≤ 3 * r + 3)) hcop_j]
        have : NeZero (p ^ r) := ⟨by positivity⟩
        have hbase_cast : (S_base_nat : ZMod (p ^ r)) =
            ∑ v ∈ (Finset.Ico 1 (p ^ (r - 1))).filter (fun v => ¬ (p ∣ v)), ((v : ZMod (p ^ r))⁻¹) ^ 2 := by
          dsimp [S_base_nat, N']; push_cast
          refine Finset.sum_congr rfl fun _ _ => by rw [ZMod.natCast_zmod_val]
        dsimp [N]
        rw [hSu_val, hcongr, sum_nondiv_inv_sq_top_slice hp (by omega) hr2, ← hbase_cast, hC]
        push_cast; ring
      obtain ⟨E₂, hE₂⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hSu_modN.symm
      have hSu_Z : (S_u_nat : ℤ) = (u : ℤ) * (N' : ℤ) * (C : ℤ) + (N : ℤ) * E₂ := by
        linear_combination hE₂
      have hSu_M : invSqSumM (P_top * u) = ((S_u_nat : ℤ) : ZMod M) := by
        simpa using hSu_cast.symm
      rw [hSu_M, htm_Z, hSu_Z]
      push_cast
      have hinv_u_cast : (inv_u_nat : ZMod M) = (u : ZMod M)⁻¹ := ZMod.natCast_zmod_val _
      have hu_mul_inv : (u : ZMod M) * (u : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one u hcop_u
      have hN'_pow : (N' : ZMod M) = (p : ZMod M) ^ (r - 1) := by dsimp [N']; push_cast; rfl
      have hN_pow : (N : ZMod M) = (p : ZMod M) ^ r := by dsimp [N]; push_cast; rfl
      rw [hinv_u_cast, hN'_pow, hN_pow]
      have hp_main : (p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 3 * (p : ZMod M) ^ (r - 1) =
          (p : ZMod M) ^ (3 * r + 2) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have hp_err1 : (p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 4 * (p : ZMod M) ^ (r - 1) = 0 := by
        rw [← pow_add, ← pow_add, show 2 * r + 4 + (r - 1) = 3 * r + 3 by omega, hpM_zero]
      have hp_err2 : (p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 3 * (p : ZMod M) ^ r = 0 := by
        rw [← pow_add, ← pow_add, show 2 * r + 3 + r = 3 * r + 3 by omega, hpM_zero]
      have hp_err3 : (p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 4 * (p : ZMod M) ^ r = 0 := by
        rw [← pow_add, ← pow_add]; exact hp_zero_ge (2 * r + 4 + r) (by omega)
      calc -2 * (p : ZMod M) ^ (2 * r) *
              (-(p : ZMod M) ^ 3 * ((u : ZMod M)⁻¹) ^ 3 + (p : ZMod M) ^ 4 * (E₁ : ZMod M)) *
              ((u : ZMod M) * (p : ZMod M) ^ (r - 1) * (C : ZMod M) + (p : ZMod M) ^ r * (E₂ : ZMod M))
          = 2 * (C : ZMod M) * ((p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 3 * (p : ZMod M) ^ (r - 1)) *
              ((u : ZMod M) * (u : ZMod M)⁻¹) * ((u : ZMod M)⁻¹) ^ 2 +
            2 * ((p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 3 * (p : ZMod M) ^ r) *
              ((u : ZMod M)⁻¹) ^ 3 * (E₂ : ZMod M) -
            2 * ((p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 4 * (p : ZMod M) ^ (r - 1)) *
              (E₁ : ZMod M) * (u : ZMod M) * (C : ZMod M) -
            2 * ((p : ZMod M) ^ (2 * r) * (p : ZMod M) ^ 4 * (p : ZMod M) ^ r) *
              (E₁ : ZMod M) * (E₂ : ZMod M) := by ring
        _ = 2 * (C : ZMod M) * (p : ZMod M) ^ (3 * r + 2) * ((u : ZMod M)⁻¹) ^ 2 := by
            rw [hp_main, hu_mul_inv, hp_err1, hp_err2, hp_err3]; ring
    rw [Finset.sum_congr rfl hTopTerm]
    -- Show `p^(3r+2) * ∑_{1 ≤ u < p} (u⁻¹)^2 = 0` in `ZMod M` via `ZMod p`.
    let S2_nat : ℕ := ∑ u ∈ Finset.Ico 1 p, ((u : ZMod M)⁻¹).val ^ 2
    have hS2_cast : (S2_nat : ZMod M) = ∑ u ∈ Finset.Ico 1 p, ((u : ZMod M)⁻¹) ^ 2 := by
      dsimp [S2_nat]; push_cast
      refine Finset.sum_congr rfl fun _ _ => by rw [ZMod.natCast_zmod_val]
    have hS2_mod_p : (S2_nat : ZMod p) = 0 := by
      dsimp [S2_nat]; push_cast
      have hcongr : ∑ u ∈ Finset.Ico 1 p, ((((u : ZMod M)⁻¹).val : ZMod p)) ^ 2 =
          ∑ u ∈ Finset.Ico 1 p, ((u : ZMod p)⁻¹) ^ 2 := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.mem_Ico] at hu
        have hcop_u : u.Coprime M :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hu.1 hu.2)).symm).pow_right (3 * r + 3)
        rw [val_inv_cast_eq_inv (dvd_pow_self p (by omega : 3 * r + 3 ≠ 0)) hcop_u]
      rw [hcongr]
      apply sum_inv_pow_zmod_eq_zero hp (by omega) (by decide)
      intro hdvd
      have := Nat.le_of_dvd (by decide : 0 < 2 ^ 2 - 1) hdvd
      omega
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff S2_nat p).mp hS2_mod_p
    rw [← Finset.mul_sum, ← hS2_cast, hq]
    calc 2 * (C : ZMod M) * (p : ZMod M) ^ (3 * r + 2) * ((p * q : ℕ) : ZMod M)
        = 2 * (C : ZMod M) * (p : ZMod M) ^ (3 * r + 3) * (q : ZMod M) := by push_cast; ring
      _ = 0 := by rw [hpM_zero]; ring
  -- Final assembly: compare `a N` and `a N'` in `ZMod M`.
  have ha_eq : ∀ n : ℕ, 1 ≤ n → (a n : ZMod M) = 1 + ∑ k ∈ Finset.Ico 1 n, (termZ n k : ZMod M) := by
    intro n hn
    unfold a
    rw [if_neg (by omega : n ≠ 0)]
    have hrange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    push_cast
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun k _ => by unfold termZ; push_cast; rfl
  have haN := ha_eq N (Nat.pow_pos hp.pos)
  have haN' := ha_eq N' (Nat.pow_pos hp.pos)
  have hsplitN : ∑ k ∈ Finset.Ico 1 N, (termZ N k : ZMod M) =
      (∑ m ∈ Finset.Ico 1 N', (termZ N (p * m) : ZMod M)) +
        ∑ k ∈ (Finset.Ico 1 N).filter (fun k => ¬ (p ∣ k)), (termZ N k : ZMod M) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 N) (fun k => p ∣ k)]
    congr 1
    symm
    have hNp : p * N' = N := by dsimp [N', N]; rw [← pow_succ']; congr 1; omega
    refine Finset.sum_bij (fun m _ => p * m) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro m hm
      rw [Finset.mem_Ico] at hm
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.mul_pos hp.pos hm.1, by rw [← hNp]; exact Nat.mul_lt_mul_of_pos_left hm.2 hp.pos⟩,
        dvd_mul_right p m⟩
    · intro m₁ _ m₂ _ h; exact Nat.mul_left_cancel hp.pos h
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      obtain ⟨⟨hk1, hkN⟩, m, rfl⟩ := hk
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hk1
        · exact hpos
      have hm_lt : m < N' := by
        rw [← hNp] at hkN
        exact lt_of_mul_lt_mul_left hkN (Nat.zero_le p)
      exact ⟨m, Finset.mem_Ico.mpr ⟨hm1, hm_lt⟩, rfl⟩
  have hcast_eq : ((a N : ℕ) : ZMod M) = ((a N' : ℕ) : ZMod M) := by
    have hdiff : (a N : ZMod M) - (a N' : ZMod M) = 0 := by
      rw [haN, haN', hsplitN, hPartA, add_zero]
      calc (1 + ∑ m ∈ Finset.Ico 1 N', (termZ N (p * m) : ZMod M)) -
              (1 + ∑ m ∈ Finset.Ico 1 N', (termZ N' m : ZMod M))
          = ∑ m ∈ Finset.Ico 1 N', (termZ N (p * m) : ZMod M) -
              ∑ m ∈ Finset.Ico 1 N', (termZ N' m : ZMod M) := by ring
        _ = ∑ m ∈ Finset.Ico 1 N', ((termZ N (p * m) : ZMod M) - (termZ N' m : ZMod M)) :=
            (Finset.sum_sub_distrib _ _).symm
        _ = 0 := hPartB
    exact sub_eq_zero.mp hdiff
  exact (ZMod.natCast_eq_natCast_iff' (a N) (a N') M).mp hcast_eq

end OMA.PrimePowerLift

theorem OMA.solution : type_of% @OeisA212334.conjecture_2 := by
  exact OMA.PrimePowerLift.prime_power_lift

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
