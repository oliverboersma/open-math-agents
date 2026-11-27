import FormalConjectures.OEIS.«208425»

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Varun Dudipala.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
Port of the proof published by Varun Dudipala in sun-conjectures-lean,
commit 9b5e21fea12a7061cfd553ed340fdc029bec74bc, file
SunConjectures/A208425/Solution.lean (Apache-2.0). The original project
credits Gemini 4 Carbon for the proof and Claude for its independent check.
This version uses the sequence and the exact target from Formal Conjectures.
The conditional rewrites follow the original November 18 source at commit
3241c0eb195e3a721af082facc886957b41f44f4 for compatibility with Lean 4.33.1.
-/

namespace Solutions.OeisA208425_3

open scoped BigOperators
open Polynomial
open _root_.OeisA208425

/- Part 1: Binomial & Hockey-Stick Reduction -/

lemma choose_triple_eq (j k : ℕ) :
    j.choose k * (j - k).choose k * (j + k).choose k =
      (3 * k).choose k * (2 * k).choose k * (j + k).choose (3 * k) := by
  by_cases h : j < 2 * k
  · have h1 : (j - k).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (j + k).choose (3 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    ring
  · replace h : 2 * k ≤ j := by omega
    set F := k.factorial * k.factorial * k.factorial * (j - 2 * k).factorial
    have hF : 0 < F := by positivity
    apply Nat.mul_right_cancel hF
    have f1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ j by omega)
    have f2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ j - k by omega)
    have f3 := Nat.choose_mul_factorial_mul_factorial (show k ≤ j + k by omega)
    have f4 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
    have f5 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have f6 := Nat.choose_mul_factorial_mul_factorial (show 3 * k ≤ j + k by omega)
    rw [show j - k - k = j - 2 * k by omega] at f2
    rw [show j + k - k = j by omega] at f3
    rw [show 3 * k - k = 2 * k by omega] at f4
    rw [show 2 * k - k = k by omega] at f5
    rw [show j + k - 3 * k = j - 2 * k by omega] at f6
    calc
      j.choose k * (j - k).choose k * (j + k).choose k * F
          = (j + k).choose k * k.factorial *
              (j.choose k * k.factorial * ((j - k).choose k * k.factorial * (j - 2 * k).factorial)) := by
              dsimp [F]; ring
      _ = (j + k).choose k * k.factorial * (j.choose k * k.factorial * (j - k).factorial) := by
              rw [f2]
      _ = (j + k).choose k * k.factorial * j.factorial := by rw [f1]
      _ = (j + k).factorial := f3
      _ = (j + k).choose (3 * k) * (3 * k).factorial * (j - 2 * k).factorial := f6.symm
      _ = (j + k).choose (3 * k) * ((3 * k).choose k * k.factorial * (2 * k).factorial) *
            (j - 2 * k).factorial := by rw [← f4]
      _ = (j + k).choose (3 * k) *
            ((3 * k).choose k * k.factorial * ((2 * k).choose k * k.factorial * k.factorial)) *
            (j - 2 * k).factorial := by rw [← f5]
      _ = (3 * k).choose k * (2 * k).choose k * (j + k).choose (3 * k) * F := by
            dsimp [F]; ring

lemma sum_choose_shift (k : ℕ) :
    ∀ p : ℕ, 0 < p → ∑ j ∈ Finset.range p, (j + k).choose (3 * k) = (p + k).choose (3 * k + 1)
  | 0, hp => by omega
  | 1, _ => by
    simp only [Finset.sum_range_one, zero_add]
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
  | p + 2, _ => by
    rw [Finset.sum_range_succ, sum_choose_shift k (p + 1) (by omega)]
    rw [show p + 2 + k = (p + 1 + k) + 1 by omega, Nat.choose_succ_succ, add_comm]

def TTerm (p k : ℕ) : ℕ :=
  (3 * k).choose k * (2 * k).choose k * (p + k).choose (3 * k + 1)

lemma sum_a_eq_sum_TTerm {p m : ℕ} (hp : p = 2 * m + 1) :
    ∑ j ∈ Finset.range p, a j = ∑ k ∈ Finset.range (m + 1), TTerm p k := by
  have hp_pos : 0 < p := by omega
  have ha_ext : ∀ j ∈ Finset.range p,
      a j = ∑ k ∈ Finset.range p,
        (3 * k).choose k * (2 * k).choose k * (j + k).choose (3 * k) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold a
    have hsplit : Finset.range p = Finset.range (j + 1) ∪ Finset.Ico (j + 1) p := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    conv_rhs => rw [hsplit, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2; omega)]
    have hzero : ∑ k ∈ Finset.Ico (j + 1) p,
        (3 * k).choose k * (2 * k).choose k * (j + k).choose (3 * k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      rw [Nat.choose_eq_zero_of_lt (show j + k < 3 * k by omega), mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun k _ => choose_triple_eq j k
  rw [Finset.sum_congr rfl ha_ext, Finset.sum_comm]
  have hstep : ∀ k ∈ Finset.range p,
      (∑ j ∈ Finset.range p, (3 * k).choose k * (2 * k).choose k * (j + k).choose (3 * k)) =
        TTerm p k := by
    intro k _
    rw [← Finset.mul_sum, sum_choose_shift k p hp_pos]
    rfl
  rw [Finset.sum_congr rfl hstep]
  have hsplit2 : Finset.range p = Finset.range (m + 1) ∪ Finset.Ico (m + 1) p := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [hsplit2, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2; omega)]
  have hzero2 : ∑ k ∈ Finset.Ico (m + 1) p, TTerm p k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    unfold TTerm
    rw [Nat.choose_eq_zero_of_lt (show p + k < 3 * k + 1 by omega), mul_zero]
  rw [hzero2, add_zero]

/- Part 2: Factorial Cancellation and Division by `p` -/

lemma factorial_add_eq_prod (p : ℕ) (hp : 0 < p) :
    ∀ k : ℕ, (p + k).factorial =
      (∏ i ∈ Finset.range k, (p + 1 + i)) * p * (p - 1).factorial
  | 0 => by
    simp only [add_zero, Finset.prod_range_zero, one_mul]
    exact (Nat.mul_factorial_pred (by omega)).symm
  | k + 1 => by
    rw [show p + (k + 1) = (p + k) + 1 by omega, Nat.factorial_succ,
      factorial_add_eq_prod p hp k, Finset.prod_range_succ]
    ring

lemma TTerm_factorial_eq {p k : ℕ} (hkp : 2 * k + 1 ≤ p) :
    (3 * k + 1) * k.factorial * TTerm p k =
      p * (2 * k).choose k * (p - 1).choose (2 * k) * (∏ i ∈ Finset.range k, (p + 1 + i)) := by
  set F := k.factorial * k.factorial * (p - 1 - 2 * k).factorial
  have hF : 0 < F := by positivity
  apply Nat.mul_right_cancel hF
  have f1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 3 * k by omega)
  have f2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  have f3 := Nat.choose_mul_factorial_mul_factorial (show 3 * k + 1 ≤ p + k by omega)
  have f4 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ p - 1 by omega)
  rw [show 3 * k - k = 2 * k by omega] at f1
  rw [show 2 * k - k = k by omega] at f2
  rw [show p + k - (3 * k + 1) = p - 1 - 2 * k by omega] at f3
  have h3k1 : (3 * k + 1) * (3 * k).factorial = (3 * k + 1).factorial :=
    Nat.factorial_succ (3 * k)
  unfold TTerm
  calc
    (3 * k + 1) * k.factorial * ((3 * k).choose k * (2 * k).choose k * (p + k).choose (3 * k + 1)) * F
        = (p + k).choose (3 * k + 1) *
            ((3 * k + 1) * ((3 * k).choose k * k.factorial *
              ((2 * k).choose k * k.factorial * k.factorial))) *
            (p - 1 - 2 * k).factorial := by dsimp [F]; ring
    _ = (p + k).choose (3 * k + 1) * ((3 * k + 1) * ((3 * k).choose k * k.factorial * (2 * k).factorial)) *
          (p - 1 - 2 * k).factorial := by rw [f2]
    _ = (p + k).choose (3 * k + 1) * ((3 * k + 1) * (3 * k).factorial) *
          (p - 1 - 2 * k).factorial := by rw [f1]
    _ = (p + k).choose (3 * k + 1) * (3 * k + 1).factorial * (p - 1 - 2 * k).factorial := by
          rw [h3k1]
    _ = (p + k).factorial := f3
    _ = (∏ i ∈ Finset.range k, (p + 1 + i)) * p * (p - 1).factorial :=
          factorial_add_eq_prod p (by omega) k
    _ = (∏ i ∈ Finset.range k, (p + 1 + i)) * p *
          ((p - 1).choose (2 * k) * (2 * k).factorial * (p - 1 - 2 * k).factorial) := by
          rw [← f4]
    _ = (∏ i ∈ Finset.range k, (p + 1 + i)) * p *
          ((p - 1).choose (2 * k) * ((2 * k).choose k * k.factorial * k.factorial) *
            (p - 1 - 2 * k).factorial) := by rw [← f2]
    _ = p * (2 * k).choose k * (p - 1).choose (2 * k) * (∏ i ∈ Finset.range k, (p + 1 + i)) * F := by
          dsimp [F]; ring

lemma choose_pred_prime_cast {p : ℕ} [hp : Fact p.Prime] :
    ∀ j : ℕ, j < p → ((p - 1).choose j : ZMod p) = (-1 : ZMod p) ^ j
  | 0, _ => by simp
  | j + 1, hj => by
    have hp_pos : 0 < p := hp.out.pos
    have hmul : (j + 1) * (p - 1).choose (j + 1) = (p - 1 - j) * (p - 1).choose j := by
      have f1 := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ p - 1 by omega)
      have f2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ p - 1 by omega)
      have hsub : p - 1 - j = (p - 1 - (j + 1)) + 1 := by omega
      have hf_step : (p - 1 - j).factorial = (p - 1 - j) * (p - 1 - (j + 1)).factorial := by
        rw [hsub, Nat.factorial_succ, ← hsub]
      rw [hf_step] at f2
      rw [Nat.factorial_succ] at f1
      have hpos : 0 < j.factorial * (p - 1 - (j + 1)).factorial := by positivity
      apply Nat.mul_right_cancel hpos
      calc
        (j + 1) * (p - 1).choose (j + 1) * (j.factorial * (p - 1 - (j + 1)).factorial)
            = (p - 1).choose (j + 1) * ((j + 1) * j.factorial) * (p - 1 - (j + 1)).factorial := by
                ring
        _ = (p - 1).factorial := f1
        _ = (p - 1).choose j * j.factorial * ((p - 1 - j) * (p - 1 - (j + 1)).factorial) := f2.symm
        _ = (p - 1 - j) * (p - 1).choose j * (j.factorial * (p - 1 - (j + 1)).factorial) := by ring
    have hcast : ((j + 1 : ℕ) : ZMod p) * ((p - 1).choose (j + 1) : ZMod p) =
        ((p - 1 - j : ℕ) : ZMod p) * ((p - 1).choose j : ZMod p) := by
      have := congrArg (fun x : ℕ => (x : ZMod p)) hmul
      simpa only [Nat.cast_mul] using this
    have hj_ne : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hsub_cast : ((p - 1 - j : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
      have hsum : (p - 1 - j) + (j + 1) = p := by omega
      have hsum_cast : ((p - 1 - j : ℕ) : ZMod p) + ((j + 1 : ℕ) : ZMod p) = (p : ZMod p) := by
        have := congrArg (fun x : ℕ => (x : ZMod p)) hsum
        simpa only [Nat.cast_add] using this
      rw [ZMod.natCast_self] at hsum_cast
      exact eq_neg_of_add_eq_zero_left hsum_cast
    rw [hsub_cast, choose_pred_prime_cast j (by omega)] at hcast
    apply mul_left_cancel₀ hj_ne
    calc
      ((j + 1 : ℕ) : ZMod p) * ((p - 1).choose (j + 1) : ZMod p)
          = -((j + 1 : ℕ) : ZMod p) * (-1 : ZMod p) ^ j := hcast
      _ = ((j + 1 : ℕ) : ZMod p) * (-1 : ZMod p) ^ (j + 1) := by rw [pow_succ]; ring

lemma not_dvd_three_mul_add_one {p k : ℕ} (hp2 : p % 3 = 2) (hkp : 2 * k + 1 ≤ p) :
    ¬ (p ∣ 3 * k + 1) := by
  rintro ⟨q, hq⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · omega
  · rcases eq_or_ne q 1 with rfl | hq1
    · omega
    · have : p * 2 ≤ p * q := Nat.mul_le_mul_left p (by omega : 2 ≤ q)
      omega

lemma dvd_TTerm_and_div_cast {p k : ℕ} [hp : Fact p.Prime] (hp2 : p % 3 = 2)
    (hkp : 2 * k + 1 ≤ p) :
    p ∣ TTerm p k ∧
      ((3 * (k : ZMod p) + 1) * ((TTerm p k / p : ℕ) : ZMod p)) = ((2 * k).choose k : ZMod p) := by
  have hf := TTerm_factorial_eq hkp
  have hdvd_prod : p ∣ (3 * k + 1) * k.factorial * TTerm p k :=
    ⟨(2 * k).choose k * (p - 1).choose (2 * k) * (∏ i ∈ Finset.range k, (p + 1 + i)),
      by linarith⟩
  have hnot1 : ¬ (p ∣ 3 * k + 1) := not_dvd_three_mul_add_one hp2 hkp
  have hnot2 : ¬ (p ∣ k.factorial) := by
    rw [hp.out.dvd_factorial]
    omega
  have hdvd_T : p ∣ TTerm p k := by
    rcases hp.out.dvd_mul.mp hdvd_prod with h12 | hT
    · rcases hp.out.dvd_mul.mp h12 with h1 | h2
      · exact absurd h1 hnot1
      · exact absurd h2 hnot2
    · exact hT
  refine ⟨hdvd_T, ?_⟩
  obtain ⟨q, hq⟩ := hdvd_T
  have hq_div : TTerm p k / p = q := by
    rw [hq, Nat.mul_div_right _ hp.out.pos]
  rw [hq_div]
  rw [hq] at hf
  have hf' : (3 * k + 1) * k.factorial * q =
      (2 * k).choose k * (p - 1).choose (2 * k) * (∏ i ∈ Finset.range k, (p + 1 + i)) := by
    apply Nat.mul_left_cancel hp.out.pos
    linarith
  have hcast : (((3 * k + 1 : ℕ) : ZMod p) * (k.factorial : ZMod p) * (q : ZMod p)) =
      ((2 * k).choose k : ZMod p) * ((p - 1).choose (2 * k) : ZMod p) *
        (∏ i ∈ Finset.range k, ((p + 1 + i : ℕ) : ZMod p)) := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hf'
    simpa only [Nat.cast_mul, Nat.cast_prod] using this
  have hprod_cast : (∏ i ∈ Finset.range k, ((p + 1 + i : ℕ) : ZMod p)) =
      (k.factorial : ZMod p) := by
    clear hf hf' hcast hq hq_div hdvd_prod hnot1 hnot2 hp2 hkp
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      rw [ZMod.natCast_self, zero_add]
      ring
  have hch_cast : ((p - 1).choose (2 * k) : ZMod p) = 1 := by
    rw [choose_pred_prime_cast (2 * k) (by omega), pow_mul, neg_one_sq, one_pow]
  rw [hprod_cast, hch_cast, mul_one] at hcast
  have hkf_ne : (k.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hnot2
  apply mul_right_cancel₀ hkf_ne
  push_cast at hcast ⊢
  linear_combination hcast

/- Part 3: Central Binomial Partial Sum Mod `p` -/

def chiZ (r : ℤ) : ℤ :=
  if r % 3 = 0 then 1 else if r % 3 = 1 then -1 else 0

def psiZ (r : ℤ) : ℤ :=
  if r % 6 = 0 ∨ r % 6 = 1 then 1 else if r % 6 = 3 ∨ r % 6 = 4 then -1 else 0

lemma chiZ_sum3 (r : ℤ) : chiZ (r + 1) + chiZ r + chiZ (r - 1) = 0 := by
  unfold chiZ; split_ifs <;> omega

lemma psiZ_rec (r : ℤ) : psiZ (r + 1) = psiZ r - psiZ (r - 1) := by
  unfold psiZ; split_ifs <;> omega

def chooseZ (n : ℕ) (k : ℤ) : ℤ :=
  if 0 ≤ k then (n.choose k.toNat : ℤ) else 0

lemma chooseZ_succ (n : ℕ) (k : ℤ) :
    chooseZ (n + 1) k = chooseZ n k + chooseZ n (k - 1) := by
  by_cases hk0 : k < 0
  · unfold chooseZ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · by_cases hk1 : k = 0
    · subst hk1
      unfold chooseZ
      simp
    · lift k to ℕ using (by omega)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      unfold chooseZ
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      have t1 : ((m + 1 : ℕ) : ℤ).toNat = m + 1 := by omega
      have t2 : (((m + 1 : ℕ) : ℤ) - 1).toNat = m := by omega
      rw [t1, t2, Nat.choose_succ_succ]
      push_cast
      ring

lemma chooseZ_succ2 (n : ℕ) (k : ℤ) :
    chooseZ (n + 2) k = chooseZ n k + 2 * chooseZ n (k - 1) + chooseZ n (k - 2) := by
  rw [show n + 2 = (n + 1) + 1 by omega, chooseZ_succ, chooseZ_succ n k, chooseZ_succ n (k - 1),
    show k - 1 - 1 = k - 2 by ring]
  ring

def seqA (M : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (M + 1), chiZ ((M : ℤ) - j) * ((2 * M + 2).choose j : ℤ)

lemma seqA_eq_sum_central :
    ∀ M : ℕ, seqA M = ∑ k ∈ Finset.range (M + 1), ((2 * k).choose k : ℤ)
  | 0 => by decide
  | M + 1 => by
    rw [Finset.sum_range_succ, ← seqA_eq_sum_central M]
    have hA1 : seqA (M + 1) =
        ∑ j ∈ Finset.range (M + 2), chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 4) j := by
      unfold seqA chooseZ
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_pos (by omega), Int.toNat_natCast, show 2 * (M + 1) + 2 = 2 * M + 4 by omega]
      push_cast; rfl
    have hA0 : seqA M =
        ∑ j ∈ Finset.range (M + 1), chiZ ((M : ℤ) - j) * chooseZ (2 * M + 2) j := by
      unfold seqA chooseZ
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_pos (by omega), Int.toNat_natCast]
    rw [hA1, hA0]
    have hexp : ∀ j ∈ Finset.range (M + 2),
        chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 4) j =
          chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) j +
          2 * chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) ((j : ℤ) - 1) +
          chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) ((j : ℤ) - 2) := by
      intro j _
      rw [show 2 * M + 4 = (2 * M + 2) + 2 by omega, chooseZ_succ2]
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hs1 : ∑ j ∈ Finset.range (M + 2), chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) j =
        (∑ j ∈ Finset.range (M + 1), chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) j) +
          ((2 * (M + 1)).choose (M + 1) : ℤ) := by
      rw [Finset.sum_range_succ]
      congr 1
      have hc0 : chiZ ((M + 1 : ℤ) - (M + 1 : ℕ)) = 1 := by
        push_cast; rw [sub_self]; decide
      rw [hc0, one_mul]
      unfold chooseZ
      rw [if_pos (by omega), Int.toNat_natCast, show 2 * M + 2 = 2 * (M + 1) by omega]
    have hs2 : ∑ j ∈ Finset.range (M + 2),
        2 * chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) ((j : ℤ) - 1) =
        ∑ j ∈ Finset.range (M + 1), 2 * chiZ ((M : ℤ) - j) * chooseZ (2 * M + 2) j := by
      rw [Finset.sum_range_succ']
      have hz : chooseZ (2 * M + 2) ((0 : ℕ) - 1) = 0 := by unfold chooseZ; simp
      rw [hz, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      rw [show (M : ℤ) + 1 - ((j : ℤ) + 1) = (M : ℤ) - j by ring, add_sub_cancel_right]
    have hs3 : ∑ j ∈ Finset.range (M + 2),
        chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) ((j : ℤ) - 2) =
        ∑ j ∈ Finset.range (M + 1), chiZ ((M - 1 : ℤ) - j) * chooseZ (2 * M + 2) j := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz0 : chooseZ (2 * M + 2) ((0 : ℕ) - 2) = 0 := by unfold chooseZ; simp
      have hz1 : chooseZ (2 * M + 2) (((0 : ℕ) + 1 : ℕ) - 2) = 0 := by unfold chooseZ; simp
      rw [hz0, hz1, mul_zero, mul_zero, add_zero, add_zero]
      conv_rhs => rw [Finset.sum_range_succ]
      have htop : chiZ ((M - 1 : ℤ) - M) * chooseZ (2 * M + 2) M = 0 := by
        have : chiZ ((M - 1 : ℤ) - M) = 0 := by
          rw [show (M - 1 : ℤ) - M = -1 by ring]
          decide
        rw [this, zero_mul]
      rw [htop, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      rw [show (M : ℤ) + 1 - ((j : ℤ) + 1 + 1) = (M : ℤ) - 1 - j by ring,
        show (j : ℤ) + 1 + 1 - 2 = j by ring]
    rw [hs1, hs2, hs3]
    have hcomb : (∑ j ∈ Finset.range (M + 1), chiZ ((M + 1 : ℤ) - j) * chooseZ (2 * M + 2) j) +
        (∑ j ∈ Finset.range (M + 1), 2 * chiZ ((M : ℤ) - j) * chooseZ (2 * M + 2) j) +
        (∑ j ∈ Finset.range (M + 1), chiZ ((M - 1 : ℤ) - j) * chooseZ (2 * M + 2) j) =
        ∑ j ∈ Finset.range (M + 1), chiZ ((M : ℤ) - j) * chooseZ (2 * M + 2) j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hc := chiZ_sum3 ((M : ℤ) - j)
      rw [show (M : ℤ) - j + 1 = (M + 1 : ℤ) - j by ring,
        show (M : ℤ) - j - 1 = (M - 1 : ℤ) - j by ring] at hc
      linear_combination chooseZ (2 * M + 2) j * hc
    linarith

def seqB' (m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 2), psiZ ((m + 1 : ℤ) - j) * ((m + j).choose j : ℤ)

lemma two_mul_seqB'_eq :
    ∀ m : ℕ, 2 * seqB' m = seqA (m + 1) + 1
  | 0 => by decide
  | m + 1 => by
    have ih := two_mul_seqB'_eq m
    have hstep : seqB' (m + 1) - seqB' m = ((2 * m + 3).choose (m + 2) : ℤ) := by
      unfold seqB'
      rw [show m + 1 + 2 = m + 3 by omega]
      push_cast
      have hrec : ∀ j ∈ Finset.range (m + 3),
          psiZ ((m : ℤ) + 1 + 1 - j) * ((m + 1 + j).choose j : ℤ) =
            psiZ ((m : ℤ) + 1 - j) * ((m + 1 + j).choose j : ℤ) -
            psiZ ((m : ℤ) - j) * ((m + 1 + j).choose j : ℤ) := by
        intro j _
        have hp := psiZ_rec ((m : ℤ) + 1 - j)
        rw [show (m : ℤ) + 1 - j + 1 = (m : ℤ) + 1 + 1 - j by ring,
          show (m : ℤ) + 1 - j - 1 = (m : ℤ) - j by ring] at hp
        rw [hp]; ring
      rw [Finset.sum_congr rfl hrec, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ' (fun j => psiZ ((m : ℤ) + 1 - j) * ((m + 1 + j).choose j : ℤ))]
      simp only [Nat.cast_zero, sub_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have hpascal : ∀ j ∈ Finset.range (m + 2),
          psiZ ((m : ℤ) + 1 - ((j + 1 : ℕ) : ℤ)) * ((m + 1 + (j + 1)).choose (j + 1) : ℤ) =
            psiZ ((m : ℤ) - j) * ((m + 1 + j).choose (j + 1) : ℤ) +
            psiZ ((m : ℤ) - j) * ((m + 1 + j).choose j : ℤ) := by
        intro j _
        push_cast
        rw [show (m : ℤ) + 1 - ((j : ℤ) + 1) = (m : ℤ) - j by ring,
          show m + 1 + (j + 1) = (m + 1 + j) + 1 by omega, Nat.choose_succ_succ]
        push_cast; ring
      rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ (fun j => psiZ ((m : ℤ) - j) * ((m + 1 + j).choose j : ℤ)) (m + 2)]
      have hpsi_neg2 : psiZ ((m : ℤ) - ((m + 2 : ℕ) : ℤ)) = -1 := by
        push_cast
        rw [show (m : ℤ) - ((m : ℤ) + 2) = -2 by ring]
        decide
      rw [hpsi_neg2, show m + 1 + (m + 2) = 2 * m + 3 by omega]
      have hB0 : ∑ j ∈ Finset.range (m + 2), psiZ ((m : ℤ) + 1 - j) * ((m + j).choose j : ℤ) =
          (∑ j ∈ Finset.range (m + 2), psiZ ((m : ℤ) - j) * ((m + 1 + j).choose (j + 1) : ℤ)) +
            psiZ ((m : ℤ) + 1) := by
        conv_lhs => rw [Finset.sum_range_succ']
        conv_rhs => lhs; rw [Finset.sum_range_succ]
        have hpsi_neg1 : psiZ ((m : ℤ) - ((m + 1 : ℕ) : ℤ)) = 0 := by
          push_cast
          rw [show (m : ℤ) - ((m : ℤ) + 1) = -1 by ring]
          decide
        rw [hpsi_neg1, zero_mul, add_zero]
        simp only [Nat.cast_zero, sub_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        rw [show (m : ℤ) + 1 - ((j : ℤ) + 1) = (m : ℤ) - j by ring,
          show m + (j + 1) = m + 1 + j by omega]
      linarith
    have hdouble : 2 * ((2 * m + 3).choose (m + 2) : ℤ) = ((2 * m + 4).choose (m + 2) : ℤ) := by
      have hc : (2 * m + 4).choose (m + 2) =
          (2 * m + 3).choose (m + 2) + (2 * m + 3).choose (m + 1) := by
        rw [show 2 * m + 4 = (2 * m + 3) + 1 by omega, Nat.choose_succ_succ, add_comm]
      have hsym : (2 * m + 3).choose (m + 1) = (2 * m + 3).choose (m + 2) := by
        rw [← Nat.choose_symm (show m + 1 ≤ 2 * m + 3 by omega)]
        congr 1; omega
      zify at hc hsym ⊢
      linarith
    have hA_diff : seqA (m + 2) - seqA (m + 1) = ((2 * m + 4).choose (m + 2) : ℤ) := by
      rw [seqA_eq_sum_central (m + 2), seqA_eq_sum_central (m + 1),
        Finset.sum_range_succ _ (m + 2), show 2 * (m + 2) = 2 * m + 4 by omega]
      ring
    linarith

lemma choose_sub_prime_cast {p : ℕ} [hp : Fact p.Prime] (N : ℕ) (hN_pos : 0 < N) :
    ∀ j : ℕ, N + j ≤ p →
      ((p - N).choose j : ZMod p) = (-1 : ZMod p) ^ j * ((N + j - 1).choose j : ZMod p)
  | 0, _ => by simp
  | j + 1, hjp => by
    have h1 : (j + 1) * (p - N).choose (j + 1) = (p - N - j) * (p - N).choose j := by
      have f1 := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ p - N by omega)
      have f2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ p - N by omega)
      have hf_step : (p - N - j).factorial = (p - N - j) * (p - N - (j + 1)).factorial := by
        rw [show p - N - j = (p - N - (j + 1)) + 1 by omega, Nat.factorial_succ]
      rw [hf_step] at f2
      rw [Nat.factorial_succ] at f1
      have hpos : 0 < j.factorial * (p - N - (j + 1)).factorial := by positivity
      apply Nat.mul_right_cancel hpos
      calc
        (j + 1) * (p - N).choose (j + 1) * (j.factorial * (p - N - (j + 1)).factorial)
            = (p - N).choose (j + 1) * ((j + 1) * j.factorial) * (p - N - (j + 1)).factorial := by
                ring
        _ = (p - N).factorial := f1
        _ = (p - N).choose j * j.factorial * ((p - N - j) * (p - N - (j + 1)).factorial) := f2.symm
        _ = (p - N - j) * (p - N).choose j * (j.factorial * (p - N - (j + 1)).factorial) := by ring
    have h2 : (j + 1) * (N + (j + 1) - 1).choose (j + 1) =
        (N + j) * (N + j - 1).choose j := by
      have f1 := Nat.choose_mul_factorial_mul_factorial (show j + 1 ≤ N + (j + 1) - 1 by omega)
      have f2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ N + j - 1 by omega)
      rw [show N + (j + 1) - 1 - (j + 1) = N - 1 by omega,
        show N + (j + 1) - 1 = N + j by omega, Nat.factorial_succ] at f1
      rw [show N + j - 1 - j = N - 1 by omega] at f2
      have hf_N : (N + j).factorial = (N + j) * (N + j - 1).factorial :=
        (Nat.mul_factorial_pred (show N + j ≠ 0 by omega)).symm
      rw [hf_N] at f1
      have hpos : 0 < j.factorial * (N - 1).factorial := by positivity
      apply Nat.mul_right_cancel hpos
      calc
        (j + 1) * (N + (j + 1) - 1).choose (j + 1) * (j.factorial * (N - 1).factorial)
            = (N + j).choose (j + 1) * ((j + 1) * j.factorial) * (N - 1).factorial := by
                rw [show N + (j + 1) - 1 = N + j by omega]; ring
        _ = (N + j) * (N + j - 1).factorial := f1
        _ = (N + j) * ((N + j - 1).choose j * j.factorial * (N - 1).factorial) := by rw [← f2]
        _ = (N + j) * (N + j - 1).choose j * (j.factorial * (N - 1).factorial) := by ring
    have hc1 : ((j + 1 : ℕ) : ZMod p) * ((p - N).choose (j + 1) : ZMod p) =
        ((p - N - j : ℕ) : ZMod p) * ((p - N).choose j : ZMod p) := by
      have := congrArg (fun x : ℕ => (x : ZMod p)) h1
      simpa only [Nat.cast_mul] using this
    have hc2 : ((j + 1 : ℕ) : ZMod p) * ((N + (j + 1) - 1).choose (j + 1) : ZMod p) =
        ((N + j : ℕ) : ZMod p) * ((N + j - 1).choose j : ZMod p) := by
      have := congrArg (fun x : ℕ => (x : ZMod p)) h2
      simpa only [Nat.cast_mul] using this
    have hsub : ((p - N - j : ℕ) : ZMod p) = -((N + j : ℕ) : ZMod p) := by
      have hs : (p - N - j) + (N + j) = p := by omega
      have hsc : ((p - N - j : ℕ) : ZMod p) + ((N + j : ℕ) : ZMod p) = (p : ZMod p) := by
        have := congrArg (fun x : ℕ => (x : ZMod p)) hs
        simpa only [Nat.cast_add] using this
      rw [ZMod.natCast_self] at hsc
      exact eq_neg_of_add_eq_zero_left hsc
    have hj_ne : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [hsub, choose_sub_prime_cast N hN_pos j (by omega)] at hc1
    apply mul_left_cancel₀ hj_ne
    calc
      ((j + 1 : ℕ) : ZMod p) * ((p - N).choose (j + 1) : ZMod p)
          = -((N + j : ℕ) : ZMod p) * ((-1 : ZMod p) ^ j * ((N + j - 1).choose j : ZMod p)) := hc1
      _ = (-1 : ZMod p) ^ (j + 1) *
            (((N + j : ℕ) : ZMod p) * ((N + j - 1).choose j : ZMod p)) := by
            rw [pow_succ]; ring
      _ = (-1 : ZMod p) ^ (j + 1) *
            (((j + 1 : ℕ) : ZMod p) * ((N + (j + 1) - 1).choose (j + 1) : ZMod p)) := by rw [← hc2]
      _ = ((j + 1 : ℕ) : ZMod p) *
            ((-1 : ZMod p) ^ (j + 1) * ((N + (j + 1) - 1).choose (j + 1) : ZMod p)) := by ring

lemma chiZ_neg_one_pow_odd (n j : ℕ) :
    chiZ ((2 * n + 1 : ℤ) - j) * (-1 : ℤ) ^ j = -psiZ ((2 * n + 1 : ℤ) - j) := by
  by_cases hj : j % 2 = 0
  · obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hj
    rw [pow_mul, neg_one_sq, one_pow, mul_one]
    unfold chiZ psiZ
    split_ifs <;> omega
  · have hpow : (-1 : ℤ) ^ j = -1 := by
      obtain ⟨q, hq⟩ : ∃ q, j = 2 * q + 1 := ⟨j / 2, by omega⟩
      rw [hq, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    rw [hpow]
    unfold chiZ psiZ
    split_ifs <;> omega

lemma three_mul_sum_central_eq_neg_one {p n : ℕ} [hp : Fact p.Prime] (hpn : p = 6 * n + 5) :
    3 * (∑ k ∈ Finset.range (2 * n + 2), ((2 * k).choose k : ZMod p)) = -1 := by
  set N := 2 * n + 1
  have hA_eq : (∑ k ∈ Finset.range (N + 1), ((2 * k).choose k : ZMod p)) = (seqA N : ZMod p) := by
    rw [seqA_eq_sum_central N]
    push_cast; rfl
  rw [show 2 * n + 2 = N + 1 by omega, hA_eq]
  have hAB : (seqA N : ZMod p) = -(seqB' (2 * n) : ZMod p) := by
    unfold seqA seqB'
    push_cast
    rw [← Finset.sum_neg_distrib, show 2 * n + 2 = N + 1 by omega]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hpN : 2 * N + 2 = p - N := by omega
    rw [hpN, choose_sub_prime_cast N (by omega) j (by omega)]
    have hsign := congrArg (fun x : ℤ => (x : ZMod p)) (chiZ_neg_one_pow_odd n j)
    push_cast at hsign
    dsimp [N]
    rw [show 2 * n + 1 + j - 1 = 2 * n + j by omega]
    linear_combination ((2 * n + j).choose j : ZMod p) * hsign
  have h2B : (2 : ZMod p) * (seqB' (2 * n) : ZMod p) = (seqA N : ZMod p) + 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod p)) (two_mul_seqB'_eq (2 * n))
    push_cast at this
    exact this
  linear_combination 2 * hAB - h2B

/- Part 4: Polynomial Derivative & Modulo `X ^ 2 - X + 1` Evaluation in `(ZMod p)[X]` -/

lemma centralBinom_succ_identity (k : ℕ) :
    (k + 1) * (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1) * (2 * k).choose k := by
  have hf1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  have hf2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
  rw [show 2 * k - k = k by omega] at hf1
  rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega,
    show 2 * (k + 1) = 2 * k + 2 by omega, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ (2 * k), Nat.factorial_succ k] at hf2
  have hpos : 0 < k.factorial * k.factorial * (k + 1) := by positivity
  apply Nat.mul_right_cancel hpos
  calc
    (k + 1) * (2 * (k + 1)).choose (k + 1) * (k.factorial * k.factorial * (k + 1))
        = (2 * k + 2).choose (k + 1) * ((k + 1) * k.factorial) * ((k + 1) * k.factorial) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by omega]; ring
    _ = (2 * k + 2) * ((2 * k + 1) * (2 * k).factorial) := hf2
    _ = (2 * k + 2) * (2 * k + 1) * ((2 * k).choose k * k.factorial * k.factorial) := by
          rw [← hf1]; ring
    _ = 2 * (2 * k + 1) * (2 * k).choose k * (k.factorial * k.factorial * (k + 1)) := by ring

lemma centralBinom_cast_eq_neg_four_pow_choose {p m : ℕ} [hp : Fact p.Prime] (hpm : p = 2 * m + 1) :
    ∀ k : ℕ, k ≤ m → ((2 * k).choose k : ZMod p) = (-4 : ZMod p) ^ k * (m.choose k : ZMod p)
  | 0, _ => by simp
  | k + 1, hkm => by
    have hc1 := centralBinom_succ_identity k
    have hc2 : (k + 1) * m.choose (k + 1) = (m - k) * m.choose k := by
      have f1 := Nat.choose_mul_factorial_mul_factorial hkm
      have f2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ m by omega)
      have hf_sub : (m - k).factorial = (m - k) * (m - (k + 1)).factorial := by
        rw [show m - k = (m - (k + 1)) + 1 by omega, Nat.factorial_succ]
      rw [hf_sub] at f2
      rw [Nat.factorial_succ] at f1
      have hpos : 0 < k.factorial * (m - (k + 1)).factorial := by positivity
      apply Nat.mul_right_cancel hpos
      calc
        (k + 1) * m.choose (k + 1) * (k.factorial * (m - (k + 1)).factorial)
            = m.choose (k + 1) * ((k + 1) * k.factorial) * (m - (k + 1)).factorial := by ring
        _ = m.factorial := f1
        _ = m.choose k * k.factorial * ((m - k) * (m - (k + 1)).factorial) := f2.symm
        _ = (m - k) * m.choose k * (k.factorial * (m - (k + 1)).factorial) := by ring
    have q1 : ((k + 1 : ℕ) : ZMod p) * ((2 * (k + 1)).choose (k + 1) : ZMod p) =
        2 * (2 * (k : ZMod p) + 1) * ((2 * k).choose k : ZMod p) := by
      have := congrArg (fun x : ℕ => (x : ZMod p)) hc1
      push_cast at this ⊢
      exact this
    have q2 : ((k + 1 : ℕ) : ZMod p) * (m.choose (k + 1) : ZMod p) =
        ((m : ZMod p) - (k : ZMod p)) * (m.choose k : ZMod p) := by
      have := congrArg (fun x : ℕ => (x : ZMod p)) hc2
      push_cast at this ⊢
      rw [Nat.cast_sub (by omega : k ≤ m)] at this
      exact this
    have hk_ne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hm_rel : (-4 : ZMod p) * ((m : ZMod p) - (k : ZMod p)) = 2 * (2 * (k : ZMod p) + 1) := by
      have hp0 : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by
        rw [← hpm]
        exact ZMod.natCast_self p
      push_cast at hp0
      linear_combination -2 * hp0
    rw [centralBinom_cast_eq_neg_four_pow_choose hpm k (by omega)] at q1
    apply mul_left_cancel₀ hk_ne
    calc
      ((k + 1 : ℕ) : ZMod p) * ((2 * (k + 1)).choose (k + 1) : ZMod p)
          = 2 * (2 * (k : ZMod p) + 1) * ((-4 : ZMod p) ^ k * (m.choose k : ZMod p)) := q1
      _ = (-4 : ZMod p) ^ k * ((-4 : ZMod p) * ((m : ZMod p) - (k : ZMod p))) *
            (m.choose k : ZMod p) := by rw [hm_rel]; ring
      _ = (-4 : ZMod p) ^ (k + 1) * (((m : ZMod p) - (k : ZMod p)) * (m.choose k : ZMod p)) := by
            rw [pow_succ]; ring
      _ = (-4 : ZMod p) ^ (k + 1) * (((k + 1 : ℕ) : ZMod p) * (m.choose (k + 1) : ZMod p)) := by
            rw [← q2]
      _ = ((k + 1 : ℕ) : ZMod p) * ((-4 : ZMod p) ^ (k + 1) * (m.choose (k + 1) : ZMod p)) := by
            ring

lemma sum_centralBinom_poly {p m : ℕ} [hp : Fact p.Prime] (hpm : p = 2 * m + 1) :
    (∑ k ∈ Finset.range (m + 1), C ((2 * k).choose k : ZMod p) * (X : (ZMod p)[X]) ^ k) =
      (1 - C 4 * X) ^ m := by
  rw [show (1 - C 4 * X : (ZMod p)[X]) = (-C 4 * X) + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [centralBinom_cast_eq_neg_four_pow_choose hpm k (by omega)]
  rw [one_pow, mul_one, mul_pow, ← C_eq_natCast, show (-C (4 : ZMod p) : (ZMod p)[X]) = C (-4) by simp,
    ← C_pow, map_mul]
  ring

lemma eq_C_of_derivative_eq_zero {p : ℕ} [hp : Fact p.Prime] {D : (ZMod p)[X]}
    (hd : derivative D = 0) (hdeg : ∀ i : ℕ, p ≤ i → D.coeff i = 0) :
    D = C (D.coeff 0) := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi0
  · simp
  · rw [coeff_C, if_neg hi0]
    by_cases hip : p ≤ i
    · exact hdeg i hip
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hc := coeff_derivative D j
      rw [hd, coeff_zero] at hc
      have hj_ne : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      exact (mul_eq_zero.mp hc.symm).resolve_right (by simpa using hj_ne)

lemma eq_C_add_X_pow_of_derivative_eq_zero {p : ℕ} [hp : Fact p.Prime] {D : (ZMod p)[X]}
    (hd : derivative D = 0) (hdeg : ∀ i : ℕ, 2 * p ≤ i → D.coeff i = 0) :
    D = C (D.coeff 0) + C (D.coeff p) * X ^ p := by
  have hp_pos : 0 < p := hp.out.pos
  ext i
  rcases eq_or_ne i 0 with rfl | hi0
  · simp [coeff_X_pow, hp_pos.ne]
  · rcases eq_or_ne i p with rfl | hip
    · simp [coeff_C, hi0]
    · have hrhs : (C (D.coeff 0) + C (D.coeff p) * X ^ p).coeff i = 0 := by
        simp [coeff_C, hi0, hip]
      rw [hrhs]
      by_cases hi2p : 2 * p ≤ i
      · exact hdeg i hi2p
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have hc := coeff_derivative D j
        rw [hd, coeff_zero] at hc
        have hj_ne : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          rintro ⟨q, hq⟩
          rcases eq_or_ne q 0 with rfl | hq0
          · omega
          · rcases eq_or_ne q 1 with rfl | hq1
            · exact hip (by omega)
            · have : p * 2 ≤ p * q := Nat.mul_le_mul_left p (by omega : 2 ≤ q)
              omega
        exact (mul_eq_zero.mp hc.symm).resolve_right (by simpa using hj_ne)

noncomputable def uPoly (p : ℕ) : (ZMod p)[X] := X * (1 - X)

noncomputable def gPoly (p k : ℕ) : (ZMod p)[X] := (uPoly p) ^ (k - 1)

noncomputable def polyQ (p k : ℕ) : (ZMod p)[X] :=
  ∑ i ∈ Finset.range (2 * k - 1),
    C ((gPoly p k).coeff i * (((i + 1 : ℕ) : ZMod p))⁻¹) * X ^ (i + 1)

lemma natDegree_uPoly_le (p : ℕ) : (uPoly p).natDegree ≤ 2 := by
  unfold uPoly
  have h1 : (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by
    rw [show (1 - X : (ZMod p)[X]) = 1 + (-X) by ring]
    refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_neg, natDegree_X_le]
  calc
    (X * (1 - X : (ZMod p)[X])).natDegree
        ≤ X.natDegree + (1 - X : (ZMod p)[X]).natDegree := natDegree_mul_le
    _ ≤ 1 + 1 := add_le_add natDegree_X_le h1
    _ = 2 := rfl

lemma natDegree_gPoly_le (p k : ℕ) : (gPoly p k).natDegree ≤ 2 * k - 2 := by
  unfold gPoly
  calc
    ((uPoly p) ^ (k - 1)).natDegree ≤ (k - 1) * (uPoly p).natDegree := natDegree_pow_le
    _ ≤ (k - 1) * 2 := Nat.mul_le_mul_left _ (natDegree_uPoly_le p)
    _ = 2 * k - 2 := by omega

lemma coeff_polyQ_zero (p k : ℕ) : (polyQ p k).coeff 0 = 0 := by
  unfold polyQ
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma eval_zero_polyQ (p k : ℕ) : (polyQ p k).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_polyQ_zero]

lemma coeff_polyQ_of_ge (p k : ℕ) {i : ℕ} (hi : 2 * k ≤ i) : (polyQ p k).coeff i = 0 := by
  unfold polyQ
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

lemma derivative_polyQ {p k : ℕ} [hp : Fact p.Prime] (hk1 : 1 ≤ k) (hkp : 2 * k - 1 < p) :
    derivative (polyQ p k) = gPoly p k := by
  ext j
  rw [coeff_derivative]
  unfold polyQ
  rw [finsetSum_coeff]
  by_cases hj : j < 2 * k - 1
  · have hsum : (∑ i ∈ Finset.range (2 * k - 1),
        (C ((gPoly p k).coeff i * (((i + 1 : ℕ) : ZMod p))⁻¹) * X ^ (i + 1)).coeff (j + 1)) =
        (gPoly p k).coeff j * (((j + 1 : ℕ) : ZMod p))⁻¹ := by
      rw [Finset.sum_eq_single j]
      · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
      · intro i _ hij
        rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hj) hnot
    rw [hsum]
    have hj_ne : (((j + 1 : ℕ) : ZMod p)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have hj_ne' : ((j : ZMod p) + 1) ≠ 0 := by push_cast at hj_ne; exact hj_ne
    push_cast
    rw [mul_assoc, inv_mul_cancel₀ hj_ne', mul_one]
  · have hsum : (∑ i ∈ Finset.range (2 * k - 1),
        (C ((gPoly p k).coeff i * (((i + 1 : ℕ) : ZMod p))⁻¹) * X ^ (i + 1)).coeff (j + 1)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    rw [hsum, zero_mul]
    symm
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_gPoly_le p k) (by omega))

lemma derivative_uPoly (p : ℕ) : derivative (uPoly p) = 1 - C 2 * X := by
  unfold uPoly
  rw [derivative_mul, derivative_X, derivative_sub, derivative_one, derivative_X]
  simp only [map_ofNat]
  ring

lemma polyQ_recurrence {p k : ℕ} [hp : Fact p.Prime] (hk1 : 1 ≤ k) (hkp : 2 * k + 1 < p) :
    C (k : ZMod p) * polyQ p k - C (4 * (k : ZMod p) + 2) * polyQ p (k + 1) =
      (1 - C 2 * X) * (uPoly p) ^ k := by
  set D := (C (k : ZMod p) * polyQ p k - C (4 * (k : ZMod p) + 2) * polyQ p (k + 1)) -
    (1 - C 2 * X) * (uPoly p) ^ k
  have hd : derivative D = 0 := by
    dsimp [D]
    rw [map_sub, map_sub, derivative_C_mul, derivative_C_mul,
      derivative_polyQ hk1 (by omega),
      derivative_polyQ (show 1 ≤ k + 1 by omega) (by omega),
      derivative_mul, derivative_sub, derivative_one, derivative_C_mul, derivative_X,
      derivative_pow, derivative_uPoly]
    unfold gPoly uPoly
    simp only [Nat.add_sub_cancel]
    have hpow : (X * (1 - X : (ZMod p)[X])) ^ k =
        (X * (1 - X)) ^ (k - 1) * (X * (1 - X)) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [hpow]
    simp only [C_eq_natCast, map_add, map_mul, map_ofNat]
    ring
  have hdeg : ∀ i : ℕ, p ≤ i → D.coeff i = 0 := by
    intro i hip
    dsimp [D]
    rw [coeff_sub, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_polyQ_of_ge p k (by omega),
      coeff_polyQ_of_ge p (k + 1) (by omega)]
    have hdeg_rhs : ((1 - C 2 * X) * (uPoly p) ^ k).natDegree < i := by
      have h1 : (1 - C 2 * X : (ZMod p)[X]).natDegree ≤ 1 := by
        rw [show (1 - C 2 * X : (ZMod p)[X]) = 1 + (-(C 2 * X)) by ring]
        refine le_trans (natDegree_add_le _ _) ?_
        simp only [natDegree_one, zero_le, max_eq_right, natDegree_neg]
        exact le_trans natDegree_mul_le (by simp [natDegree_C])
      have h2 : ((uPoly p) ^ k).natDegree ≤ 2 * k := by
        calc ((uPoly p) ^ k).natDegree ≤ k * (uPoly p).natDegree := natDegree_pow_le
        _ ≤ k * 2 := Nat.mul_le_mul_left _ (natDegree_uPoly_le p)
        _ = 2 * k := by ring
      calc ((1 - C 2 * X : (ZMod p)[X]) * (uPoly p) ^ k).natDegree
          ≤ (1 - C 2 * X : (ZMod p)[X]).natDegree + ((uPoly p) ^ k).natDegree := natDegree_mul_le
        _ ≤ 1 + 2 * k := add_le_add h1 h2
        _ < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg_rhs]
    ring
  have hD := eq_C_of_derivative_eq_zero hd hdeg
  have hc0 : D.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp [D, uPoly]
    simp [eval_zero_polyQ, zero_pow (by omega : k ≠ 0)]
  rw [hc0, map_zero] at hD
  exact sub_eq_zero.mp hD

lemma polyQ_eval_one_identity {p : ℕ} [hp : Fact p.Prime] :
    ∀ k : ℕ, 1 ≤ k → 2 * k - 1 < p →
      (k : ZMod p) * ((2 * k).choose k : ZMod p) * (polyQ p k).eval 1 = 2
  | 0, hk1, _ => by omega
  | 1, _, _ => by
    unfold polyQ gPoly
    simp
  | k + 2, _, hkp => by
    set j := k + 1
    have hj1 : 1 ≤ j := by omega
    have ih := polyQ_eval_one_identity (p := p) j hj1 (by dsimp [j]; omega)
    have hrec := congrArg (eval 1) (polyQ_recurrence (p := p) hj1 (by dsimp [j]; omega))
    unfold uPoly at hrec
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_one, eval_X,
      sub_self, mul_zero, zero_pow (by omega : j ≠ 0), sub_eq_zero] at hrec
    have hc := congrArg (fun x : ℕ => (x : ZMod p)) (centralBinom_succ_identity j)
    push_cast at hc
    change ((j + 1 : ℕ) : ZMod p) * ((2 * (j + 1)).choose (j + 1) : ZMod p) *
      (polyQ p (j + 1)).eval 1 = 2
    push_cast
    linear_combination (polyQ p (j + 1)).eval 1 * hc -
      ((2 * j).choose j : ZMod p) * hrec + ih

noncomputable def modPoly (p : ℕ) : (ZMod p)[X] := X ^ 2 - X + 1

lemma modPoly_dvd_uPoly_pow_sub_one (p : ℕ) :
    ∀ k : ℕ, modPoly p ∣ (uPoly p) ^ k - 1
  | 0 => by simp
  | k + 1 => by
    have h1 : modPoly p ∣ uPoly p - 1 := by
      refine ⟨-1, ?_⟩
      unfold modPoly uPoly; ring
    have hsplit : (uPoly p) ^ (k + 1) - 1 =
        uPoly p * ((uPoly p) ^ k - 1) + (uPoly p - 1) := by
      rw [pow_succ']; ring
    rw [hsplit]
    exact dvd_add (dvd_mul_of_dvd_right (modPoly_dvd_uPoly_pow_sub_one p k) _) h1

lemma modPoly_dvd_two_mul_polyQ {p : ℕ} [hp : Fact p.Prime] :
    ∀ k : ℕ, 1 ≤ k → 2 * k - 1 < p →
      modPoly p ∣ C 2 * polyQ p k -
        C ((polyQ p k).eval 1) *
          (1 + (C 2 * X - 1) * C (∑ i ∈ Finset.range k, ((2 * i).choose i : ZMod p)))
  | 0, hk1, _ => by omega
  | 1, _, _ => by
    unfold polyQ gPoly
    simp
  | k + 2, _, hkp => by
    set j := k + 1
    have hj1 : 1 ≤ j := by omega
    have ih := modPoly_dvd_two_mul_polyQ (p := p) j hj1 (by dsimp [j]; omega)
    have hrec := polyQ_recurrence (p := p) hj1 (by dsimp [j]; omega)
    have hdvd_u : modPoly p ∣ (1 - C 2 * X) * ((uPoly p) ^ j - 1) :=
      dvd_mul_of_dvd_right (modPoly_dvd_uPoly_pow_sub_one p j) _
    have hdvd_rec : modPoly p ∣
        (C (j : ZMod p) * polyQ p j - C (4 * (j : ZMod p) + 2) * polyQ p (j + 1)) -
          (1 - C 2 * X) := by
      rw [hrec]
      simpa [mul_sub, mul_one] using hdvd_u
    have hq_rel : (j : ZMod p) * (polyQ p j).eval 1 =
        (4 * (j : ZMod p) + 2) * (polyQ p (j + 1)).eval 1 := by
      have hr1 := congrArg (eval 1) hrec
      unfold uPoly at hr1
      simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_one, eval_X,
        sub_self, mul_zero, zero_pow (by omega : j ≠ 0), sub_eq_zero] at hr1
      exact hr1
    have hval := polyQ_eval_one_identity (p := p) j hj1 (by dsimp [j]; omega)
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have h2j1_ne : (2 * (j : ZMod p) + 1) ≠ 0 := by
      have : (2 * (j : ZMod p) + 1) = ((2 * j + 1 : ℕ) : ZMod p) := by push_cast; ring
      rw [this, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      dsimp [j] at this
      omega
    have h4j2_ne : (4 * (j : ZMod p) + 2) ≠ 0 := by
      rw [show (4 * (j : ZMod p) + 2) = 2 * (2 * (j : ZMod p) + 1) by ring]
      exact mul_ne_zero h2_ne h2j1_ne
    change modPoly p ∣ C 2 * polyQ p (j + 1) -
      C ((polyQ p (j + 1)).eval 1) *
        (1 + (C 2 * X - 1) * C (∑ i ∈ Finset.range (j + 1), ((2 * i).choose i : ZMod p)))
    obtain ⟨P1, hP1⟩ := ih
    obtain ⟨P2, hP2⟩ := hdvd_rec
    refine ⟨C ((4 * (j : ZMod p) + 2)⁻¹) * (C (j : ZMod p) * P1 - C 2 * P2), ?_⟩
    rw [Finset.sum_range_succ]
    set S := ∑ i ∈ Finset.range j, ((2 * i).choose i : ZMod p)
    set qj := (polyQ p j).eval 1
    set qj1 := (polyQ p (j + 1)).eval 1
    set cj := ((2 * j).choose j : ZMod p)
    have hcoef : C (4 * (j : ZMod p) + 2) *
        (C 2 * polyQ p (j + 1) - C qj1 * (1 + (C 2 * X - 1) * C (S + cj))) =
        C (j : ZMod p) * (C 2 * polyQ p j - C qj * (1 + (C 2 * X - 1) * C S)) -
        C 2 * ((C (j : ZMod p) * polyQ p j - C (4 * (j : ZMod p) + 2) * polyQ p (j + 1)) -
          (1 - C 2 * X)) +
        C ((j : ZMod p) * qj - (4 * (j : ZMod p) + 2) * qj1) *
          (1 + (C 2 * X - 1) * C S) +
        C (2 - ((4 * (j : ZMod p) + 2) * qj1) * cj) * (C 2 * X - 1) := by
      simp only [C_eq_natCast, map_add, map_sub, map_mul, map_ofNat]
      ring
    have hz1 : (j : ZMod p) * qj - (4 * (j : ZMod p) + 2) * qj1 = 0 := sub_eq_zero.mpr hq_rel
    have hz2 : 2 - ((4 * (j : ZMod p) + 2) * qj1) * cj = 0 := by
      rw [← hq_rel]
      linear_combination -hval
    rw [hz1, hz2, map_zero, zero_mul, zero_mul, add_zero, add_zero, hP1, hP2] at hcoef
    have hinv : C ((4 * (j : ZMod p) + 2)⁻¹) * C (4 * (j : ZMod p) + 2) = (1 : (ZMod p)[X]) := by
      rw [← map_mul, inv_mul_cancel₀ h4j2_ne, map_one]
    calc
      C 2 * polyQ p (j + 1) - C qj1 * (1 + (C 2 * X - 1) * C (S + cj))
          = (C ((4 * (j : ZMod p) + 2)⁻¹) * C (4 * (j : ZMod p) + 2)) *
              (C 2 * polyQ p (j + 1) - C qj1 * (1 + (C 2 * X - 1) * C (S + cj))) := by
              rw [hinv, one_mul]
      _ = C ((4 * (j : ZMod p) + 2)⁻¹) *
            (C (j : ZMod p) * (modPoly p * P1) - C 2 * (modPoly p * P2)) := by
            rw [mul_assoc, hcoef]
      _ = modPoly p * (C ((4 * (j : ZMod p) + 2)⁻¹) * (C (j : ZMod p) * P1 - C 2 * P2)) := by
            ring

noncomputable def polyF (p m : ℕ) : (ZMod p)[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C (((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹) * X ^ k

lemma natDegree_polyF_le (p : ℕ) : ∀ m : ℕ, (polyF p m).natDegree ≤ m
  | 0 => by
    unfold polyF
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    exact natDegree_C_mul_X_pow_le _ 0
  | m + 1 => by
    unfold polyF
    rw [Finset.sum_range_succ]
    refine (natDegree_add_le _ _).trans ?_
    exact max_le ((natDegree_polyF_le p m).trans (by omega)) (natDegree_C_mul_X_pow_le _ (m + 1))

lemma derivative_three_X_pow_mul_polyF {p n m r : ℕ} [hp : Fact p.Prime]
    (hpn : p = 6 * n + 5) (hm : m = 3 * n + 2) (hr : r = 2 * n + 2) :
    derivative (C 3 * (X ^ r * polyF p m)) = X ^ (r - 1) * (1 - C 4 * X) ^ m := by
  unfold polyF
  rw [Finset.mul_sum, Finset.mul_sum, map_sum]
  rw [← sum_centralBinom_poly (p := p) (m := m) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hexp : C (3 : ZMod p) * (X ^ r * (C (((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹) * X ^ k)) =
      C (3 * ((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹) * X ^ (r + k) := by
    simp only [map_mul, map_ofNat]
    rw [pow_add]
    ring
  rw [hexp, derivative_C_mul, derivative_X_pow]
  have h3r : 3 * (r : ZMod p) = 1 := by
    have : 3 * r = p + 1 := by omega
    have hc := congrArg (fun x : ℕ => (x : ZMod p)) this
    push_cast at hc
    rw [ZMod.natCast_self, zero_add] at hc
    exact hc
  have h3rk : 3 * ((r + k : ℕ) : ZMod p) = 3 * (k : ZMod p) + 1 := by
    push_cast; linear_combination h3r
  have hne : (3 * (k : ZMod p) + 1) ≠ 0 := by
    have hcast : (3 * (k : ZMod p) + 1) = ((3 * k + 1 : ℕ) : ZMod p) := by push_cast; ring
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_three_mul_add_one (by omega) (by omega)
  have hcancel : 3 * ((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹ *
      ((r + k : ℕ) : ZMod p) = ((2 * k).choose k : ZMod p) := by
    calc
      3 * ((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹ * ((r + k : ℕ) : ZMod p)
          = ((2 * k).choose k : ZMod p) *
              ((3 * (k : ZMod p) + 1)⁻¹ * (3 * ((r + k : ℕ) : ZMod p))) := by ring
      _ = ((2 * k).choose k : ZMod p) * ((3 * (k : ZMod p) + 1)⁻¹ * (3 * (k : ZMod p) + 1)) := by
            rw [h3rk]
      _ = ((2 * k).choose k : ZMod p) := by rw [inv_mul_cancel₀ hne, mul_one]
  rw [show r + k - 1 = (r - 1) + k by omega, pow_add, ← mul_assoc, ← map_mul, hcancel]
  ring

lemma polyH_eq {p n m r : ℕ} [hp : Fact p.Prime]
    (hpn : p = 6 * n + 5) (hm : m = 3 * n + 2) (hr : r = 2 * n + 2) :
    (C 3 * (X ^ r * polyF p m)).comp (uPoly p) =
      polyQ p r - C 2 * X ^ p * polyQ p r + C ((polyQ p r).eval 1) * X ^ p := by
  set H := (C 3 * (X ^ r * polyF p m)).comp (uPoly p)
  set qr := (polyQ p r).eval 1
  set R := polyQ p r - C 2 * X ^ p * polyQ p r + C qr * X ^ p
  have hdH : derivative H = (uPoly p) ^ (r - 1) - C 2 * X ^ p * (uPoly p) ^ (r - 1) := by
    dsimp [H]
    rw [derivative_comp, derivative_three_X_pow_mul_polyF hpn hm hr, derivative_uPoly]
    simp only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, C_comp]
    have hsq : 1 - C (4 : ZMod p) * uPoly p = (1 - C (2 : ZMod p) * X) ^ 2 := by
      unfold uPoly; simp only [map_ofNat]; ring
    have hpowp : (1 - C (2 : ZMod p) * X) ^ p = 1 - C (2 : ZMod p) * X ^ p := by
      rw [sub_pow_char, one_pow, mul_pow, ← C_pow]
      have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
      rw [h2p]
    rw [hsq]
    have hpow2m : ((1 - C (2 : ZMod p) * X) ^ 2) ^ m * (1 - C 2 * X) =
        1 - C 2 * X ^ p := by
      rw [← pow_mul, ← pow_succ, show 2 * m + 1 = p by omega, hpowp]
    linear_combination (uPoly p) ^ (r - 1) * hpow2m
  have hderiv_Xp : derivative (X ^ p : (ZMod p)[X]) = 0 := by
    rw [derivative_X_pow, CharP.cast_eq_zero, map_zero, zero_mul]
  have hdQ : derivative (polyQ p r) = (uPoly p) ^ (r - 1) :=
    derivative_polyQ (show 1 ≤ r by omega) (show 2 * r - 1 < p by omega)
  have hdR : derivative R = (uPoly p) ^ (r - 1) - C 2 * X ^ p * (uPoly p) ^ (r - 1) := by
    dsimp [R]
    rw [map_add, map_sub, hdQ,
      show C (2 : ZMod p) * X ^ p * polyQ p r = (C 2 * X ^ p) * polyQ p r by ring,
      derivative_mul, derivative_C_mul, hderiv_Xp, mul_zero, zero_mul, zero_add, hdQ,
      derivative_C_mul, hderiv_Xp, mul_zero, add_zero]
  set D := H - R
  have hdD : derivative D = 0 := by
    dsimp [D]
    rw [map_sub, hdH, hdR, sub_self]
  have hdegH : H.natDegree ≤ 2 * (r + m) := by
    dsimp [H]
    have hdegP : (C 3 * (X ^ r * polyF p m)).natDegree ≤ r + m := by
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      exact add_le_add (natDegree_X_pow_le r) (natDegree_polyF_le p m)
    calc
      ((C 3 * (X ^ r * polyF p m)).comp (uPoly p)).natDegree
          ≤ (C 3 * (X ^ r * polyF p m)).natDegree * (uPoly p).natDegree := natDegree_comp_le
      _ ≤ (r + m) * 2 := Nat.mul_le_mul hdegP (natDegree_uPoly_le p)
      _ = 2 * (r + m) := by ring
  have hdegD : ∀ i : ℕ, 2 * p ≤ i → D.coeff i = 0 := by
    intro i hi
    dsimp [D, R]
    have hcH : H.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegH (by omega))
    have hcQ1 : (polyQ p r).coeff i = 0 :=
      coeff_polyQ_of_ge p r (by omega)
    have hcQ2 : (C 2 * X ^ p * polyQ p r).coeff i = 0 := by
      rw [show C (2 : ZMod p) * X ^ p * polyQ p r = C 2 * (X ^ p * polyQ p r) by ring,
        coeff_C_mul, coeff_X_pow_mul', if_pos (by omega : p ≤ i),
        coeff_polyQ_of_ge p r (by omega), mul_zero]
    have hcC : (C qr * X ^ p).coeff i = 0 := by
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega : i ≠ p), mul_zero]
    simp [hcH, hcQ1, hcQ2, hcC]
  have hD_form := eq_C_add_X_pow_of_derivative_eq_zero hdD hdegD
  have hp_pos : 0 < p := hp.out.pos
  have hr_ne : r ≠ 0 := by omega
  have heval0 : D.eval 0 = 0 := by
    dsimp [D, H, R, uPoly]
    simp [eval_comp, eval_zero_polyQ, zero_pow hr_ne, zero_pow hp_pos.ne']
  have hc0 : D.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero, heval0]
  rw [hc0, map_zero, zero_add] at hD_form
  have heval1 : D.eval 1 = 0 := by
    have hH1 : H.eval 1 = 0 := by
      dsimp [H, uPoly]
      rw [eval_comp]
      simp [zero_pow hr_ne]
    have hR1 : R.eval 1 = 0 := by
      dsimp [R, qr]
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow]
      ring
    dsimp [D]
    rw [eval_sub, hH1, hR1, sub_self]
  have hcp : D.coeff p = 0 := by
    have := congrArg (eval 1) hD_form
    rw [heval1, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] at this
    exact this.symm
  rw [hcp, map_zero, zero_mul] at hD_form
  exact sub_eq_zero.mp hD_form

lemma modPoly_dvd_X_pow_six_mul_add_five (p : ℕ) :
    ∀ n : ℕ, modPoly p ∣ (X : (ZMod p)[X]) ^ (6 * n + 5) - (1 - X)
  | 0 => by
    refine ⟨X ^ 3 + X ^ 2 - 1, ?_⟩
    unfold modPoly; ring
  | n + 1 => by
    have h6 : modPoly p ∣ (X : (ZMod p)[X]) ^ 6 - 1 := by
      refine ⟨X ^ 4 + X ^ 3 - X - 1, ?_⟩
      unfold modPoly; ring
    have hsplit : (X : (ZMod p)[X]) ^ (6 * (n + 1) + 5) - (1 - X) =
        X ^ (6 * n + 5) * (X ^ 6 - 1) + (X ^ (6 * n + 5) - (1 - X)) := by
      rw [show 6 * (n + 1) + 5 = (6 * n + 5) + 6 by omega, pow_add]
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_of_dvd_right h6 _) (modPoly_dvd_X_pow_six_mul_add_five p n)

lemma eq_zero_of_modPoly_dvd_C {p : ℕ} {c : ZMod p} (h : modPoly p ∣ C c) : c = 0 := by
  obtain ⟨Q, hQ⟩ := h
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero] at hQ
    have := congrArg (fun P => P.coeff 0) hQ
    simpa using this
  · exfalso
    set j := Q.natDegree
    have hlead : Q.coeff j ≠ 0 := by
      change Q.leadingCoeff ≠ 0
      exact leadingCoeff_ne_zero.mpr hQ0
    have hc := congrArg (fun P => P.coeff (j + 2)) hQ
    rw [coeff_C_of_ne_zero (by omega)] at hc
    have hexp : modPoly p * Q = X ^ 2 * Q - X * Q + Q := by unfold modPoly; ring
    rw [hexp, coeff_add, coeff_sub, coeff_X_pow_mul,
      show j + 2 = (j + 1) + 1 by omega, coeff_X_mul,
      coeff_eq_zero_of_natDegree_lt (show Q.natDegree < j + 1 by dsimp [j]; omega),
      coeff_eq_zero_of_natDegree_lt (show Q.natDegree < j + 1 + 1 by dsimp [j]; omega),
      sub_zero, add_zero] at hc
    exact hlead hc.symm

lemma polyF_eval_one_eq {p n m r : ℕ} [hp : Fact p.Prime]
    (hpn : p = 6 * n + 5) (hm : m = 3 * n + 2) (hr : r = 2 * n + 2) :
    ((2 * r).choose r : ZMod p) * (polyF p m).eval 1 = 2 := by
  set F1 := (polyF p m).eval 1
  set qr := (polyQ p r).eval 1
  have hH_eq := polyH_eq hpn hm hr
  -- 1. H ≡ C (3 * F1) (mod modPoly p)
  have hdvd_H : modPoly p ∣ (C 3 * (X ^ r * polyF p m)).comp (uPoly p) - C (3 * F1) := by
    have hexpand : (C 3 * (X ^ r * polyF p m)).comp (uPoly p) - C (3 * F1) =
        ∑ k ∈ Finset.range (m + 1),
          C (3 * (((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹)) *
            ((uPoly p) ^ (r + k) - 1) := by
      have hF1 : F1 = ∑ k ∈ Finset.range (m + 1),
          ((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹ := by
        dsimp [F1]
        unfold polyF
        rw [eval_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp
      unfold polyF
      rw [hF1, Finset.mul_sum, Finset.mul_sum, sum_comp, Finset.mul_sum, map_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_comp, pow_comp, X_comp, C_comp, map_mul]
      rw [pow_add]
      ring
    rw [hexpand]
    exact Finset.dvd_sum fun k _ =>
      dvd_mul_of_dvd_right (modPoly_dvd_uPoly_pow_sub_one p (r + k)) _
  -- 2. C 3 * polyQ p r ≡ C qr * (C 2 - X) (mod modPoly p)
  have hdvd_Q2 := modPoly_dvd_two_mul_polyQ (p := p) r (by omega) (by omega)
  have hsum3 : 3 * (∑ i ∈ Finset.range r, ((2 * i).choose i : ZMod p)) = -1 := by
    rw [hr]
    exact three_mul_sum_central_eq_neg_one hpn
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hdvd_3Q : modPoly p ∣ C 3 * polyQ p r - C qr * (C 2 - X) := by
    obtain ⟨P_Q, hP_Q⟩ := hdvd_Q2
    refine ⟨C ((2 : ZMod p)⁻¹ * 3) * P_Q, ?_⟩
    set S_r := ∑ i ∈ Finset.range r, ((2 * i).choose i : ZMod p)
    have hmul3 : C (3 : ZMod p) *
        (C 2 * polyQ p r - C qr * (1 + (C 2 * X - 1) * C S_r)) =
        C 2 * (C 3 * polyQ p r - C qr * (C 2 - X)) := by
      have hS : C (3 : ZMod p) * C S_r = C (-1 : ZMod p) := by
        rw [← map_mul, hsum3]
      calc
        C (3 : ZMod p) * (C 2 * polyQ p r - C qr * (1 + (C 2 * X - 1) * C S_r))
            = C 2 * (C 3 * polyQ p r) - C qr * (C 3 + (C 2 * X - 1) * (C 3 * C S_r)) := by ring
        _ = C 2 * (C 3 * polyQ p r) - C qr * (C 3 + (C 2 * X - 1) * C (-1)) := by rw [hS]
        _ = C 2 * (C 3 * polyQ p r - C qr * (C 2 - X)) := by
              simp only [map_neg, map_one, map_ofNat]; ring
    have hinv2 : C ((2 : ZMod p)⁻¹) * C (2 : ZMod p) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ h2_ne, map_one]
    calc
      C 3 * polyQ p r - C qr * (C 2 - X)
          = (C ((2 : ZMod p)⁻¹) * C 2) * (C 3 * polyQ p r - C qr * (C 2 - X)) := by
              rw [hinv2, one_mul]
      _ = C ((2 : ZMod p)⁻¹) * (C 2 * (C 3 * polyQ p r - C qr * (C 2 - X))) := by ring
      _ = C ((2 : ZMod p)⁻¹) * (C 3 * (modPoly p * P_Q)) := by rw [← hmul3, hP_Q]
      _ = modPoly p * (C ((2 : ZMod p)⁻¹ * 3) * P_Q) := by simp only [map_mul, map_ofNat]; ring
  -- 3. X ^ p ≡ 1 - X (mod modPoly p)
  have hdvd_Xp : modPoly p ∣ (X : (ZMod p)[X]) ^ p - (1 - X) := by
    have := modPoly_dvd_X_pow_six_mul_add_five p n
    rwa [← hpn] at this
  -- 4. Combine into modPoly p ∣ C (9 * F1 - 3 * qr)
  have hdvd_const : modPoly p ∣ C (9 * F1 - 3 * qr) := by
    obtain ⟨P_H, hP_H⟩ := hdvd_H
    obtain ⟨P_Q, hP_Q⟩ := hdvd_3Q
    obtain ⟨P_X, hP_X⟩ := hdvd_Xp
    rw [hH_eq] at hP_H
    refine ⟨-C 3 * P_H + (1 - C 2 * X ^ p) * P_Q -
      C qr * (1 - C 2 * X) * P_X - C (2 * qr), ?_⟩
    have hident : C (9 * F1 - 3 * qr) =
        -C 3 * ((polyQ p r - C 2 * X ^ p * polyQ p r + C qr * X ^ p) - C (3 * F1)) +
        (1 - C 2 * X ^ p) * (C 3 * polyQ p r - C qr * (C 2 - X)) -
        C qr * (1 - C 2 * X) * (X ^ p - (1 - X)) -
        modPoly p * C (2 * qr) := by
      unfold modPoly
      simp only [map_sub, map_mul, map_ofNat]
      ring
    rw [hident, hP_H, hP_Q, hP_X]
    ring
  have hc_zero : 9 * F1 - 3 * qr = 0 := eq_zero_of_modPoly_dvd_C hdvd_const
  have h3_ne : (3 : ZMod p) ≠ 0 := by
    rw [Ne, show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hqr_eq : qr = 3 * F1 := by
    apply mul_left_cancel₀ h3_ne
    linear_combination -hc_zero
  have hQ1 := polyQ_eval_one_identity (p := p) r (by omega) (by omega)
  have h3r : 3 * (r : ZMod p) = 1 := by
    have : 3 * r = p + 1 := by omega
    have hc := congrArg (fun x : ℕ => (x : ZMod p)) this
    push_cast at hc
    rw [ZMod.natCast_self, zero_add] at hc
    exact hc
  calc
    ((2 * r).choose r : ZMod p) * F1
        = (3 * (r : ZMod p)) * ((2 * r).choose r : ZMod p) * F1 := by rw [h3r, one_mul]
    _ = (r : ZMod p) * ((2 * r).choose r : ZMod p) * (3 * F1) := by ring
    _ = (r : ZMod p) * ((2 * r).choose r : ZMod p) * qr := by rw [← hqr_eq]
    _ = 2 := hQ1

/- Part 5: Final Rational Numerator Congruence Modulo `p ^ 2` -/

theorem conjecture_3 (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 2) :
    ((∑ k ∈ Finset.range p, (a k : ℚ)) -
      (2 * p : ℚ) / ((2 * (p + 1) / 3).choose ((p + 1) / 3) : ℚ)).num % (p ^ 2 : ℤ) = 0 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · norm_num [a, Finset.sum_range_succ]
  · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    set n := p / 6
    have hpn : p = 6 * n + 5 := by omega
    have : Fact p.Prime := ⟨hp⟩
    set m := 3 * n + 2
    set r := 2 * n + 2
    have hsum_a : ∑ j ∈ Finset.range p, a j = ∑ k ∈ Finset.range (m + 1), TTerm p k :=
      sum_a_eq_sum_TTerm (by dsimp [m]; omega)
    set U : ℕ := ∑ k ∈ Finset.range (m + 1), TTerm p k / p
    have hsum_eq_pU : ∑ j ∈ Finset.range p, a j = p * U := by
      rw [hsum_a]
      dsimp [U]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hdvd := (dvd_TTerm_and_div_cast (p := p) (k := k) hmod (by dsimp [m] at hk; omega)).1
      exact (Nat.mul_div_cancel' hdvd).symm
    have hU_cast : (U : ZMod p) = (polyF p m).eval 1 := by
      dsimp [U]
      unfold polyF
      rw [Nat.cast_sum, eval_finsetSum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      have hdiv := (dvd_TTerm_and_div_cast (p := p) (k := k) hmod (by dsimp [m] at hk; omega)).2
      have hne : (3 * (k : ZMod p) + 1) ≠ 0 := by
        have hcast : (3 * (k : ZMod p) + 1) = ((3 * k + 1 : ℕ) : ZMod p) := by push_cast; ring
        rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
        exact not_dvd_three_mul_add_one hmod (by dsimp [m] at hk; omega)
      simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
      apply mul_left_cancel₀ hne
      rw [hdiv]
      calc
        ((2 * k).choose k : ZMod p)
            = ((2 * k).choose k : ZMod p) * ((3 * (k : ZMod p) + 1) * (3 * (k : ZMod p) + 1)⁻¹) := by
                rw [mul_inv_cancel₀ hne, mul_one]
        _ = (3 * (k : ZMod p) + 1) * (((2 * k).choose k : ZMod p) * (3 * (k : ZMod p) + 1)⁻¹) := by
                ring
    set Cr : ℕ := (2 * r).choose r
    have hr1 : (p + 1) / 3 = r := by dsimp [r]; omega
    have hr2 : 2 * (p + 1) / 3 = 2 * r := by dsimp [r]; omega
    rw [hr1, hr2]
    change ((∑ k ∈ Finset.range p, (a k : ℚ)) - (2 * p : ℚ) / (Cr : ℚ)).num % (p ^ 2 : ℤ) = 0
    have hCr_U : (Cr : ZMod p) * (U : ZMod p) = 2 := by
      rw [hU_cast]
      exact polyF_eval_one_eq hpn rfl rfl
    have hp_dvd_diff : (p : ℤ) ∣ (U : ℤ) * (Cr : ℤ) - 2 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      linear_combination hCr_U
    have hCr_pos : 0 < Cr := Nat.choose_pos (by omega)
    have hp_not_dvd_Cr : ¬ (p ∣ Cr) := by
      intro hdvd
      have hf := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
      rw [show 2 * r - r = r by omega] at hf
      have hdvd_fac : p ∣ (2 * r).factorial := by
        rw [← hf]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
      rw [hp.dvd_factorial] at hdvd_fac
      dsimp [r] at hdvd_fac
      omega
    set q : ℚ := (∑ k ∈ Finset.range p, (a k : ℚ)) - (2 * p : ℚ) / (Cr : ℚ)
    set N_int : ℤ := (p : ℤ) * ((U : ℤ) * (Cr : ℤ) - 2)
    have hq_mul : (q.num : ℚ) * (Cr : ℚ) = (N_int : ℚ) * (q.den : ℚ) := by
      have hCr_ne : (Cr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hCr_pos.ne'
      have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
      have hsum_q : (∑ k ∈ Finset.range p, (a k : ℚ)) = (p : ℚ) * (U : ℚ) := by
        exact_mod_cast hsum_eq_pU
      have hq_eq : q * (Cr : ℚ) = (N_int : ℚ) := by
        dsimp [q, N_int]
        rw [hsum_q]
        push_cast
        field_simp [hCr_ne]
      calc
        (q.num : ℚ) * (Cr : ℚ)
            = ((q.num : ℚ) / (q.den : ℚ)) * (Cr : ℚ) * (q.den : ℚ) := by field_simp [hden_ne]
        _ = (q * (Cr : ℚ)) * (q.den : ℚ) := by rw [Rat.num_div_den]
        _ = (N_int : ℚ) * (q.den : ℚ) := by rw [hq_eq]
    have hmul_int : q.num * (Cr : ℤ) = N_int * (q.den : ℤ) := by
      exact_mod_cast hq_mul
    have hp2_dvd_N : ((p ^ 2 : ℕ) : ℤ) ∣ N_int := by
      obtain ⟨t, ht⟩ := hp_dvd_diff
      refine ⟨t, ?_⟩
      dsimp [N_int]
      rw [ht]
      ring
    have hp2_dvd_mul : p ^ 2 ∣ (q.num * (Cr : ℤ)).natAbs := by
      rw [hmul_int, Int.natAbs_mul]
      have hdvd_abs : p ^ 2 ∣ N_int.natAbs := Int.natCast_dvd.mp hp2_dvd_N
      exact dvd_mul_of_dvd_left hdvd_abs _
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hp2_dvd_mul
    have hcop : (p ^ 2).Coprime Cr := (hp.coprime_iff_not_dvd.mpr hp_not_dvd_Cr).pow_left 2
    have hp2_dvd_num_abs : p ^ 2 ∣ q.num.natAbs := hcop.dvd_of_dvd_mul_right hp2_dvd_mul
    have hp2_dvd_num : (p ^ 2 : ℤ) ∣ q.num := by
      exact_mod_cast Int.natCast_dvd.mpr hp2_dvd_num_abs
    exact Int.emod_eq_zero_of_dvd hp2_dvd_num

end Solutions.OeisA208425_3

theorem OMA.solution : type_of% @OeisA208425.conjecture_3 := by
  exact Solutions.OeisA208425_3.conjecture_3
