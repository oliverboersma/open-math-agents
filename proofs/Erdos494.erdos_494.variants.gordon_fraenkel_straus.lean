import FormalConjectures.ErdosProblems.«494»
import Mathlib

/-!
# Erdos Problem 494

The core of this file (namespace OMA494, renamed from Erdos494 to avoid clashing with the
upstream statement file) is adapted from the Lean 4 formalization in
https://github.com/hongjin-he/erdos-lean (directory ErdosLean/Erdos494, commit efede969),
released under the Apache License 2.0. Changes: the modules are concatenated in dependency order, comments are removed, the namespace
is renamed, and Mathlib API drift is repaired. The final section bridges the source statement
to the one in FormalConjectures.ErdosProblems.494 and derives the target statement.
-/

-- Statement
section
open Filter

namespace OMA494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

def GFSStatement : Prop :=
  ∀ k > 2, ∀ᶠ card in atTop, Erdos494Unique k card

def Erdos494Full : Prop :=
  (∀ k > 2, ¬Erdos494Unique k k) ∧ (∀ k > 2, ¬Erdos494Unique k (2 * k)) ∧ GFSStatement

end OMA494
end

-- Defs
section
namespace OMA494

def gfsPoly (s n j : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 s, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (s - i) : ℤ)

def GFSCore : Prop :=
  ∀ s > 2, ∀ᶠ n in Filter.atTop, ∀ j ≥ 1, gfsPoly s n j ≠ 0

def psum (A : Finset ℂ) (j : ℕ) : ℂ := ∑ a ∈ A, a ^ j

noncomputable def ksumPsum (A : Finset ℂ) (s j : ℕ) : ℂ :=
  ((sumMultiset A s).map (· ^ j)).sum

noncomputable def hasseEval (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (x y : ℝ) : ℝ :=
  ∑ k1 ∈ Finset.range (r1 + 1), ∑ k2 ∈ Finset.range (r2 + 1),
    (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * x ^ (k1 - i1) * y ^ (k2 - i2)

def BoxNonzero (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) : Prop :=
  ∃ k1 ≤ r1, ∃ k2 ≤ r2, c k1 k2 ≠ 0

noncomputable def binRoot (r a b : ℕ) : ℝ :=
  ((b : ℝ) / (a : ℝ)) ^ ((1 : ℝ) / (r : ℝ))

end OMA494
end

-- PowerSumsDetermine
section
namespace OMA494

open Finset

lemma newton_finset (S : Finset ℂ) (k : ℕ) :
    (k : ℂ) * S.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * S.val.esymm a.1 * psum S a.2 := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : S => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum S ℂ k)
  have hv : (Finset.univ : Finset S).val.map (fun x : S => (x : ℂ)) = S.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val _
  have he : ∀ m, MvPolynomial.aeval (fun x : S => (x : ℂ)) (MvPolynomial.esymm S ℂ m)
      = S.val.esymm m := by
    intro m; rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hv]
  have hp : ∀ m, MvPolynomial.aeval (fun x : S => (x : ℂ)) (MvPolynomial.psum S ℂ m)
      = psum S m := by
    intro m
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, psum]
    exact Finset.sum_coe_sort S (fun a => a ^ m)
  simpa [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, he, hp] using h

theorem power_sums_determine (A B : Finset ℂ) (n : ℕ) (hA : A.card = n) (hB : B.card = n)
    (h : ∀ j, 1 ≤ j → j ≤ n → psum A j = psum B j) : A = B := by

  have hE : ∀ k, k ≤ n → A.val.esymm k = B.val.esymm k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [Multiset.esymm]
      have hA' := newton_finset A k
      have hB' := newton_finset B k
      have hsum : ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * psum A a.2
          = ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * psum B a.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [ih a.1 ha.2 (by omega), h a.2 (by omega) (by omega)]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
      apply mul_left_cancel₀ hk0
      rw [hA', hB', hsum]

  have hpoly : (A.val.map fun t => Polynomial.X - Polynomial.C t).prod
      = (B.val.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    have hcA : Multiset.card A.val = n := hA
    have hcB : Multiset.card B.val = n := hB
    rw [hcA, hcB]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hE j (by simpa [Nat.lt_succ_iff] using hj)]
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Finset.val_inj.mp hroots

end OMA494
end

-- GfsRecursion
section
namespace OMA494

namespace GfsRecursionAux

lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 m, F i = ∑ i ∈ Finset.range m, F (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

def g (n m : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 m, (-1) ^ (i + 1) * (n.choose (m - i) : ℤ)

lemma g_succ (n m : ℕ) : g n (m + 1) = (n.choose m : ℤ) - g n m := by
  unfold g
  rw [sum_Icc_one_eq_range, sum_Icc_one_eq_range, Finset.sum_range_succ']
  have h : ∑ i ∈ Finset.range m, (-1 : ℤ) ^ (i + 1 + 1 + 1) * (n.choose (m + 1 - (i + 1 + 1)) : ℤ)
      = -∑ i ∈ Finset.range m, (-1 : ℤ) ^ (i + 1 + 1) * (n.choose (m - (i + 1)) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 1 - (i + 1 + 1) = m - (i + 1) := by omega
    rw [this, pow_succ]; ring
  rw [h]; simp; ring

lemma key (n m : ℕ) : (m : ℤ) * (n.choose m : ℤ) = (n : ℤ) * g n m := by
  induction m with
  | zero => simp [g]
  | succ m ih =>
    rw [g_succ, mul_sub, ← ih]
    have h := Nat.choose_succ_right_eq n m
    rcases le_or_gt m n with hmn | hmn
    · have h' : ((n.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (n.choose m : ℤ) * ((n : ℤ) - m) := by
        have := congrArg (fun x : ℕ => (x : ℤ)) h
        push_cast [Nat.cast_sub hmn] at this
        exact this
      push_cast; linarith
    · rw [Nat.choose_eq_zero_of_lt hmn, Nat.choose_eq_zero_of_lt (by omega)]; simp

end GfsRecursionAux

open GfsRecursionAux in
theorem gfs_recursion (n j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (k : ℤ) * gfsPoly k n j =
      ∑ i ∈ Finset.Icc 1 k, (-1) ^ (i + 1) *
        ((n : ℤ) * gfsPoly (k - i) n j + (n.choose (k - i) : ℤ) * (i : ℤ) ^ j) := by

  have split : ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) *
        ((n : ℤ) * gfsPoly (k - i) n j + (n.choose (k - i) : ℤ) * (i : ℤ) ^ j)
      = (n : ℤ) * ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) * gfsPoly (k - i) n j
        + ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (k - i) : ℤ)
            * (i : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have e1 : (-1 : ℤ) ^ (i + 1) = (-1) ^ (i - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
      simp [pow_succ]
    have e2 : (i : ℤ) ^ j = (i : ℤ) ^ (j - 1) * i := by
      rw [← pow_succ]; congr 1; omega
    rw [e1, e2]; ring

  have swap : ∑ i ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (i + 1) * gfsPoly (k - i) n j
      = ∑ l ∈ Finset.Icc 1 k, (-1 : ℤ) ^ (l - 1) * (l : ℤ) ^ (j - 1) * g n (k - l) := by
    unfold gfsPoly g
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm' (t' := Finset.Icc 1 k) (s' := fun l => Finset.Icc 1 (k - l))]
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      have : k - i - l = k - l - i := by omega
      rw [this]; ring
    · intro i l; simp only [Finset.mem_Icc]; omega
  rw [split, swap, Finset.mul_sum, gfsPoly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hkey := key n (k - i)
  push_cast [Nat.cast_sub hik] at hkey
  linear_combination (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * hkey
end OMA494
end

-- KSumPowerSum
section
namespace OMA494

namespace KSumAux

open Finset PowerSeries

noncomputable def E (c : ℂ) : ℂ⟦X⟧ := rescale c (exp ℂ)

lemma E_add (a b : ℂ) : E a * E b = E (a + b) := exp_mul_exp_eq_exp_add a b

lemma E_zero : E 0 = 1 := by
  simp [E, constantCoeff_exp]

lemma prod_E {ι : Type*} (t : Finset ι) (c : ι → ℂ) : ∏ i ∈ t, E (c i) = E (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [E_zero]
  | insert x t hx ih => rw [prod_insert hx, sum_insert hx, ih, E_add]

lemma E_pow (c : ℂ) (i : ℕ) : E c ^ i = E ((i : ℂ) * c) := by
  induction i with
  | zero => simp [E_zero]
  | succ i ih => rw [pow_succ, ih, E_add]; push_cast; ring_nf

lemma coeff_E (c : ℂ) (m : ℕ) : coeff m (E c) = c ^ m / (m.factorial : ℂ) := by
  rw [E, coeff_rescale, coeff_exp]; simp [div_eq_mul_inv]

noncomputable def G (A : Finset ℂ) (k : ℕ) : ℂ⟦X⟧ := ∑ S ∈ A.powersetCard k, E (S.sum id)

noncomputable def P (A : Finset ℂ) (i : ℕ) : ℂ⟦X⟧ := ∑ a ∈ A, E ((i : ℂ) * a)

lemma sum_powersetCard_subtype {M : Type*} [AddCommMonoid M] (A : Finset ℂ) (r : ℕ)
    (F : ℂ → M) :
    ∑ t ∈ (univ : Finset A).powersetCard r, F (∑ i ∈ t, (i : ℂ)) =
      ∑ S ∈ A.powersetCard r, F (S.sum id) := by
  have hA : A.powersetCard r = ((univ : Finset A).powersetCard r).map
      (mapEmbedding (Function.Embedding.subtype (· ∈ A))).toEmbedding := by
    rw [← powersetCard_map, univ_eq_attach, attach_map_val]
  rw [hA, sum_map]
  refine sum_congr rfl fun t _ => ?_
  simp [mapEmbedding_apply, sum_map]

lemma newton (A : Finset ℂ) (k : ℕ) :
    (k : ℂ⟦X⟧) * G A k = ∑ i ∈ Icc 1 k, (-1) ^ (i + 1) * G A (k - i) * P A i := by
  have h := congrArg (MvPolynomial.aeval (fun a : A => E (a : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum A ℂ k)
  have hes : ∀ r, MvPolynomial.aeval (fun a : A => E (a : ℂ)) (MvPolynomial.esymm A ℂ r)
      = G A r := by
    intro r
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X, prod_E]
    exact sum_powersetCard_subtype A r E
  have hps : ∀ i, MvPolynomial.aeval (fun a : A => E (a : ℂ)) (MvPolynomial.psum A ℂ i)
      = P A i := by
    intro i
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, E_pow]
    exact sum_coe_sort A (fun a => E ((i : ℂ) * a))
  simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, hes, hps] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_nbij' (fun a => a.2) (fun i => (k - i, i)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    simp only [mem_Icc]; omega
  · intro i hi
    simp only [mem_Icc] at hi
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal]; omega
  · intro a ha
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    ext
    · simp; omega
    · simp
  · intro i _; rfl
  · intro a ha
    obtain ⟨a1, a2⟩ := a
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    obtain ⟨rfl, _⟩ := ha
    simp only
    have e1 : a1 + a2 - a2 = a1 := by omega
    rw [e1]
    have e2 : ((-1 : ℂ⟦X⟧) ^ (a1 + a2 + 1)) * (-1) ^ a1 = (-1) ^ (a2 + 1) := by
      rw [← pow_add, show a1 + a2 + 1 + a1 = 2 * a1 + (a2 + 1) by ring, pow_add, pow_mul,
        neg_one_sq, one_pow, one_mul]
    rw [← e2]; ring

noncomputable def q (A : Finset ℂ) (k m : ℕ) : ℂ := ∑ S ∈ A.powersetCard k, (S.sum id) ^ m

lemma ksumPsum_eq (A : Finset ℂ) (k m : ℕ) : ksumPsum A k m = q A k m := by
  unfold ksumPsum sumMultiset q
  rw [Multiset.map_map]; rfl

lemma coeff_G (A : Finset ℂ) (k m : ℕ) : coeff m (G A k) = q A k m / (m.factorial : ℂ) := by
  simp only [G, map_sum, coeff_E, q, Finset.sum_div]

lemma coeff_P (A : Finset ℂ) (i v : ℕ) :
    coeff v (P A i) = (i : ℂ) ^ v * psum A v / (v.factorial : ℂ) := by
  simp only [P, map_sum, coeff_E, psum, Finset.mul_sum, Finset.sum_div, mul_pow]

lemma coeff_G_zero (A : Finset ℂ) (k : ℕ) : coeff 0 (G A k) = (A.card.choose k : ℂ) := by
  rw [coeff_G, q]; simp [card_powersetCard]

lemma coeff_P_zero (A : Finset ℂ) (i : ℕ) : coeff 0 (P A i) = (A.card : ℂ) := by
  rw [coeff_P]; simp [psum]

lemma G_zero (A : Finset ℂ) : G A 0 = 1 := by
  simp [G, E_zero]

lemma newton_coeff (A : Finset ℂ) (k m : ℕ) :
    (k : ℂ) * coeff m (G A k) = ∑ i ∈ Icc 1 k, (-1) ^ (i + 1) *
      ∑ x ∈ antidiagonal m, coeff x.1 (G A (k - i)) * coeff x.2 (P A i) := by
  have h := congrArg (coeff m) (newton A k)
  rw [← map_natCast (C (R := ℂ)) k, coeff_C_mul] at h
  rw [h, map_sum]
  refine sum_congr rfl fun i _ => ?_
  have : ((-1 : ℂ⟦X⟧) ^ (i + 1)) * G A (k - i) * P A i
      = C ((-1 : ℂ) ^ (i + 1)) * (G A (k - i) * P A i) := by
    simp [mul_assoc]
  rw [this, coeff_C_mul, coeff_mul]

end KSumAux

open KSumAux Finset PowerSeries in
theorem ksum_power_sum (A B : Finset ℂ) (n s j : ℕ) (hA : A.card = n) (hB : B.card = n)
    (hj : 1 ≤ j) (h : ∀ l, 1 ≤ l → l < j → psum A l = psum B l) :
    ksumPsum A s j - ksumPsum B s j = (gfsPoly s n j : ℂ) * (psum A j - psum B j) := by

  have hP : ∀ i v, v < j → coeff v (P A i) = coeff v (P B i) := by
    intro i v hv
    rw [coeff_P, coeff_P]
    rcases Nat.eq_zero_or_pos v with rfl | hv0
    · simp [psum, hA, hB]
    · rw [h v hv0 hv]

  have hlow : ∀ k, ∀ m, m < j → coeff m (G A k) = coeff m (G B k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [G_zero]
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk'
      rw [newton_coeff, newton_coeff]
      refine sum_congr rfl fun i hi => ?_
      have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
      rw [ih (k - i) (by omega) x.1 (by omega), hP i x.2 (by omega)]

  set Δ := psum A j - psum B j with hΔ
  have hmain : ∀ k, coeff j (G A k) - coeff j (G B k) =
      (gfsPoly k n j : ℂ) * Δ / (j.factorial : ℂ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [G_zero, gfsPoly, coeff_one, show j ≠ 0 by omega]
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk'
      rw [mul_sub, newton_coeff, newton_coeff, ← sum_sub_distrib]
      have hrec := congrArg (fun z : ℤ => (z : ℂ)) (gfs_recursion n j k hj hk)
      push_cast at hrec
      have hterm : ∀ i ∈ Icc 1 k,
          (-1 : ℂ) ^ (i + 1) * ∑ x ∈ antidiagonal j, coeff x.1 (G A (k - i)) * coeff x.2 (P A i)
          - (-1 : ℂ) ^ (i + 1) *
            ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i)) * coeff x.2 (P B i)
          = (-1 : ℂ) ^ (i + 1) * ((n : ℂ) * (gfsPoly (k - i) n j : ℂ) +
              (n.choose (k - i) : ℂ) * (i : ℂ) ^ j) * Δ / (j.factorial : ℂ) := by
        intro i hi
        have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
        have hsplit : ∑ x ∈ antidiagonal j, coeff x.1 (G A (k - i)) * coeff x.2 (P A i)
            - ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i)) * coeff x.2 (P B i)
            = ∑ x ∈ antidiagonal j, (coeff x.1 (G A (k - i)) - coeff x.1 (G B (k - i)))
                * coeff x.2 (P A i)
              + ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i))
                * (coeff x.2 (P A i) - coeff x.2 (P B i)) := by
          rw [← sum_add_distrib, ← sum_sub_distrib]
          refine sum_congr rfl fun x _ => ?_
          ring
        have h1 : ∑ x ∈ antidiagonal j, (coeff x.1 (G A (k - i)) - coeff x.1 (G B (k - i)))
            * coeff x.2 (P A i) = (coeff j (G A (k - i)) - coeff j (G B (k - i))) * n := by
          rw [sum_eq_single (j, 0)]
          · simp [coeff_P_zero, hA]
          · intro x hx hne
            have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
            have : x.1 < j := by
              rcases Nat.lt_or_ge x.1 j with h' | h'
              · exact h'
              · exact absurd (Prod.ext (by simp; omega) (by simp; omega)) hne
            rw [hlow _ _ this, sub_self, zero_mul]
          · intro hn; exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn
        have h2 : ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i))
            * (coeff x.2 (P A i) - coeff x.2 (P B i))
            = (n.choose (k - i) : ℂ) * ((i : ℂ) ^ j * Δ / (j.factorial : ℂ)) := by
          rw [sum_eq_single (0, j)]
          · simp only [coeff_G_zero, hB, coeff_P, hΔ]
            ring
          · intro x hx hne
            have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
            have : x.2 < j := by
              rcases Nat.lt_or_ge x.2 j with h' | h'
              · exact h'
              · exact absurd (Prod.ext (by simp; omega) (by simp; omega)) hne
            rw [hP _ _ this, sub_self, mul_zero]
          · intro hn; exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn
        rw [← mul_sub, hsplit, h1, h2, ih (k - i) (by omega)]
        ring
      rw [sum_congr rfl hterm]
      rw [← sum_div, ← sum_mul, mul_div_assoc, mul_div_assoc, ← mul_assoc]
      congr 1
      rw [hrec]
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hs := hmain s
  rw [coeff_G, coeff_G, ← sub_div, div_left_inj' hfac] at hs
  rw [ksumPsum_eq, ksumPsum_eq, hs]

end OMA494
end

-- Kruyt
section
namespace OMA494

open Complex

lemma sumMultiset_of_card_eq (C : Finset ℂ) (k : ℕ) (hC : C.card = k) :
    sumMultiset C k = {C.sum id} := by
  subst hC
  unfold sumMultiset
  rw [Finset.powersetCard_self]
  rfl

theorem kruyt_counterexample : ∀ k > 2, ¬Erdos494Unique k k := by
  intro k hk hU
  let c : ℕ → ℂ := fun i => (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)
  let f : ℕ → ℂ := fun i => (i : ℂ)
  let g : ℕ → ℂ := fun i => (i : ℂ) + I * c i
  have hcre : ∀ i, (I * c i).re = 0 := by
    intro i
    simp only [c]
    split_ifs <;> simp
  have hf : Function.Injective f := by
    intro a b h
    simp only [f] at h
    exact_mod_cast h
  have hg : Function.Injective g := by
    intro a b h
    have h2 := congrArg Complex.re h
    simp only [g, Complex.add_re, hcre, add_zero, Complex.natCast_re] at h2
    exact_mod_cast h2
  set A := (Finset.range k).image f with hAdef
  set B := (Finset.range k).image g with hBdef
  have hA : A.card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_range]
  have hB : B.card = k := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_range]
  have hc : ∑ i ∈ Finset.range k, c i = 0 := by
    simp only [c]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have h1 : 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    simp [h0, h1]
  have hsum : A.sum id = B.sum id := by
    rw [Finset.sum_image (fun a _ b _ h => hf h), Finset.sum_image (fun a _ b _ h => hg h)]
    simp only [id, g, f]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc, mul_zero, add_zero]
  have hAB : A = B := hU A B hA hB (by
    rw [sumMultiset_of_card_eq A k hA, sumMultiset_of_card_eq B k hB, hsum])
  have h0A : (0 : ℂ) ∈ A := by
    rw [hAdef, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr (by omega), by simp [f]⟩
  have h0B : (0 : ℂ) ∉ B := by
    rw [hBdef, Finset.mem_image]
    rintro ⟨i, _, hi⟩
    have hre := congrArg Complex.re hi
    simp only [g, Complex.add_re, hcre, add_zero, Complex.natCast_re, Complex.zero_re] at hre
    have hi0 : i = 0 := by exact_mod_cast hre
    subst hi0
    have him := congrArg Complex.im hi
    simp [g, c] at him
  exact h0B (hAB ▸ h0A)

end OMA494
end

-- TaoNeg
section
namespace OMA494

open Finset

theorem sumMultiset_neg_of_sum_zero (A : Finset ℂ) (k : ℕ) (hc : A.card = 2 * k)
    (hs : A.sum id = 0) :
    sumMultiset (A.map (Equiv.neg ℂ).toEmbedding) k = sumMultiset A k := by
  unfold sumMultiset
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map]
  have key : ∀ t ∈ (A.powersetCard k).val,
      ((fun s : Finset ℂ => s.sum id) ∘
        (Finset.mapEmbedding (Equiv.neg ℂ).toEmbedding).toEmbedding) t = (A \ t).sum id := by
    intro t ht
    rw [Finset.mem_val, Finset.mem_powersetCard] at ht
    have h1 := Finset.sum_sdiff ht.1 (f := id)
    rw [hs] at h1
    simp only [Function.comp, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply,
      Finset.sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, id]
    rw [Finset.sum_neg_distrib]
    simp only [id] at h1
    linear_combination -h1
  rw [Multiset.map_congr rfl key]
  have hperm : (A.powersetCard k).val.map (fun t => A \ t) = (A.powersetCard k).val := by
    rw [Multiset.Nodup.ext]
    · intro u
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_powersetCard]
      constructor
      · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
        refine ⟨Finset.sdiff_subset, ?_⟩
        rw [Finset.card_sdiff_of_subset ht1, hc, ht2]; omega
      · rintro ⟨hu1, hu2⟩
        refine ⟨A \ u, ⟨Finset.sdiff_subset, ?_⟩, Finset.sdiff_sdiff_eq_self hu1⟩
        rw [Finset.card_sdiff_of_subset hu1, hc, hu2]; omega
    · refine Multiset.Nodup.map_on ?_ (A.powersetCard k).nodup
      intro x hx y hy hxy
      rw [Finset.mem_val, Finset.mem_powersetCard] at hx hy
      rw [← Finset.sdiff_sdiff_eq_self hx.1, ← Finset.sdiff_sdiff_eq_self hy.1]
      exact congrArg (A \ ·) hxy
    · exact (A.powersetCard k).nodup
  calc ((A.powersetCard k).val.map fun t => (A \ t).sum id)
      = (((A.powersetCard k).val.map fun t => A \ t).map fun s => s.sum id) := by
        rw [Multiset.map_map]; rfl
    _ = _ := by rw [hperm]

theorem tao_counterexample : ∀ k > 2, ¬Erdos494Unique k (2 * k) := by
  intro k hk hU
  set I : Finset ℕ := Finset.Icc 1 (2 * k - 1) with hI
  set N : ℕ := ∑ i ∈ I, i with hN
  set B : Finset ℂ := I.image (fun i : ℕ => (i : ℂ)) with hB
  set A : Finset ℂ := insert (-(N : ℂ)) B with hA
  have hinj : Function.Injective (fun i : ℕ => (i : ℂ)) := Nat.cast_injective
  have hBcard : B.card = 2 * k - 1 := by
    rw [hB, Finset.card_image_of_injective _ hinj, hI, Nat.card_Icc]; omega
  have hmemB : ∀ z ∈ B, 0 < z.re := by
    intro z hz
    rw [hB, Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    rw [hI, Finset.mem_Icc] at hi
    simp only [Complex.natCast_re, Nat.cast_pos]; omega
  have hNpos : 2 ≤ N := by
    rw [hN]
    have h2 : (2 : ℕ) ∈ I := by rw [hI, Finset.mem_Icc]; omega
    exact Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) h2
  have hnotin : -(N : ℂ) ∉ B := by
    intro h
    have := hmemB _ h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  have hAcard : A.card = 2 * k := by
    rw [hA, Finset.card_insert_of_notMem hnotin, hBcard]; omega
  have hBsum : B.sum id = (N : ℂ) := by
    rw [hB, Finset.sum_image (fun x _ y _ h => hinj h), hN]; simp
  have hAsum : A.sum id = 0 := by
    rw [hA, Finset.sum_insert hnotin, hBsum]; simp
  have hneg := sumMultiset_neg_of_sum_zero A k hAcard hAsum
  have hAcard' : (A.map (Equiv.neg ℂ).toEmbedding).card = 2 * k := by
    rw [Finset.card_map, hAcard]
  have heq := hU _ _ hAcard' hAcard hneg

  have h1 : (1 : ℂ) ∈ A := by
    rw [hA]; apply Finset.mem_insert_of_mem
    rw [hB, Finset.mem_image]
    exact ⟨1, by rw [hI, Finset.mem_Icc]; omega, by simp⟩
  have hm1 : (-1 : ℂ) ∈ A.map (Equiv.neg ℂ).toEmbedding := by
    rw [Finset.mem_map]; exact ⟨1, h1, by simp⟩
  rw [heq, hA, Finset.mem_insert] at hm1
  rcases hm1 with h | h
  · have : (N : ℂ) = 1 := by linear_combination h
    have : N = 1 := by exact_mod_cast this
    omega
  · have := hmemB _ h
    norm_num at this

end OMA494
end

-- Divisibility
section
namespace OMA494

lemma dvd_factorial_mul_choose (n t m : ℕ) (hm1 : 1 ≤ m) (hmt : m ≤ t) :
    n ∣ t.factorial * n.choose m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hdv : m' + 1 ∣ t.factorial := Nat.dvd_factorial (by omega) hmt
  obtain ⟨k, hk⟩ := hdv
  rcases n with _ | n'
  · simp
  · have h : (n' + 1) * n'.choose m' = (n' + 1).choose (m' + 1) * (m' + 1) :=
      Nat.add_one_mul_choose_eq n' m'

    refine ⟨n'.choose m' * k, ?_⟩
    rw [hk]
    calc (m' + 1) * k * (n' + 1).choose (m' + 1)
        = (n' + 1).choose (m' + 1) * (m' + 1) * k := by ring
      _ = (n' + 1) * n'.choose m' * k := by rw [← h]
      _ = (n' + 1) * (n'.choose m' * k) := by ring

theorem gfs_dvd (s n j : ℕ) (hs : 1 ≤ s) (_hn : 0 < n) (h : gfsPoly s n j = 0) :
    n ∣ (s - 1).factorial * s ^ (j - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  unfold gfsPoly at h
  rw [Finset.sum_Icc_succ_top (by omega)] at h
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one,
    Nat.add_sub_cancel] at h
  have hrest : (n : ℤ) ∣ (t.factorial : ℤ) *
      ∑ i ∈ Finset.Icc 1 t, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 1 - i) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have := dvd_factorial_mul_choose n t (t + 1 - i) (by omega) (by omega)
    have hz : (n : ℤ) ∣ (t.factorial : ℤ) * (n.choose (t + 1 - i) : ℤ) := by exact_mod_cast this
    exact Dvd.dvd.trans hz ⟨(-1) ^ (i - 1) * (i : ℤ) ^ (j - 1), by ring⟩
  have hlast : (t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1)) =
      -((t.factorial : ℤ) *
        ∑ i ∈ Finset.Icc 1 t, (-1) ^ (i - 1) * (i : ℤ) ^ (j - 1) *
          (n.choose (t + 1 - i) : ℤ)) := by
    have h' := congrArg (fun x => (t.factorial : ℤ) * x) h
    simp only [mul_zero, mul_add] at h'
    linarith
  have h1 : (n : ℤ) ∣ (t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1)) := by
    rw [hlast]; exact hrest.neg_right
  have h2 : (n : ℤ) ∣ ((t.factorial * (t + 1) ^ (j - 1) : ℕ) : ℤ) := by
    have h3 := Dvd.dvd.mul_left h1 ((-1) ^ t)
    have e : (-1 : ℤ) ^ t * ((t.factorial : ℤ) * ((-1) ^ t * ((t + 1 : ℕ) : ℤ) ^ (j - 1))) =
        ((t.factorial * (t + 1) ^ (j - 1) : ℕ) : ℤ) := by
      push_cast
      have : ((-1 : ℤ) ^ t) * (-1) ^ t = 1 := by rw [← mul_pow]; norm_num
      linear_combination ((t.factorial : ℤ) * ((t : ℤ) + 1) ^ (j - 1)) * this
    rwa [e] at h3
  exact_mod_cast h2

end OMA494
end

-- BoundedJ
section
namespace OMA494

private lemma choose_mono_low (n r : ℕ) :
    ∀ k : ℕ, r + k ≤ n / 2 → n.choose r ≤ n.choose (r + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : n.choose (r + k) ≤ n.choose (r + k + 1) :=
      Nat.choose_le_succ_of_lt_half_left (by omega)
    calc n.choose r ≤ n.choose (r + k) := h1
      _ ≤ n.choose (r + (k + 1)) := by rw [← add_assoc]; exact h2

theorem bounded_j (s : ℕ) (hs : 2 ≤ s) (J : ℕ) :
    ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → j < J → gfsPoly s n j ≠ 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  set K : ℕ := (t + 2) ^ J with hK
  refine ⟨2 * (t + 2) + (t + 1) * (t + 1) * K + t + 1, ?_⟩
  intro n j hn hj

  unfold gfsPoly
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ t + 2)]
  have hfirst : ((-1 : ℤ) ^ (1 - 1) * ((1 : ℕ) : ℤ) ^ (j - 1) * (n.choose (t + 2 - 1) : ℤ))
      = (n.choose (t + 1) : ℤ) := by
    simp
  rw [hfirst]
  set R := ∑ i ∈ Finset.Ioc 1 (t + 2),
    (-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ) with hR

  have hterm : ∀ i ∈ Finset.Ioc 1 (t + 2),
      |(-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ)|
        ≤ (K : ℤ) * (n.choose t : ℤ) := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hpow : i ^ (j - 1) ≤ K := by
      calc i ^ (j - 1) ≤ (t + 2) ^ (j - 1) := Nat.pow_le_pow_left hi.2 _
        _ ≤ (t + 2) ^ J := Nat.pow_le_pow_right (by omega) (by omega)
    have hch : n.choose (t + 2 - i) ≤ n.choose t := by
      have := choose_mono_low n (t + 2 - i) (i - 2) (by omega)
      have e : t + 2 - i + (i - 2) = t := by omega
      rwa [e] at this
    have : i ^ (j - 1) * n.choose (t + 2 - i) ≤ K * n.choose t := Nat.mul_le_mul hpow hch
    exact_mod_cast this
  have hRle : |R| ≤ ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) := by
    calc |R| ≤ ∑ i ∈ Finset.Ioc 1 (t + 2),
          |(-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (j - 1) * (n.choose (t + 2 - i) : ℤ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Ioc 1 (t + 2), (K : ℤ) * (n.choose t : ℤ) := Finset.sum_le_sum hterm
      _ = ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; congr 2

  have hlead : (t + 1) * (K * n.choose t) < n.choose (t + 1) := by
    have hrec := Nat.choose_succ_right_eq n t
    have hpos : 0 < n.choose t := Nat.choose_pos (by omega)
    have hnt : (t + 1) * (t + 1) * K < n - t := by omega
    have : (t + 1) * (K * n.choose t) * (t + 1) < n.choose (t + 1) * (t + 1) := by
      rw [hrec]
      calc (t + 1) * (K * n.choose t) * (t + 1)
          = n.choose t * ((t + 1) * (t + 1) * K) := by ring
        _ < n.choose t * (n - t) := Nat.mul_lt_mul_of_pos_left hnt hpos
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  have hlead' : ((t + 1 : ℕ) : ℤ) * ((K : ℤ) * (n.choose t : ℤ)) < (n.choose (t + 1) : ℤ) := by
    exact_mod_cast hlead
  intro h0
  have : R = -(n.choose (t + 1) : ℤ) := by linarith
  rw [this, abs_neg, abs_of_nonneg (by positivity)] at hRle
  linarith

end OMA494
end

-- TwoTermApprox
section
namespace OMA494

namespace TwoTermApprox

open Finset

lemma choose_lc (n r : ℕ) : n.choose (r + 2) * n.choose r ≤ n.choose (r + 1) ^ 2 := by
  rcases Nat.lt_or_ge r n with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = r + t + 1 := ⟨n - r - 1, by omega⟩
    have h1 := Nat.choose_succ_right_eq (r + t + 1) r
    have h2 := Nat.choose_succ_right_eq (r + t + 1) (r + 1)
    have e1 : r + t + 1 - r = t + 1 := by omega
    have e2 : r + t + 1 - (r + 1) = t := by omega
    rw [e1] at h1
    rw [e2] at h2
    set a := (r + t + 1).choose r
    set b := (r + t + 1).choose (r + 1)
    set c := (r + t + 1).choose (r + 1 + 1)
    have hpos : 0 < (r + 2) * (t + 1) := by positivity
    have key : c * a * ((r + 2) * (t + 1)) ≤ b ^ 2 * ((r + 2) * (t + 1)) := by
      calc c * a * ((r + 2) * (t + 1)) = (c * (r + 1 + 1)) * (a * (t + 1)) := by ring
        _ = (b * t) * (b * (r + 1)) := by rw [h2, h1]
        _ = b ^ 2 * (t * (r + 1)) := by ring
        _ ≤ b ^ 2 * ((r + 2) * (t + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
    exact Nat.le_of_mul_le_mul_right key hpos
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < r + 2)]
    simp

lemma far_up (T : ℕ → ℝ) (s m : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ μ * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hm1 : 1 ≤ m) (hmax : ∀ i, T i ≤ T m) :
    ∀ d, T (m + d + 2) ≤ μ * T m := by
  have aux : ∀ d, T (m + d + 1) ≤ T (m + d) → T (m + d + 2) ≤ μ * T (m + d + 1) := by
    intro d hd
    rcases (hnn (m + d)).lt_or_eq with h | h
    · have h1 := hlc (m + d)
      have h2 : μ * T (m + d + 1) ^ 2 ≤ μ * T (m + d + 1) * T (m + d) := by
        rw [sq, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hd (mul_nonneg hμ0 (hnn _))
      have h3 : T (m + d) * T (m + d + 2) ≤ T (m + d) * (μ * T (m + d + 1)) := by
        have : m + d + 1 + 1 = m + d + 2 := rfl
        nlinarith
      exact le_of_mul_le_mul_left h3 h
    · have hs : ¬ (m + d ≤ s) := by
        intro hc
        have := (hpos (m + d)).2 ⟨by omega, hc⟩
        linarith
      have h4 : ¬ (0 < T (m + d + 2)) := by
        rw [hpos]; omega
      push Not at h4
      linarith [mul_nonneg hμ0 (hnn (m + d + 1))]
  have mono : ∀ d, T (m + d + 1) ≤ T (m + d) := by
    intro d
    induction d with
    | zero => simpa using hmax (m + 1)
    | succ d ih =>
      have h5 := aux d ih
      have e1 : m + (d + 1) + 1 = m + d + 2 := by ring
      have e2 : m + (d + 1) = m + d + 1 := by ring
      rw [e1, e2]
      nlinarith [hnn (m + d + 1)]
  intro d
  calc T (m + d + 2) ≤ μ * T (m + d + 1) := aux d (mono d)
    _ ≤ μ * T m := mul_le_mul_of_nonneg_left (hmax _) hμ0

lemma far (T : ℕ → ℝ) (s m : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ μ * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hm1 : 1 ≤ m) (hms : m ≤ s)
    (hmax : ∀ i, T i ≤ T m) :
    ∀ i, (i + 2 ≤ m ∨ m + 2 ≤ i) → T i ≤ μ * T m := by
  intro i hi
  rcases hi with hi | hi
  ·
    set U : ℕ → ℝ := fun i => T (s + 1 - i) with hU
    have hT0 : T 0 = 0 := by
      have h := hpos 0
      have : ¬ (0 < T 0) := by rw [h]; omega
      linarith [hnn 0]
    have hUnn : ∀ i, 0 ≤ U i := fun i => hnn _
    have hUpos : ∀ i, 0 < U i ↔ (1 ≤ i ∧ i ≤ s) := by
      intro i; simp only [hU]; rw [hpos]; omega
    have hUlc : ∀ k, U k * U (k + 2) ≤ μ * U (k + 1) ^ 2 := by
      intro k
      simp only [hU]
      by_cases hk : k + 2 ≤ s + 1
      · have := hlc (s + 1 - (k + 2))
        have e1 : s + 1 - (k + 2) + 2 = s + 1 - k := by omega
        have e2 : s + 1 - (k + 2) + 1 = s + 1 - (k + 1) := by omega
        rw [e1, e2] at this
        linarith
      · have : s + 1 - (k + 2) = 0 := by omega
        rw [this, hT0, mul_zero]
        exact mul_nonneg hμ0 (sq_nonneg _)
    have hUmax : ∀ i, U i ≤ U (s + 1 - m) := by
      intro i; simp only [hU]
      have : s + 1 - (s + 1 - m) = m := by omega
      rw [this]; exact hmax _
    have := far_up U s (s + 1 - m) μ hμ0 hμ1 hUnn hUlc hUpos (by omega) hUmax (m - i - 2)
    simp only [hU] at this
    have e1 : s + 1 - (s + 1 - m + (m - i - 2) + 2) = i := by omega
    have e2 : s + 1 - (s + 1 - m) = m := by omega
    rw [e1, e2] at this
    exact this
  · have := far_up T s m μ hμ0 hμ1 hnn hlc hpos hm1 hmax (i - m - 2)
    have e : m + (i - m - 2) + 2 = i := by omega
    rw [e] at this
    exact this

lemma core (T : ℕ → ℝ) (s : ℕ) (θk : ℝ) (hθ0 : 0 ≤ θk) (he : ((s : ℝ) + 1) * θk ≤ 1 / 2)
    (hnn : ∀ i, 0 ≤ T i) (hlc : ∀ k, T k * T (k + 2) ≤ θk ^ 2 * T (k + 1) ^ 2)
    (hpos : ∀ i, 0 < T i ↔ (1 ≤ i ∧ i ≤ s)) (hs : 1 ≤ s)
    (hsum : ∑ i ∈ Icc 1 s, (-1 : ℝ) ^ (i - 1) * T i = 0) :
    ∃ i ∈ Icc 1 (s - 1), |T i - T (i + 1)| ≤ 2 * (((s : ℝ) + 1) * θk) * T (i + 1) := by
  have hSne : (Icc 1 s).Nonempty := ⟨1, by simp; omega⟩
  obtain ⟨m, hmS, hmmax⟩ := Finset.exists_max_image (Icc 1 s) T hSne
  have hmS' := Finset.mem_Icc.1 hmS
  have hM : 0 < T m := (hpos m).2 hmS'
  have hmax : ∀ i, T i ≤ T m := by
    intro i
    by_cases hi : i ∈ Icc 1 s
    · exact hmmax i hi
    · have : ¬ (0 < T i) := by rw [hpos]; simpa using hi
      linarith [hnn i]
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hθ1 : θk ≤ 1 := by nlinarith
  set μ := θk ^ 2 with hμ
  have hμ0 : 0 ≤ μ := sq_nonneg _
  have hμ1 : μ ≤ 1 := by rw [hμ]; nlinarith
  have hμθ : μ ≤ θk := by rw [hμ]; nlinarith
  have hfar := far T s m μ hμ0 hμ1 hnn hlc hpos hmS'.1 hmS'.2 hmax

  have hsplit := Finset.add_sum_erase (Icc 1 s) (fun i => (-1 : ℝ) ^ (i - 1) * T i) hmS
  rw [hsum] at hsplit
  have hrest : |∑ i ∈ (Icc 1 s).erase m, (-1 : ℝ) ^ (i - 1) * T i| = T m := by
    have : ∑ i ∈ (Icc 1 s).erase m, (-1 : ℝ) ^ (i - 1) * T i = -((-1 : ℝ) ^ (m - 1) * T m) := by
      linarith
    rw [this, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hM]
  have hle1 : T m ≤ ∑ i ∈ (Icc 1 s).erase m, T i := by
    rw [← hrest]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (hnn i)]
  set A := T (m - 1) with hA
  set B := T (m + 1) with hB
  have hle2 : ∑ i ∈ (Icc 1 s).erase m, T i ≤ ∑ i ∈ (Icc 1 s).erase m,
      ((if i = m - 1 then A else 0) + (if i = m + 1 then B else 0) + μ * T m) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_erase.1 hi
    have hi'' := Finset.mem_Icc.1 hi'.2
    have hμM : 0 ≤ μ * T m := mul_nonneg hμ0 hM.le
    split_ifs with h1 h2 h2
    · omega
    · rw [h1]; linarith
    · rw [h2]; linarith
    · have := hfar i (by omega)
      linarith
  have hA0 : 0 ≤ A := hnn _
  have hB0 : 0 ≤ B := hnn _
  have hle3 : ∑ i ∈ (Icc 1 s).erase m,
      ((if i = m - 1 then A else 0) + (if i = m + 1 then B else 0) + μ * T m) ≤
      A + B + s * (μ * T m) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      Finset.sum_const, nsmul_eq_mul]
    have hc : (((Icc 1 s).erase m).card : ℝ) ≤ s := by
      have := Finset.card_erase_le (s := Icc 1 s) (a := m)
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have h1 : (if m - 1 ∈ (Icc 1 s).erase m then A else 0) ≤ A := by split_ifs <;> linarith
    have h2 : (if m + 1 ∈ (Icc 1 s).erase m then B else 0) ≤ B := by split_ifs <;> linarith
    have h3 : (((Icc 1 s).erase m).card : ℝ) * (μ * T m) ≤ s * (μ * T m) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hμ0 hM.le)
    linarith
  have hkey : T m ≤ A + B + s * (μ * T m) := by linarith
  have hAB : A * B ≤ μ * T m ^ 2 := by
    have := hlc (m - 1)
    have e1 : m - 1 + 2 = m + 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e1, e2] at this
    exact this
  have hAM : A ≤ T m := hmax _
  have hBM : B ≤ T m := hmax _
  have hsμ : (s : ℝ) * (μ * T m) ≤ s * (θk * T m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hμθ hM.le) hs0
  have he0 : 0 ≤ ((s : ℝ) + 1) * θk := by positivity
  rcases le_or_gt A B with hle | hlt
  ·
    have hAsmall : A ≤ θk * T m := by
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ θk * T m := mul_nonneg hθ0 hM.le
      have : (θk * T m) * (θk * T m) < A * A := mul_self_lt_mul_self h0 hc
      nlinarith
    have hBbig : T m - B ≤ ((s : ℝ) + 1) * θk * T m := by nlinarith
    have hB2 : T m ≤ 2 * B := by nlinarith
    have hBpos : 0 < B := by linarith
    have hm1s : 1 ≤ m + 1 ∧ m + 1 ≤ s := (hpos (m + 1)).1 hBpos
    refine ⟨m, Finset.mem_Icc.2 ⟨hmS'.1, by omega⟩, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    calc T m - B ≤ ((s : ℝ) + 1) * θk * T m := hBbig
      _ ≤ ((s : ℝ) + 1) * θk * (2 * B) := mul_le_mul_of_nonneg_left hB2 he0
      _ = 2 * (((s : ℝ) + 1) * θk) * B := by ring
  ·
    have hBsmall : B ≤ θk * T m := by
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ θk * T m := mul_nonneg hθ0 hM.le
      have : (θk * T m) * (θk * T m) < B * B := mul_self_lt_mul_self h0 hc
      nlinarith
    have hAbig : T m - A ≤ ((s : ℝ) + 1) * θk * T m := by nlinarith
    have hApos : 0 < A := by nlinarith
    have hm1s : 1 ≤ m - 1 ∧ m - 1 ≤ s := (hpos (m - 1)).1 hApos
    refine ⟨m - 1, Finset.mem_Icc.2 ⟨hm1s.1, by omega⟩, ?_⟩
    have e : m - 1 + 1 = m := by omega
    rw [e, abs_of_nonpos (by linarith)]
    calc -(A - T m) = T m - A := by ring
      _ ≤ ((s : ℝ) + 1) * θk * T m := hAbig
      _ ≤ 2 * (((s : ℝ) + 1) * θk) * T m := by nlinarith

lemma constants (S : ℝ) (hS3 : 3 ≤ S) :
    ∃ θ q α : ℝ, 0 ≤ θ ∧ 1 < q ∧ q < S ∧ 0 < α ∧ α < 1 ∧ θ * q ≤ α ∧
      (∀ i : ℝ, 1 ≤ i → i + 1 ≤ S → i * q ≤ α * (i + 1)) ∧
      (∀ k : ℝ, 1 ≤ k → k + 2 ≤ S → k * (k + 2) ≤ θ ^ 2 * (k + 1) ^ 2) := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * S ^ 2) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (2 * (S - 1) ^ 2) := ⟨_, rfl⟩
  have hS0 : 0 < S := by linarith
  have hS1 : 0 < S - 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεS : ε * (2 * S ^ 2) = 1 := by rw [hε]; field_simp
  have hS2 : 9 ≤ S ^ 2 := by nlinarith
  have hε1 : ε ≤ 1 / 18 := by nlinarith
  have hx0 : 0 < x := by rw [hx]; positivity
  have hxS : x * (2 * (S - 1) ^ 2) = 1 := by rw [hx]; field_simp
  have hS12 : 4 ≤ (S - 1) ^ 2 := by nlinarith
  have hx1 : x ≤ 1 / 8 := by nlinarith
  have hεx : ε ≤ x := by
    have h1 : (S - 1) ^ 2 ≤ S ^ 2 := by nlinarith
    have h2 : x * (2 * (S - 1) ^ 2) ≤ x * (2 * S ^ 2) := by nlinarith
    have h3 : ε * (2 * S ^ 2) ≤ x * (2 * S ^ 2) := by linarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  refine ⟨1 - x, 1 + ε / 2, (1 + ε / 2) * (1 - ε), by linarith, by linarith, by linarith,
    by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
  · intro i hi1 hiS
    have h1 : i + 1 ≤ 2 * S ^ 2 := by nlinarith
    have h2 : ε * (i + 1) ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε / 2)
      (by linarith : (0 : ℝ) ≤ 1 - ε * (i + 1))]
  · intro k hk1 hk2
    have ht : (k + 1) ^ 2 ≤ (S - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h1 : 2 * x * (k + 1) ^ 2 ≤ 1 := by nlinarith
    have hθ2 : 1 - 2 * x ≤ (1 - x) ^ 2 := by nlinarith [sq_nonneg x]
    have h2 : (1 - 2 * x) * (k + 1) ^ 2 ≤ (1 - x) ^ 2 * (k + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)
    nlinarith

noncomputable def Tf (s n κ : ℕ) (i : ℕ) : ℝ :=
  if 1 ≤ i ∧ i ≤ s then (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) else 0

lemma Tf_in (s n κ i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ s) :
    Tf s n κ i = (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) := by
  unfold Tf; rw [if_pos ⟨h1, h2⟩]

lemma Tf_out (s n κ i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ s)) : Tf s n κ i = 0 := by
  unfold Tf; rw [if_neg h]

lemma choose_pos_real (s n r : ℕ) (hn : s < n) (hr : r ≤ s) : (0 : ℝ) < (n.choose r : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega)

lemma Tf_nonneg (s n κ : ℕ) : ∀ i, 0 ≤ Tf s n κ i := by
  intro i
  by_cases h : 1 ≤ i ∧ i ≤ s
  · rw [Tf_in s n κ i h.1 h.2]; positivity
  · rw [Tf_out s n κ i h]

lemma Tf_pos (s n κ : ℕ) (hn : s < n) : ∀ i, 0 < Tf s n κ i ↔ (1 ≤ i ∧ i ≤ s) := by
  intro i
  constructor
  · intro h
    by_contra hc
    rw [Tf_out s n κ i hc] at h
    exact lt_irrefl _ h
  · intro h
    rw [Tf_in s n κ i h.1 h.2]
    have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast h.1
    have := choose_pos_real s n (s - i) hn (Nat.sub_le _ _)
    positivity

lemma Tf_lc (s n κ : ℕ) (θ : ℝ)
    (hθ : ∀ k : ℝ, 1 ≤ k → k + 2 ≤ (s : ℝ) → k * (k + 2) ≤ θ ^ 2 * (k + 1) ^ 2) :
    ∀ k, Tf s n κ k * Tf s n κ (k + 2) ≤ (θ ^ κ) ^ 2 * Tf s n κ (k + 1) ^ 2 := by
  intro k
  by_cases hk : 1 ≤ k ∧ k + 2 ≤ s
  · rw [Tf_in s n κ k hk.1 (by omega), Tf_in s n κ (k + 2) (by omega) hk.2,
      Tf_in s n κ (k + 1) (by omega) (by omega)]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk2 : (k : ℝ) + 2 ≤ (s : ℝ) := by exact_mod_cast hk.2
    have hpow := hθ k hk1 hk2
    have hpowk : ((k : ℝ) * ((k : ℝ) + 2)) ^ κ ≤ (θ ^ 2 * ((k : ℝ) + 1) ^ 2) ^ κ :=
      pow_le_pow_left₀ (by positivity) hpow κ
    have hb := choose_lc n (s - k - 2)
    have e1 : s - k - 2 + 2 = s - k := by omega
    have e2 : s - k - 2 + 1 = s - (k + 1) := by omega
    have e3 : s - k - 2 = s - (k + 2) := by omega
    rw [e1, e2, e3] at hb
    have hbR : (n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ) ≤
        (n.choose (s - (k + 1)) : ℝ) ^ 2 := by exact_mod_cast hb
    have hc0 : (0 : ℝ) ≤ (n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ) := by positivity
    have hk2' : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have hk1' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk2', hk1']
    calc (k : ℝ) ^ κ * (n.choose (s - k) : ℝ) * (((k : ℝ) + 2) ^ κ * (n.choose (s - (k + 2)) : ℝ))
        = ((k : ℝ) * ((k : ℝ) + 2)) ^ κ *
            ((n.choose (s - k) : ℝ) * (n.choose (s - (k + 2)) : ℝ)) := by rw [mul_pow]; ring
      _ ≤ (θ ^ 2 * ((k : ℝ) + 1) ^ 2) ^ κ * ((n.choose (s - (k + 1)) : ℝ) ^ 2) :=
          mul_le_mul hpowk hbR hc0 (by positivity)
      _ = (θ ^ κ) ^ 2 * (((k : ℝ) + 1) ^ κ * (n.choose (s - (k + 1)) : ℝ)) ^ 2 := by
          have p1 : (θ ^ 2) ^ κ = (θ ^ κ) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
          have p2 : (((k : ℝ) + 1) ^ 2) ^ κ = (((k : ℝ) + 1) ^ κ) ^ 2 := by
            rw [← pow_mul, ← pow_mul, mul_comm]
          rw [mul_pow, p1, p2]; ring
  · have h0 : Tf s n κ k * Tf s n κ (k + 2) = 0 := by
      by_cases h1 : 1 ≤ k
      · rw [Tf_out s n κ (k + 2) (by omega), mul_zero]
      · rw [Tf_out s n κ k (by omega), zero_mul]
    rw [h0]; positivity

lemma Tf_sum (s n j : ℕ) (hf : gfsPoly s n j = 0) :
    ∑ i ∈ Icc 1 s, (-1 : ℝ) ^ (i - 1) * Tf s n (j - 1) i = 0 := by
  have hf' : ((gfsPoly s n j : ℤ) : ℝ) = 0 := by rw [hf]; simp
  unfold gfsPoly at hf'
  push_cast at hf'
  rw [← hf']
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Icc.1 hi
  rw [Tf_in s n (j - 1) i hi'.1 hi'.2]
  ring

lemma conversion (s n κ i : ℕ) (hn : s < n) (hi1 : 1 ≤ i) (his : i + 1 ≤ s) (e : ℝ)
    (hclose : |Tf s n κ i - Tf s n κ (i + 1)| ≤ 2 * e * Tf s n κ (i + 1)) :
    |(n : ℝ) * (i : ℝ) ^ κ - ((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ| ≤
      2 * e * (((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ) + (s : ℝ) * (i : ℝ) ^ κ := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((s : ℝ) - i) * ((i : ℝ) + 1) ^ κ := ⟨_, rfl⟩
  rw [← hYdef]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (n.choose (s - (i + 1)) : ℝ) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact choose_pos_real s n _ hn (by omega)
  have hIs : (i : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast his
  have hpas : (n.choose (s - i) : ℝ) * ((s : ℝ) - i) = c * ((n : ℝ) - s + i + 1) := by
    have h := Nat.choose_succ_right_eq n (s - (i + 1))
    have e1 : s - (i + 1) + 1 = s - i := by omega
    rw [e1] at h
    have h' : ((n.choose (s - i) * (s - i) : ℕ) : ℝ) =
        ((n.choose (s - (i + 1)) * (n - (s - (i + 1))) : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub (by omega : i ≤ s), Nat.cast_sub (by omega : s - (i + 1) ≤ n),
      Nat.cast_sub (by omega : i + 1 ≤ s)] at h'
    rw [hc]; linarith
  have hTi : Tf s n κ i = (i : ℝ) ^ κ * (n.choose (s - i) : ℝ) := Tf_in s n κ i hi1 (by omega)
  have hTi1 : Tf s n κ (i + 1) = ((i : ℝ) + 1) ^ κ * c := by
    rw [Tf_in s n κ (i + 1) (by omega) (by omega), hc]; push_cast; ring
  have hdiff : ((s : ℝ) - i) * (Tf s n κ i - Tf s n κ (i + 1)) =
      c * ((i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y) := by
    rw [hTi, hTi1, hYdef]
    have : ((s : ℝ) - i) * ((i : ℝ) ^ κ * (n.choose (s - i) : ℝ)) =
        (i : ℝ) ^ κ * ((n.choose (s - i) : ℝ) * ((s : ℝ) - i)) := by ring
    rw [mul_sub, this, hpas]; ring
  have hTY : ((s : ℝ) - i) * Tf s n κ (i + 1) = c * Y := by rw [hTi1, hYdef]; ring
  have hsi : (0 : ℝ) < (s : ℝ) - i := by linarith
  have herr1 : |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| ≤ 2 * e * Y := by
    have h1 : c * |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| =
        ((s : ℝ) - i) * |Tf s n κ i - Tf s n κ (i + 1)| := by
      rw [← abs_of_pos hcpos, ← abs_mul, ← hdiff, abs_mul, abs_of_pos hsi]
    have h2 : ((s : ℝ) - i) * |Tf s n κ i - Tf s n κ (i + 1)| ≤
        ((s : ℝ) - i) * (2 * e * Tf s n κ (i + 1)) :=
      mul_le_mul_of_nonneg_left hclose hsi.le
    have h3 : ((s : ℝ) - i) * (2 * e * Tf s n κ (i + 1)) = c * (2 * e * Y) := by
      linear_combination (2 * e) * hTY
    have h4 : c * |(i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y| ≤ c * (2 * e * Y) := by linarith
    exact le_of_mul_le_mul_left h4 hcpos
  have hIκ0 : (0 : ℝ) ≤ (i : ℝ) ^ κ := by positivity
  have hsplit : (n : ℝ) * (i : ℝ) ^ κ - Y = ((i : ℝ) ^ κ * ((n : ℝ) - s + i + 1) - Y) +
      (i : ℝ) ^ κ * ((s : ℝ) - i - 1) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hI0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  have h5 : |(i : ℝ) ^ κ * ((s : ℝ) - i - 1)| ≤ (s : ℝ) * (i : ℝ) ^ κ := by
    rw [abs_of_nonneg (mul_nonneg hIκ0 (by linarith))]
    nlinarith
  linarith

lemma final_step (S q α θ I N : ℝ) (κ : ℕ) (hS1 : 1 < S) (hq1 : 1 < q) (hθ0 : 0 ≤ θ)
    (hα0 : 0 < α) (hθq : θ * q ≤ α) (hακ : 4 * (S + 1) * q * α ^ κ ≤ 1) (hI1 : 1 ≤ I)
    (hIS : I + 1 ≤ S) (hiq : I * q ≤ α * (I + 1))
    (herr : |N - (S - I) * (I + 1) ^ κ| ≤
      2 * ((S + 1) * θ ^ κ) * ((S - I) * (I + 1) ^ κ) + S * I ^ κ) :
    |N - (S - I) * (I + 1) ^ κ| ≤ ((S - I) * (I + 1) ^ κ) ^ (1 - Real.logb S q) := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = (S - I) * (I + 1) ^ κ := ⟨_, rfl⟩
  rw [← hYdef] at herr ⊢
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.logb S q := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; exact Real.logb_pos hS1 hq1
  have hSδ : S ^ δ = q := by rw [hδ]; exact Real.rpow_logb (by linarith) (by linarith) (by linarith)
  have hsi : (1 : ℝ) ≤ S - I := by linarith
  have hi1κ : (1 : ℝ) ≤ (I + 1) ^ κ := one_le_pow₀ (by linarith)
  have hYge : (I + 1) ^ κ ≤ Y := by rw [hYdef]; nlinarith
  have hYpos : 0 < Y := by linarith
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = Y ^ δ := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hYpos δ
  have hYS : Y ≤ S ^ (κ + 1) := by
    rw [hYdef, pow_succ]
    have h1 : (I + 1) ^ κ ≤ S ^ κ := pow_le_pow_left₀ (by linarith) hIS κ
    have h2 : S - I ≤ S := by linarith
    have h3 : 0 ≤ (I + 1) ^ κ := by positivity
    have h4 : 0 ≤ S ^ κ := by positivity
    nlinarith
  have hPq : P ≤ q ^ (κ + 1) := by
    calc P = Y ^ δ := hP
      _ ≤ (S ^ (κ + 1)) ^ δ := Real.rpow_le_rpow hYpos.le hYS hδ0.le
      _ = (S ^ δ) ^ (κ + 1) := by
          rw [← Real.rpow_natCast_mul (by linarith), ← Real.rpow_mul_natCast (by linarith),
            mul_comm]
      _ = q ^ (κ + 1) := by rw [hSδ]
  have hR : Y ^ (1 - δ) = Y / P := by
    rw [Real.rpow_sub hYpos, Real.rpow_one, hP]
  have hθκ0 : 0 ≤ θ ^ κ := pow_nonneg hθ0 κ
  have hθκα : θ ^ κ * q ^ κ ≤ α ^ κ := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hθ0 (by linarith)) hθq κ
  have hqκ0 : 0 ≤ q ^ κ := by positivity

  have hc1 : 2 * ((S + 1) * θ ^ κ) * Y * (2 * P) ≤ Y := by
    have h1 : 4 * ((S + 1) * θ ^ κ) * P ≤ 1 := by
      calc 4 * ((S + 1) * θ ^ κ) * P ≤ 4 * ((S + 1) * θ ^ κ) * q ^ (κ + 1) :=
            mul_le_mul_of_nonneg_left hPq (by positivity)
        _ = 4 * (S + 1) * q * (θ ^ κ * q ^ κ) := by rw [pow_succ]; ring
        _ ≤ 4 * (S + 1) * q * α ^ κ :=
            mul_le_mul_of_nonneg_left hθκα (by positivity)
        _ ≤ 1 := hακ
    have := mul_le_mul_of_nonneg_left h1 hYpos.le
    nlinarith

  have hc2 : S * I ^ κ * (2 * P) ≤ Y := by
    have hiqκ : (I * q) ^ κ ≤ (α * (I + 1)) ^ κ :=
      pow_le_pow_left₀ (by positivity) hiq κ
    rw [mul_pow, mul_pow] at hiqκ
    have h2 : 2 * S * q * α ^ κ ≤ 1 := by
      have : 0 ≤ q * α ^ κ := by positivity
      nlinarith
    calc S * I ^ κ * (2 * P) ≤ S * I ^ κ * (2 * q ^ (κ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = 2 * S * q * (I ^ κ * q ^ κ) := by rw [pow_succ]; ring
      _ ≤ 2 * S * q * (α ^ κ * (I + 1) ^ κ) :=
          mul_le_mul_of_nonneg_left hiqκ (by positivity)
      _ = (2 * S * q * α ^ κ) * (I + 1) ^ κ := by ring
      _ ≤ 1 * (I + 1) ^ κ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Y := by linarith
  rw [hR, le_div_iff₀ hPpos]
  have := mul_le_mul_of_nonneg_right herr hPpos.le
  nlinarith

end TwoTermApprox

open TwoTermApprox in
theorem two_term_approx (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ J0 : ℕ, ∀ n j : ℕ, s < n → J0 ≤ j → gfsPoly s n j = 0 →
      ∃ i ∈ Finset.Icc 1 (s - 1),
        |((n * i ^ (j - 1) : ℕ) : ℝ) - (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ)| ≤
          (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ) ^ (1 - δ) ∧
        n ≤ 2 * ((s - i) * (i + 1) ^ (j - 1)) := by
  have hS3 : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hS1 : (1 : ℝ) < (s : ℝ) := by linarith
  obtain ⟨θ, q, α, hθ0, hq1, hqS, hα0, hα1, hθq, hiq, hlcθ⟩ := constants (s : ℝ) hS3
  have hC : 0 < 1 / (4 * ((s : ℝ) + 1) * q) := by positivity
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hC hα1
  have hKall : ∀ κ, K ≤ κ → 4 * ((s : ℝ) + 1) * q * α ^ κ ≤ 1 := by
    intro κ hκ
    have h1 : α ^ κ ≤ α ^ K := pow_le_pow_of_le_one hα0.le hα1.le hκ
    have h2 : 0 < 4 * ((s : ℝ) + 1) * q := by positivity
    have h3 : α ^ κ < 1 / (4 * ((s : ℝ) + 1) * q) := lt_of_le_of_lt h1 hK
    rw [lt_div_iff₀ h2] at h3
    linarith
  refine ⟨Real.logb (s : ℝ) q, Real.logb_pos hS1 hq1, ?_, K + 1, ?_⟩
  · rw [← Real.logb_self_eq_one hS1]
    exact Real.logb_lt_logb hS1 (by linarith) hqS
  intro n j hn hj hf
  have hακ := hKall (j - 1) (by omega)

  have hθκ0 : 0 ≤ θ ^ (j - 1) := pow_nonneg hθ0 _
  have he : ((s : ℝ) + 1) * θ ^ (j - 1) ≤ 1 / 2 := by
    have h1 : θ ^ (j - 1) ≤ α ^ (j - 1) := by
      have hθα : θ ≤ α := le_trans (by nlinarith) hθq
      exact pow_le_pow_left₀ hθ0 hθα _
    have h2 : 0 ≤ α ^ (j - 1) := pow_nonneg hα0.le _
    have h3 : 4 * ((s : ℝ) + 1) * α ^ (j - 1) ≤ 4 * ((s : ℝ) + 1) * q * α ^ (j - 1) := by
      have : 0 ≤ 4 * ((s : ℝ) + 1) * α ^ (j - 1) := by positivity
      nlinarith
    have h4 : ((s : ℝ) + 1) * θ ^ (j - 1) ≤ ((s : ℝ) + 1) * α ^ (j - 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  obtain ⟨i, hi, hclose⟩ := core (Tf s n (j - 1)) s (θ ^ (j - 1)) hθκ0 he
    (Tf_nonneg s n (j - 1)) (Tf_lc s n (j - 1) θ hlcθ) (Tf_pos s n (j - 1) hn) (by omega)
    (Tf_sum s n j hf)
  have hi' := Finset.mem_Icc.1 hi
  refine ⟨i, hi, ?_⟩
  have herr := conversion s n (j - 1) i hn hi'.1 (by omega) _ hclose
  have hI1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi'.1
  have hIs : (i : ℝ) + 1 ≤ (s : ℝ) := by
    have : i + 1 ≤ s := by omega
    exact_mod_cast this
  have hmain := final_step (s : ℝ) q α θ (i : ℝ) ((n : ℝ) * (i : ℝ) ^ (j - 1)) (j - 1) hS1 hq1
    hθ0 hα0 hθq hακ hI1 hIs (hiq (i : ℝ) hI1 hIs) herr
  have hYcast : (((s - i) * (i + 1) ^ (j - 1) : ℕ) : ℝ) =
      ((s : ℝ) - i) * ((i : ℝ) + 1) ^ (j - 1) := by
    push_cast [Nat.cast_sub (by omega : i ≤ s)]; ring
  have hXcast : ((n * i ^ (j - 1) : ℕ) : ℝ) = (n : ℝ) * (i : ℝ) ^ (j - 1) := by
    push_cast; ring
  rw [hYcast, hXcast]
  refine ⟨hmain, ?_⟩

  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((s : ℝ) - i) * ((i : ℝ) + 1) ^ (j - 1) := ⟨_, rfl⟩
  rw [← hYdef] at hmain hYcast
  have hδ1 : Real.logb (s : ℝ) q < 1 := by
    rw [← Real.logb_self_eq_one hS1]
    exact Real.logb_lt_logb hS1 (by linarith) hqS
  have hi1κ : (1 : ℝ) ≤ ((i : ℝ) + 1) ^ (j - 1) := one_le_pow₀ (by linarith)
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    have : (1 : ℝ) ≤ (s : ℝ) - i := by linarith
    nlinarith
  have hRY : Y ^ (1 - Real.logb (s : ℝ) q) ≤ Y := by
    calc Y ^ (1 - Real.logb (s : ℝ) q) ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [Real.logb_pos hS1 hq1])
      _ = Y := Real.rpow_one Y
  have h1 : (n : ℝ) * (i : ℝ) ^ (j - 1) ≤ 2 * Y := by
    have := (abs_le.1 hmain).2
    linarith
  have hiκ1 : (1 : ℝ) ≤ (i : ℝ) ^ (j - 1) := one_le_pow₀ hI1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h2 : (n : ℝ) ≤ 2 * Y := by nlinarith
  rw [← hYcast] at h2
  exact_mod_cast h2

end OMA494
end

-- ExactCase
section
namespace OMA494

lemma exactCase_choose_mul_pow_le (n s : ℕ) :
    ∀ t k, k + t ≤ s → n.choose k * (n - s) ^ t ≤ s ^ t * n.choose (k + t) := by
  intro t
  induction t with
  | zero => intro k _; simp
  | succ t ih =>
    intro k hk
    have h1 := Nat.choose_succ_right_eq n k
    have h2 : n - s ≤ n - k := by omega
    have h3 := ih (k + 1) (by omega)
    calc n.choose k * (n - s) ^ (t + 1) = n.choose k * (n - s) * (n - s) ^ t := by ring
      _ ≤ n.choose k * (n - k) * (n - s) ^ t := by gcongr
      _ = n.choose (k + 1) * (k + 1) * (n - s) ^ t := by rw [h1]
      _ ≤ n.choose (k + 1) * s * (n - s) ^ t := by gcongr; omega
      _ = s * (n.choose (k + 1) * (n - s) ^ t) := by ring
      _ ≤ s * (s ^ t * n.choose (k + 1 + t)) := by gcongr
      _ = s ^ (t + 1) * n.choose (k + (t + 1)) := by
          rw [show k + 1 + t = k + (t + 1) by omega]; ring

lemma exactCase_le_two_pow (i : ℕ) (hi : 4 ≤ i) : i ≤ 2 ^ (i - 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = t + 4 := ⟨i - 4, by omega⟩
  have h : t < 2 ^ t := Nat.lt_two_pow_self
  rw [show t + 4 - 2 = t + 2 by omega, pow_add]
  norm_num
  omega

lemma exactCase_term_le (s n m i : ℕ) (hi4 : 4 ≤ i) (his : i ≤ s) (hn : 2 ^ m ≤ n - s) :
    i ^ m * n.choose (s - i) ≤ 2 ^ m * s ^ s * n.choose (s - 3) := by
  have key := exactCase_choose_mul_pow_le n s (i - 3) (s - i) (by omega)
  rw [show s - i + (i - 3) = s - 3 by omega] at key
  have hpow : i ^ m ≤ 2 ^ m * (2 ^ m) ^ (i - 3) := by
    calc i ^ m ≤ (2 ^ (i - 2)) ^ m := Nat.pow_le_pow_left (exactCase_le_two_pow i hi4) m
      _ = 2 ^ m * (2 ^ m) ^ (i - 3) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1
          rw [show i - 2 = (i - 3) + 1 by omega]; ring
  have hst : s ^ (i - 3) ≤ s ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  calc i ^ m * n.choose (s - i) ≤ 2 ^ m * (2 ^ m) ^ (i - 3) * n.choose (s - i) := by gcongr
    _ = 2 ^ m * (n.choose (s - i) * (2 ^ m) ^ (i - 3)) := by ring
    _ ≤ 2 ^ m * (n.choose (s - i) * (n - s) ^ (i - 3)) := by gcongr
    _ ≤ 2 ^ m * (s ^ (i - 3) * n.choose (s - 3)) := by gcongr
    _ ≤ 2 ^ m * (s ^ s * n.choose (s - 3)) := by gcongr
    _ = 2 ^ m * s ^ s * n.choose (s - 3) := by ring

lemma exactCase_bernoulli (m : ℕ) : 2 ^ m * (m + 2) ≤ 2 * 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (2 ^ m), Nat.zero_le m]

lemma exactCase_one' (r m n : ℕ) (hm : 2 ≤ m) (hn : n = (r + 2) * 2 ^ m)
    (hK : 2 ^ m * (1 + (r + 3) ^ (r + 3 + 1)) < 3 ^ m) :
    0 < gfsPoly (r + 3) n (m + 1) := by
  have h2m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hns : 2 ^ m ≤ n - (r + 3) := by
    have : (r + 2) * 2 ^ m = (r + 1) * 2 ^ m + 2 ^ m := by ring
    have h4 : (r + 1) * 4 ≤ (r + 1) * 2 ^ m := Nat.mul_le_mul_left _ h2m
    omega
  have hnr : r + 2 ≤ n := by
    have : (r + 2) * 1 ≤ (r + 2) * 2 ^ m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hf : gfsPoly (r + 3) n (m + 1) = ∑ i ∈ Finset.Icc 1 (r + 3),
      (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) := by
    simp [gfsPoly]
  have hsplit : ∑ i ∈ Finset.Icc 1 (r + 3),
      (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) =
      ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ) + 3 ^ m * (n.choose r : ℤ)) +
      ∑ i ∈ Finset.Ico 4 (r + 4), (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ) := by
    have e : Finset.Icc 1 (r + 3) = Finset.Ico 1 (r + 4) := by
      ext x; simp [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, ← Finset.sum_Ico_consecutive _ (show 1 ≤ 4 by norm_num) (show 4 ≤ r + 4 by omega)]
    congr 1
    rw [Finset.sum_Ico_succ_top (by norm_num), Finset.sum_Ico_succ_top (by norm_num),
      Finset.sum_Ico_succ_top (by norm_num)]
    simp only [Finset.Ico_self, Finset.sum_empty]
    rw [show r + 3 - 1 = r + 2 by omega, show r + 3 - 2 = r + 1 by omega,
      show r + 3 - 3 = r by omega]
    norm_num
    ring
  have hcpos : 0 < n.choose r := Nat.choose_pos (by omega)

  have hR : |∑ i ∈ Finset.Ico 4 (r + 4), (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ)|
      ≤ (r : ℤ) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * (n.choose r : ℤ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.Ico 4 (r + 4),
        |(-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ)|
          ≤ ((2 ^ m * (r + 3) ^ (r + 3) * n.choose r : ℕ) : ℤ) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have := exactCase_term_le (r + 3) n m i hi.1 (by omega) hns
      rw [show r + 3 - 3 = r by omega] at this
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      exact_mod_cast this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, show r + 4 - 4 = r by omega]
    push_cast
    exact le_refl _
  have hA := Nat.choose_succ_right_eq n (r + 1)
  have hB := Nat.choose_succ_right_eq n r
  have hAz : (n.choose (r + 2) : ℤ) * (r + 2) = (n.choose (r + 1) : ℤ) * ((n : ℤ) - (r + 1)) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hA
    push_cast [Nat.cast_sub (show r + 1 ≤ n by omega)] at this
    rw [show r + 1 + 1 = r + 2 by omega] at this
    linarith
  have hBz : (n.choose (r + 1) : ℤ) * (r + 1) = (n.choose r : ℤ) * ((n : ℤ) - r) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hB
    push_cast [Nat.cast_sub (show r ≤ n by omega)] at this
    linarith
  have hnz : (n : ℤ) = (r + 2) * 2 ^ m := by
    rw [hn]; push_cast; ring
  have hkey : ((r : ℤ) + 2) * ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ)) = (n.choose r : ℤ) * r := by
    linear_combination hAz - hBz + ((n.choose (r + 1) : ℤ) - (n.choose r : ℤ)) * hnz
  have hfirst : (0 : ℤ) ≤ (n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ) := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 : ((r : ℤ) + 2) * ((n.choose (r + 2) : ℤ) - 2 ^ m * (n.choose (r + 1) : ℤ)
      + 2 ^ m * (n.choose r : ℤ)) < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    have h2 : (0 : ℤ) ≤ (n.choose r : ℤ) * r := by positivity
    linarith
  rw [hf, hsplit]
  have hR' := neg_abs_le (∑ i ∈ Finset.Ico 4 (r + 4),
    (-1) ^ (i - 1) * (i : ℤ) ^ m * (n.choose (r + 3 - i) : ℤ))
  have hKz : (2 : ℤ) ^ m * (1 + ((r : ℤ) + 3) ^ (r + 3 + 1)) + 1 ≤ 3 ^ m := by
    exact_mod_cast hK
  have hcz : (1 : ℤ) ≤ n.choose r := by exact_mod_cast hcpos
  have hss : (r : ℤ) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r)
      ≤ 2 ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * n.choose r := by
    have h0 : (0 : ℤ) ≤ 2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r := by positivity
    have : (2 : ℤ) ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * n.choose r
        = ((r : ℤ) + 3) * (2 ^ m * ((r : ℤ) + 3) ^ (r + 3) * n.choose r) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) h0
  set X : ℤ := (2 : ℤ) ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) with hX
  set C : ℤ := (n.choose r : ℤ) with hC
  have hD : (0 : ℤ) ≤ (3 ^ m - (2 ^ m + X + 1)) * (C - 1) :=
    mul_nonneg (by nlinarith) (by linarith)
  have hX' : 2 ^ m * ((r : ℤ) + 3) ^ (r + 3 + 1) * C = X * C := by rw [hX]
  nlinarith

lemma exactCase_one (s m : ℕ) (hs : 3 ≤ s) (hm : 2 ≤ m)
    (hK : 2 ^ m * (1 + s ^ (s + 1)) < 3 ^ m) :
    0 < gfsPoly s ((s - 1) * 2 ^ m) (m + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
  exact exactCase_one' r m _ hm (by rw [show r + 3 - 1 = r + 2 by omega]) hK

theorem exact_case (s : ℕ) (hs : 3 ≤ s) :
    ∃ N : ℕ, ∀ n j i : ℕ, N ≤ n → 1 ≤ j → i ∈ Finset.Icc 1 (s - 1) →
      n * i ^ (j - 1) = (s - i) * (i + 1) ^ (j - 1) → gfsPoly s n j ≠ 0 := by
  set K := 1 + s ^ (s + 1) with hKdef
  set M := 2 * K + 2 with hM
  refine ⟨s ^ (s + 1) + (s - 1) * 2 ^ M + 1, ?_⟩
  intro n j i hN hj hi heq
  rw [Finset.mem_Icc] at hi
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at heq
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  ·
    have hi1' : i = 1 := by omega
    subst hi1'
    simp only [one_pow, mul_one] at heq
    norm_num at heq
    subst heq
    have hmM : M ≤ m := by
      by_contra hlt
      rw [not_le] at hlt
      have : 2 ^ m ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hlt.le
      have : (s - 1) * 2 ^ m ≤ (s - 1) * 2 ^ M := Nat.mul_le_mul_left _ this
      omega
    have hb := exactCase_bernoulli m
    have hK : 2 ^ m * (1 + s ^ (s + 1)) < 3 ^ m := by
      rw [← hKdef]
      have : 2 ^ m * (2 * K) < 2 ^ m * (m + 2) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
      nlinarith
    exact (exactCase_one s m hs (by omega) hK).ne'
  ·
    exfalso
    have hcop : Nat.Coprime (i ^ m) ((i + 1) ^ m) :=
      Nat.Coprime.pow m m (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _))
    have hdvd : i ^ m ∣ (s - i) * (i + 1) ^ m := ⟨n, by rw [← heq]; ring⟩
    have hd := hcop.dvd_of_dvd_mul_right hdvd
    have hle : i ^ m ≤ s - i := Nat.le_of_dvd (by omega) hd
    have h2i : 2 ^ m ≤ i ^ m := Nat.pow_le_pow_left hi2 m
    have hms : m < s := by
      have : m < 2 ^ m := Nat.lt_two_pow_self
      omega
    have hip : 1 ≤ i ^ m := Nat.one_le_pow _ _ (by omega)
    have h1 : n ≤ n * i ^ m := Nat.le_mul_of_pos_right n hip
    have h2 : (s - i) * (i + 1) ^ m ≤ s * s ^ s := by
      apply Nat.mul_le_mul (by omega)
      calc (i + 1) ^ m ≤ s ^ m := Nat.pow_le_pow_left (by omega) m
        _ ≤ s ^ s := Nat.pow_le_pow_right (by omega) hms.le
    have h3 : s * s ^ s = s ^ (s + 1) := by ring
    omega

end OMA494
end

-- AuxPolynomial
section
namespace OMA494

open Finset Matrix

local instance instOMAMatrixSeminormedAddCommGroup {m n α : Type*} [Fintype m] [Fintype n]
    [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Matrix m n α) :=
  Matrix.seminormedAddCommGroup

lemma binRoot_pow' (r a b : ℕ) (hr : 1 ≤ r) : binRoot r a b ^ r = (b : ℝ) / a := by
  unfold binRoot
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (by positivity) (by omega)

lemma binRoot_pos' (r a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < binRoot r a b := by
  unfold binRoot
  exact Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hb) (by exact_mod_cast ha)) _

def auxEntryN (r a b r1 r2 : ℕ) (s i1 i2 k1 k2 : ℕ) : ℕ :=
  if (k1 + k2) % r = s then
    k1.choose i1 * k2.choose i2 * b ^ ((k1 + k2) / r) * a ^ ((r1 + r2) / r - (k1 + k2) / r)
  else 0

lemma auxEntryN_le (r a b r1 r2 s i1 i2 k1 k2 : ℕ) (ha : 0 < a) (hk1 : k1 ≤ r1) (hk2 : k2 ≤ r2) :
    auxEntryN r a b r1 r2 s i1 i2 k1 k2 ≤ (2 * max a b) ^ (r1 + r2) := by
  unfold auxEntryN
  split_ifs
  · set q := (k1 + k2) / r
    set Q := (r1 + r2) / r
    have hqQ : q ≤ Q := Nat.div_le_div_right (by omega)
    have hQ : Q ≤ r1 + r2 := Nat.div_le_self _ _
    have hM : 1 ≤ max a b := le_trans ha (le_max_left _ _)
    have h1 : k1.choose i1 ≤ 2 ^ r1 :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hk1)
    have h2 : k2.choose i2 ≤ 2 ^ r2 :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hk2)
    have h3 : b ^ q ≤ max a b ^ q := Nat.pow_le_pow_left (le_max_right _ _) _
    have h4 : a ^ (Q - q) ≤ max a b ^ (Q - q) := Nat.pow_le_pow_left (le_max_left _ _) _
    have h5 : max a b ^ q * max a b ^ (Q - q) ≤ max a b ^ (r1 + r2) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hM (by omega)
    calc k1.choose i1 * k2.choose i2 * b ^ q * a ^ (Q - q)
        = (k1.choose i1 * k2.choose i2) * (b ^ q * a ^ (Q - q)) := by ring
      _ ≤ (2 ^ r1 * 2 ^ r2) * (max a b ^ q * max a b ^ (Q - q)) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
      _ ≤ (2 ^ r1 * 2 ^ r2) * max a b ^ (r1 + r2) := Nat.mul_le_mul le_rfl h5
      _ = (2 * max a b) ^ (r1 + r2) := by rw [mul_pow, ← pow_add]
  · exact Nat.zero_le _

lemma aux_col_identity (r a b r1 r2 i1 i2 k1 k2 : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (_hb : 0 < b)
    (hk : k1 + k2 ≤ r1 + r2) :
    ∑ s : Fin r, binRoot r a b ^ (s : ℕ) * ((auxEntryN r a b r1 r2 s i1 i2 k1 k2 : ℕ) : ℝ) =
      (a : ℝ) ^ ((r1 + r2) / r) * binRoot r a b ^ (i1 + i2) *
        ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * binRoot r a b ^ (k1 - i1) *
          binRoot r a b ^ (k2 - i2)) := by
  set θ := binRoot r a b with hθ
  set q := (k1 + k2) / r
  set Q := (r1 + r2) / r
  have hqQ : q ≤ Q := Nat.div_le_div_right hk
  have hmod : (k1 + k2) % r < r := Nat.mod_lt _ (by omega)
  rw [Finset.sum_eq_single (⟨(k1 + k2) % r, hmod⟩ : Fin r)]
  · simp only [auxEntryN]
    by_cases h1 : i1 ≤ k1
    · by_cases h2 : i2 ≤ k2
      · have hθk : θ ^ (i1 + i2) * (θ ^ (k1 - i1) * θ ^ (k2 - i2)) = θ ^ (k1 + k2) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        have he : θ ^ (k1 + k2) = ((b : ℝ) / a) ^ q * θ ^ ((k1 + k2) % r) := by
          rw [← binRoot_pow' r a b hr, ← pow_mul, ← pow_add, Nat.div_add_mod]
        have hQq : (a : ℝ) ^ Q = (a : ℝ) ^ (Q - q) * (a : ℝ) ^ q := by
          rw [← pow_add, Nat.sub_add_cancel hqQ]
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
        calc θ ^ ((k1 + k2) % r) *
              (((k1.choose i1 * k2.choose i2 * b ^ q * a ^ (Q - q) : ℕ)) : ℝ)
            = (a : ℝ) ^ (Q - q) * ((a : ℝ) ^ q * ((b : ℝ) / a) ^ q) * θ ^ ((k1 + k2) % r) *
                ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ)) := by
              rw [← mul_pow, mul_div_cancel₀ _ ha']; push_cast; ring
          _ = (a : ℝ) ^ Q * (θ ^ (i1 + i2) * (θ ^ (k1 - i1) * θ ^ (k2 - i2))) *
                ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ)) := by
              rw [hθk, he, hQq]; ring
          _ = _ := by ring
      · have : k2.choose i2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [this]
    · have : k1.choose i1 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  · intro s _ hs
    have : (k1 + k2) % r ≠ (s : ℕ) := by
      intro h; apply hs; ext; exact h.symm
    simp [auxEntryN, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem aux_polynomial (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r1 r2 : ℕ, 16 * r ≤ r2 → r2 ≤ r1 →
      ∃ c : ℕ → ℕ → ℤ, BoxNonzero r1 r2 c ∧ (∀ k1 k2, |(c k1 k2 : ℝ)| ≤ K ^ (r1 + r2)) ∧
        ∀ i1 i2 : ℕ, ((i1 : ℝ) / r1 + (i2 : ℝ) / r2) * (2 * Real.sqrt r) < 1 →
          hasseEval r1 r2 c i1 i2 (binRoot r a b) (binRoot r a b) = 0 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  refine ⟨4 * ((max a b : ℕ) : ℝ), ?_, ?_⟩
  · have : (a : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_left a b
    linarith
  intro r1 r2 h16 h21
  set θ := binRoot r a b with hθ
  have hθpos : 0 < θ := binRoot_pos' r a b ha hb
  set sr := Real.sqrt (r : ℝ) with hsr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsr1 : 1 ≤ sr := by rw [hsr]; exact Real.one_le_sqrt.mpr hrR
  have hsrsq : sr * sr = r := Real.mul_self_sqrt (by positivity)
  have hsr_le : sr ≤ r := by nlinarith
  have hr1R : (16 : ℝ) * r ≤ r2 := by exact_mod_cast h16
  have hr21R : (r2 : ℝ) ≤ r1 := by exact_mod_cast h21
  set N1 := ⌈(r1 : ℝ) / (2 * sr)⌉₊ with hN1
  set N2 := ⌈(r2 : ℝ) / (2 * sr)⌉₊ with hN2
  have h2sr : 0 < 2 * sr := by linarith
  have hN1pos : 0 < N1 := Nat.ceil_pos.mpr (div_pos (by linarith) h2sr)
  have hN2pos : 0 < N2 := Nat.ceil_pos.mpr (div_pos (by linarith) h2sr)
  have hN1le : (N1 : ℝ) ≤ (r1 : ℝ) / (2 * sr) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hN2le : (N2 : ℝ) ≤ (r2 : ℝ) / (2 * sr) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le

  have hcountR : 2 * ((r : ℝ) * N1 * N2) ≤ ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) := by
    set x := (r1 : ℝ) / (2 * sr) with hx
    set y := (r2 : ℝ) / (2 * sr) with hy
    have hx2 : x * (2 * sr) = r1 := div_mul_cancel₀ _ h2sr.ne'
    have hy2 : y * (2 * sr) = r2 := div_mul_cancel₀ _ h2sr.ne'
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hb1 : (r : ℝ) * N1 * N2 ≤ r * (x + 1) * (y + 1) := by
      have := mul_le_mul hN1le hN2le (Nat.cast_nonneg _) (by positivity)
      calc (r : ℝ) * N1 * N2 = r * (N1 * N2) := by ring
        _ ≤ r * ((x + 1) * (y + 1)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hb2 : 4 * ((r : ℝ) * (x + 1) * (y + 1)) =
        r1 * r2 + 2 * sr * (r1 + r2) + 4 * r := by
      rw [← hx2, ← hy2, ← hsrsq]; ring
    have h16sr : 16 * sr ≤ r2 := by linarith
    nlinarith
  have hcount : 2 * (r * N1 * N2) ≤ (r1 + 1) * (r2 + 1) := by exact_mod_cast hcountR

  let A : Matrix (Fin r × Fin N1 × Fin N2) (Fin (r1 + 1) × Fin (r2 + 1)) ℤ :=
    fun p k => ((auxEntryN r a b r1 r2 p.1 p.2.1 p.2.2 k.1 k.2 : ℕ) : ℤ)
  have hcardα : Fintype.card (Fin r × Fin N1 × Fin N2) = r * N1 * N2 := by
    simp [Fintype.card_prod, mul_assoc]
  have hcardβ : Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) = (r1 + 1) * (r2 + 1) := by
    simp [Fintype.card_prod]
  have hm : 0 < Fintype.card (Fin r × Fin N1 × Fin N2) := by
    rw [hcardα]; positivity
  have hn : Fintype.card (Fin r × Fin N1 × Fin N2) < Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) := by
    rw [hcardα, hcardβ]
    have : 0 < r * N1 * N2 := by positivity
    omega
  obtain ⟨t, ht0, hAt, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm

  set M : ℕ := max a b with hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans ha (le_max_left a b)
  have hAnorm : ‖A‖ ≤ ((2 : ℝ) * M) ^ (r1 + r2) := by
    rw [Matrix.norm_le_iff (by positivity)]
    intro p k
    simp only [A, Int.norm_natCast]
    have := auxEntryN_le r a b r1 r2 p.1 p.2.1 p.2.2 k.1 k.2 ha (Nat.lt_succ_iff.mp k.1.isLt)
      (Nat.lt_succ_iff.mp k.2.isLt)
    exact_mod_cast this
  have hexp : ((Fintype.card (Fin r × Fin N1 × Fin N2) : ℕ) : ℝ) /
      ((Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) : ℕ) - (Fintype.card (Fin r × Fin N1 × Fin N2) : ℕ)) ≤ 1 := by
    rw [hcardα, hcardβ]
    have hc : (2 : ℝ) * ((r * N1 * N2 : ℕ) : ℝ) ≤ (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hpos : (0 : ℝ) < ((r * N1 * N2 : ℕ) : ℝ) := by
      have : 0 < r * N1 * N2 := by positivity
      exact_mod_cast this
    rw [div_le_one (by linarith)]
    linarith
  have hnle : (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r1 + r2) := by
    have h1 : r1 + 1 ≤ 2 ^ r1 := Nat.lt_two_pow_self
    have h2 : r2 + 1 ≤ 2 ^ r2 := Nat.lt_two_pow_self
    have : (r1 + 1) * (r2 + 1) ≤ 2 ^ (r1 + r2) := by
      rw [pow_add]; exact Nat.mul_le_mul h1 h2
    exact_mod_cast this
  have hbase1 : (1 : ℝ) ≤ (Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) : ℝ) * max 1 ‖A‖ := by
    rw [hcardβ]
    have : (1 : ℝ) ≤ (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) := by
      have : 1 ≤ (r1 + 1) * (r2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    nlinarith [le_max_left (1 : ℝ) ‖A‖]
  have htn' : ‖t‖ ≤ (4 * (M : ℝ)) ^ (r1 + r2) := by
    refine htn.trans ?_
    refine (Real.rpow_le_rpow_of_exponent_le hbase1 hexp).trans ?_
    rw [Real.rpow_one, hcardβ]
    have hmax : max 1 ‖A‖ ≤ ((2 : ℝ) * M) ^ (r1 + r2) :=
      max_le (one_le_pow₀ (by linarith)) hAnorm
    calc (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) * max 1 ‖A‖
        ≤ (2 : ℝ) ^ (r1 + r2) * ((2 : ℝ) * M) ^ (r1 + r2) :=
          mul_le_mul hnle hmax (by positivity) (by positivity)
      _ = (4 * (M : ℝ)) ^ (r1 + r2) := by rw [← mul_pow]; ring

  let c : ℕ → ℕ → ℤ := fun k1 k2 =>
    if h : k1 ≤ r1 ∧ k2 ≤ r2 then t (⟨k1, Nat.lt_succ_of_le h.1⟩, ⟨k2, Nat.lt_succ_of_le h.2⟩)
    else 0
  refine ⟨c, ?_, ?_, ?_⟩
  ·
    obtain ⟨⟨k1, k2⟩, hk⟩ := Function.ne_iff.mp ht0
    refine ⟨k1, Nat.lt_succ_iff.mp k1.isLt, k2, Nat.lt_succ_iff.mp k2.isLt, ?_⟩
    simp only [c, dif_pos (And.intro (Nat.lt_succ_iff.mp k1.isLt) (Nat.lt_succ_iff.mp k2.isLt))]
    simpa using hk
  · intro k1 k2
    simp only [c]
    split_ifs with h
    · have := (norm_le_pi_norm t (⟨k1, Nat.lt_succ_of_le h.1⟩, ⟨k2, Nat.lt_succ_of_le h.2⟩)).trans htn'
      rw [Int.norm_eq_abs] at this
      exact this
    · simp only [Int.cast_zero, abs_zero]; positivity
  · intro i1 i2 hw
    have hr1pos : (0 : ℝ) < r1 := by linarith
    have hr2pos : (0 : ℝ) < r2 := by linarith
    have hi1 : i1 < N1 := by
      rw [hN1, Nat.lt_ceil, lt_div_iff₀ h2sr]
      have : (i1 : ℝ) / r1 * (2 * sr) < 1 := by
        have : 0 ≤ (i2 : ℝ) / r2 * (2 * sr) := by positivity
        nlinarith
      rw [div_mul_eq_mul_div, div_lt_one hr1pos] at this
      exact this
    have hi2 : i2 < N2 := by
      rw [hN2, Nat.lt_ceil, lt_div_iff₀ h2sr]
      have : (i2 : ℝ) / r2 * (2 * sr) < 1 := by
        have : 0 ≤ (i1 : ℝ) / r1 * (2 * sr) := by positivity
        nlinarith
      rw [div_mul_eq_mul_div, div_lt_one hr2pos] at this
      exact this
    have hrow : ∀ s : Fin r, (A *ᵥ t) (s, ⟨i1, hi1⟩, ⟨i2, hi2⟩) = 0 := fun s => by
      rw [hAt]; rfl
    have hH : hasseEval r1 r2 c i1 i2 θ θ =
        ∑ k : Fin (r1 + 1) × Fin (r2 + 1), (t k : ℝ) *
          ((((k.1 : ℕ).choose i1 : ℕ) : ℝ) * (((k.2 : ℕ).choose i2 : ℕ) : ℝ) *
            θ ^ ((k.1 : ℕ) - i1) * θ ^ ((k.2 : ℕ) - i2)) := by
      unfold hasseEval
      rw [Fintype.sum_prod_type, Finset.sum_range]
      refine Finset.sum_congr rfl fun k1 _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun k2 _ => ?_
      simp only [c, dif_pos (And.intro (Nat.lt_succ_iff.mp k1.isLt) (Nat.lt_succ_iff.mp k2.isLt))]
      ring
    have hkey : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) * hasseEval r1 r2 c i1 i2 θ θ =
        ∑ s : Fin r, θ ^ (s : ℕ) * (((A *ᵥ t) (s, ⟨i1, hi1⟩, ⟨i2, hi2⟩) : ℤ) : ℝ) := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      rw [Finset.sum_comm, hH, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k.1 : ℕ) + k.2 ≤ r1 + r2 := by
        have := k.1.isLt; have := k.2.isLt; omega
      have hcol := aux_col_identity r a b r1 r2 i1 i2 k.1 k.2 hr ha hb hk
      rw [← hθ] at hcol
      simp only [A, Int.cast_natCast]
      calc (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) *
            ((t k : ℝ) * ((((k.1 : ℕ).choose i1 : ℕ) : ℝ) * (((k.2 : ℕ).choose i2 : ℕ) : ℝ) *
              θ ^ ((k.1 : ℕ) - i1) * θ ^ ((k.2 : ℕ) - i2)))
          = (t k : ℝ) * ∑ s : Fin r, θ ^ (s : ℕ) *
              ((auxEntryN r a b r1 r2 s i1 i2 k.1 k.2 : ℕ) : ℝ) := by
            rw [hcol]; ring
        _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
    have hzero : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) * hasseEval r1 r2 c i1 i2 θ θ = 0 := by
      rw [hkey]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hrow s]; simp
    have hne : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) ≠ 0 := by
      have : (0 : ℝ) < a := by linarith
      positivity
    exact (mul_eq_zero.mp hzero).resolve_left hne

end OMA494
end

-- RothLemmaTwo
section
open Polynomial Finset

namespace OMA494
namespace RL2

noncomputable def a2_wr {m : ℕ} (f : Fin m → Polynomial ℚ) : Matrix (Fin m) (Fin m) (Polynomial ℚ) :=
  Matrix.of fun (μ k : Fin m) => Polynomial.derivative^[(μ : ℕ)] (f k)

lemma a2_iterate_derivative_add' (p q : Polynomial ℚ) (k : ℕ) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by
  induction k generalizing p q with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply, ih]

lemma a2_coeff_prod_of_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Polynomial ℚ)
    (e : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ e i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff (e i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a).natDegree ≤ e a := h a (Finset.mem_insert_self a s)
    have h2 : (∏ i ∈ s, p i).natDegree ≤ ∑ i ∈ s, e i :=
      (natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [coeff_mul_add_eq_of_natDegree_le h1 h2, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

lemma a2_det_ne_zero_of_injective {m : ℕ} (f : Fin m → Polynomial ℚ) (hne : ∀ k, f k ≠ 0)
    (hinj : Function.Injective fun k => (f k).natDegree) : (a2_wr f).det ≠ 0 := by
  set d : Fin m → ℕ := fun k => (f k).natDegree with hd
  set N : ℕ := ∑ k, d k - ∑ μ : Fin m, (μ : ℕ) with hN
  have key : ∀ σ : Equiv.Perm (Fin m),
      (∏ k, derivative^[(σ k : ℕ)] (f k)).coeff N
        = ∏ k, ((f k).leadingCoeff * ((d k).descFactorial (σ k) : ℚ)) := by
    intro σ
    by_cases h : ∀ k, (σ k : ℕ) ≤ d k
    · have hN' : N = ∑ k, (d k - σ k) := by
        rw [Finset.sum_tsub_distrib _ (fun k _ => h k), hN]
        congr 1
        exact (Equiv.sum_comp σ (fun μ : Fin m => (μ : ℕ))).symm
      rw [hN', a2_coeff_prod_of_le _ _ _ (fun k _ => by
        have := natDegree_iterate_derivative (f k) (σ k); simpa [hd] using this)]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [coeff_iterate_derivative, Nat.sub_add_cancel (h k), nsmul_eq_mul, mul_comm]
      rfl
    · push Not at h
      obtain ⟨k, hk⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (iterate_derivative_eq_zero hk),
        Finset.prod_eq_zero (Finset.mem_univ k)]
      · simp
      · simp [(Nat.descFactorial_eq_zero_iff_lt).mpr hk]

  let D : Matrix (Fin m) (Fin m) ℚ := Matrix.of fun (μ k : Fin m) => ((d k).descFactorial μ : ℚ)
  have hcoeff : (a2_wr f).det.coeff N = (∏ k, (f k).leadingCoeff) * D.det := by
    have e1 : (a2_wr f).det.coeff N
        = (Matrix.of fun (μ k : Fin m) => (f k).leadingCoeff * D μ k).det := by
      rw [Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← C_eq_intCast,
        coeff_C_mul]
      simp only [a2_wr, Matrix.of_apply, D]
      rw [key]
    rw [e1, ← Matrix.det_transpose D, ← Matrix.det_mul_column]
    conv_lhs => rw [← Matrix.det_transpose]
    rfl
  have hD : D.det ≠ 0 := by
    have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun k => (d k : ℚ)) (fun μ => descPochhammer ℚ μ)
      (fun μ => descPochhammer_natDegree ℚ μ) (fun μ => monic_descPochhammer ℚ μ)
    have hDt : D = (Matrix.of fun (i j : Fin m) =>
        (descPochhammer ℚ (j : ℕ)).eval ((d i : ℕ) : ℚ)).transpose := by
      ext μ k
      simp [D, descPochhammer_eval_eq_descFactorial]
    rw [hDt, Matrix.det_transpose, ← hv, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact hinj (Nat.cast_injective hab)
  intro h0
  have : (a2_wr f).det.coeff N = 0 := by rw [h0]; simp
  rw [hcoeff] at this
  refine (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => ?_) hD) this
  exact leadingCoeff_ne_zero.mpr (hne k)

lemma a2_wmain {m : ℕ} (n : ℕ) : ∀ f : Fin m → Polynomial ℚ, (∑ k, (f k).natDegree) = n →
    LinearIndependent ℚ f → (a2_wr f).det ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  by_cases hinj : Function.Injective fun k => (f k).natDegree
  · exact a2_det_ne_zero_of_injective f (fun k => hf.ne_zero k) hinj
  simp only [Function.Injective, not_forall] at hinj
  obtain ⟨a, b, hdeg, hab⟩ := hinj
  have hfa : f a ≠ 0 := hf.ne_zero a
  have hla : (f a).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfa
  set c : ℚ := -((f b).leadingCoeff / (f a).leadingCoeff) with hc
  set g : Fin m → Polynomial ℚ := Function.update f b (f b + c • f a) with hg
  have hba : b ≠ a := fun h => hab h.symm
  have hgli : LinearIndependent ℚ g := by
    refine hf.update b _ ⟨1, one_mem _, Finsupp.single b 1 + Finsupp.single a c, ?_, ?_⟩
    · simp [hab]
    · simp [Finsupp.linearCombination_single, map_add]
  have hwr : a2_wr g = Matrix.updateCol (a2_wr f) b (fun k => a2_wr f k b + C c • a2_wr f k a) := by
    ext μ k : 1
    by_cases hk : k = b
    · subst hk
      simp [a2_wr, hg, smul_eq_C_mul]
    · simp [a2_wr, hg, hk]
  have hdet : (a2_wr g).det = (a2_wr f).det := by
    rw [hwr]; exact Matrix.det_updateCol_add_smul_self (a2_wr f) hba (C c)
  have hgb : g b = f b + c • f a := by simp [hg]
  have hgb0 : g b ≠ 0 := hgli.ne_zero b
  have hle : (g b).natDegree ≤ (f b).natDegree := by
    rw [hgb]
    refine (natDegree_add_le _ _).trans (max_le le_rfl ?_)
    exact (natDegree_smul_le _ _).trans (le_of_eq hdeg)
  have hcoef : (g b).coeff (f b).natDegree = 0 := by
    have hA : (f a).coeff (f b).natDegree = (f a).leadingCoeff := by rw [← hdeg]; rfl
    rw [hgb, coeff_add, coeff_smul, hA, smul_eq_mul]
    change (f b).leadingCoeff + c * (f a).leadingCoeff = 0
    rw [hc]; field_simp; ring
  have hlt : (g b).natDegree < (f b).natDegree := by
    refine lt_of_le_of_ne hle fun h => ?_
    have : (g b).leadingCoeff = 0 := by rw [leadingCoeff, h]; exact hcoef
    exact hgb0 (leadingCoeff_eq_zero.mp this)
  have hsum : ∑ k, (g k).natDegree < n := by
    rw [← hn]
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨b, Finset.mem_univ _, hlt⟩
    by_cases hk : k = b
    · subst hk; exact hle
    · simp [hg, hk]
  rw [← hdet]
  exact ih _ hsum g rfl hgli

theorem wronskian_ne_zero {m : ℕ} (f : Fin m → Polynomial ℚ) (hf : LinearIndependent ℚ f) :
    (Matrix.of fun (μ k : Fin m) => Polynomial.derivative^[(μ : ℕ)] (f k)).det ≠ 0 :=
  a2_wmain _ f rfl hf

theorem gauss_order_bound (U : Polynomial ℤ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime p (q : ℤ)) (e : ℕ)
    (hdvd : (Polynomial.X - Polynomial.C ((p : ℚ) / q)) ^ e ∣ U.map (Int.castRingHom ℚ)) :
    (q : ℤ) ^ e ∣ U.leadingCoeff := by
  set V : ℤ[X] := C (q : ℤ) * X + C (-p) with hV
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hVcoeff1 : V.coeff 1 = q := by
    rw [hV, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]; simp
  have hVcoeff0 : V.coeff 0 = -p := by
    rw [hV, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero]; simp
  have hVlc : V.leadingCoeff = q := leadingCoeff_linear hq0
  have hVprim : V.IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h1 := hr 1
    have h0 := hr 0
    rw [hVcoeff1] at h1
    rw [hVcoeff0, dvd_neg] at h0
    exact hcop.isUnit_of_dvd' h0 h1
  have hVpow : ∀ n : ℕ, (V ^ n).IsPrimitive := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact ih.mul hVprim
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmapV : V.map (Int.castRingHom ℚ) = C ((q : ℚ)) * (X - C ((p : ℚ) / q)) := by
    rw [hV, Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X, mul_sub, ← C_mul,
      mul_div_cancel₀ _ hq', sub_eq_add_neg, ← C_neg]
    simp
  have hdiv : V ^ e ∣ U := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (hVpow e), Polynomial.map_pow, hmapV,
      mul_pow, ← C_pow]
    have hu : IsUnit (C ((q : ℚ) ^ e)) :=
      isUnit_C.mpr (IsUnit.pow _ (isUnit_iff_ne_zero.mpr hq'))
    exact hu.mul_left_dvd.mpr hdvd
  obtain ⟨W, hW⟩ := hdiv
  rw [hW, leadingCoeff_mul, leadingCoeff_pow, hVlc]
  exact dvd_mul_right _ _

structure NormLike {R : Type*} [Ring R] (ν : R → ℝ) : Prop where
  zero : ν 0 = 0
  nonneg : ∀ a, 0 ≤ ν a
  add : ∀ a b, ν (a + b) ≤ ν a + ν b
  mul : ∀ a b, ν (a * b) ≤ ν a * ν b
  neg : ∀ a, ν (-a) = ν a
  one : ν 1 ≤ 1

noncomputable def L1 {R : Type*} [Semiring R] (ν : R → ℝ) (p : R[X]) : ℝ :=
  p.sum fun _ a => ν a

lemma L1_eq_sum {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) (p : R[X]) (s : Finset ℕ)
    (hs : p.support ⊆ s) : L1 ν p = ∑ i ∈ s, ν (p.coeff i) := by
  unfold L1
  rw [Polynomial.sum_def]
  apply Finset.sum_subset hs
  intro i _ hi
  rw [Polynomial.notMem_support_iff.mp hi, hν.zero]

lemma L1_monomial {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) (n : ℕ) (a : R) :
    L1 ν (monomial n a) = ν a := by
  unfold L1
  rw [Polynomial.sum_monomial_index]
  exact hν.zero

lemma L1_normLike {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) : NormLike (L1 ν) where
  zero := by simp [L1]
  nonneg := fun p => by
    unfold L1; rw [Polynomial.sum_def]; exact Finset.sum_nonneg fun i _ => hν.nonneg _
  add := fun p q => by
    classical
    rw [L1_eq_sum hν (p + q) (p.support ∪ q.support) Polynomial.support_add,
      L1_eq_sum hν p (p.support ∪ q.support) Finset.subset_union_left,
      L1_eq_sum hν q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact hν.add _ _
  mul := fun p q => by
    classical
    rw [Polynomial.mul_eq_sum_sum]
    have hsub : ∀ (s : Finset ℕ) (g : ℕ → R[X]), L1 ν (∑ i ∈ s, g i) ≤ ∑ i ∈ s, L1 ν (g i) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp [L1]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        refine le_trans ?_ (add_le_add le_rfl ih)
        rw [L1_eq_sum hν _ ((g a).support ∪ (∑ i ∈ s, g i).support) Polynomial.support_add,
          L1_eq_sum hν (g a) ((g a).support ∪ (∑ i ∈ s, g i).support) Finset.subset_union_left,
          L1_eq_sum hν (∑ i ∈ s, g i) ((g a).support ∪ (∑ i ∈ s, g i).support)
            Finset.subset_union_right, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact hν.add _ _
    refine le_trans (hsub _ _) ?_
    rw [L1_eq_sum hν p p.support subset_rfl, L1_eq_sum hν q q.support subset_rfl,
      Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Polynomial.sum_def]
    refine le_trans (hsub _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [L1_monomial hν]
    exact hν.mul _ _
  neg := fun p => by
    rw [L1_eq_sum hν (-p) p.support (by rw [Polynomial.support_neg]),
      L1_eq_sum hν p p.support subset_rfl]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_neg, hν.neg]
  one := by
    rw [← Polynomial.C_1, ← Polynomial.monomial_zero_left, L1_monomial hν]
    exact hν.one

lemma le_L1 {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) (p : R[X]) (i : ℕ) :
    ν (p.coeff i) ≤ L1 ν p := by
  classical
  rw [L1_eq_sum hν p (insert i p.support) (Finset.subset_insert _ _)]
  exact Finset.single_le_sum (f := fun j => ν (p.coeff j)) (fun j _ => hν.nonneg _)
    (Finset.mem_insert_self _ _)

lemma normLike_abs : NormLike (fun a : ℤ => (|a| : ℝ)) where
  zero := by simp
  nonneg := fun a => by positivity
  add := fun a b => by push_cast; exact abs_add_le _ _
  mul := fun a b => by push_cast; rw [abs_mul]
  neg := fun a => by push_cast; rw [abs_neg]
  one := by simp

lemma normLike_prod {R : Type*} [CommRing R] {ν : R → ℝ} (hν : NormLike ν) {ι : Type*}
    (s : Finset ι) (g : ι → R) : ν (∏ i ∈ s, g i) ≤ ∏ i ∈ s, ν (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hν.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (hν.mul _ _) (mul_le_mul_of_nonneg_left ih (hν.nonneg _))

lemma normLike_sum {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) {ι : Type*}
    (s : Finset ι) (g : ι → R) : ν (∑ i ∈ s, g i) ≤ ∑ i ∈ s, ν (g i) :=
  Finset.le_sum_of_subadditive ν hν.zero.le hν.add s g

lemma normLike_det {R : Type*} [CommRing R] {ν : R → ℝ} (hν : NormLike ν) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (B : ℝ) (hB : ∀ i j, ν (M i j) ≤ B) :
    ν M.det ≤ (n.factorial : ℝ) * B ^ n := by
  rw [Matrix.det_apply]
  refine le_trans (normLike_sum hν _ _) ?_
  have h1 : ∀ σ : Equiv.Perm (Fin n), ν (Equiv.Perm.sign σ • ∏ i, M (σ i) i) ≤ B ^ n := by
    intro σ
    have : ν (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ν (∏ i, M (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
      · rw [one_smul]
      · rw [Units.neg_smul, one_smul, hν.neg]
    rw [this]
    refine le_trans (normLike_prod hν _ _) ?_
    calc ∏ i, ν (M (σ i) i) ≤ ∏ _i : Fin n, B :=
          Finset.prod_le_prod (fun i _ => hν.nonneg _) (fun i _ => hB _ _)
      _ = B ^ n := by simp
  refine le_trans (Finset.sum_le_sum fun σ _ => h1 σ) ?_
  simp [Fintype.card_perm]

noncomputable def a2_L (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] ℚ[X] where
  toFun v := ∑ i : Fin n, monomial (i : ℕ) (v i)
  map_add' v w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_monomial]

lemma a2_L_apply (n : ℕ) (v : Fin n → ℚ) : a2_L n v = ∑ i : Fin n, monomial (i : ℕ) (v i) := rfl

lemma a2_L_coeff (n : ℕ) (v : Fin n → ℚ) (i : Fin n) : (a2_L n v).coeff i = v i := by
  rw [a2_L_apply, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [coeff_monomial, if_neg]; exact fun h => hb (Fin.ext h)
  · simp

lemma a2_L_ker (n : ℕ) : LinearMap.ker (a2_L n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv; funext i; have := a2_L_coeff n v i; rw [hv] at this; simpa using this.symm

lemma a2_L_natDegree (n : ℕ) (v : Fin (n+1) → ℚ) (k : ℕ) :
    (hasseDeriv k (a2_L (n+1) v)).natDegree < n + 1 := by
  refine lt_of_le_of_lt (natDegree_hasseDeriv_le _ _) ?_
  refine lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le ?_)
  rw [a2_L_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => le_trans (natDegree_monomial_le _) ?_
  exact Nat.lt_succ_iff.mp i.2

lemma a2_eval_hD_L (n : ℕ) (v : Fin n → ℚ) (i : ℕ) (x : ℚ) :
    (hasseDeriv i (a2_L n v)).eval x = ∑ j : Fin n, ((j : ℕ).choose i : ℚ) * v j * x ^ ((j : ℕ) - i) := by
  rw [a2_L_apply, map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_monomial, eval_monomial]

noncomputable def a2_HWm {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → R[X]) :
    Matrix (Fin m) (Fin m) R[X] :=
  Matrix.of fun (μ k : Fin m) => hasseDeriv (μ : ℕ) (f k)

noncomputable def a2_HW {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → R[X]) : R[X] :=
  (a2_HWm f).det

lemma a2_HW_ne_zero {m : ℕ} (f : Fin m → ℚ[X]) (hf : LinearIndependent ℚ f) : a2_HW f ≠ 0 := by
  have h := wronskian_ne_zero f hf
  have : (Matrix.of fun (μ k : Fin m) => derivative^[(μ : ℕ)] (f k)) =
      Matrix.of fun (μ k : Fin m) => (((μ : ℕ).factorial : ℚ[X])) * a2_HWm f μ k := by
    ext1 μ k
    simp only [Matrix.of_apply, a2_HWm]
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]
  rw [this, Matrix.det_mul_column] at h
  exact right_ne_zero_of_mul h

lemma a2_HW_comb {R : Type*} [CommRing R] {m : ℕ} (f h : Fin m → R[X])
    (G : Matrix (Fin m) (Fin m) R) (hf : ∀ k', f k' = ∑ k, G k' k • h k) :
    a2_HW f = C G.det * a2_HW h := by
  unfold a2_HW
  have : a2_HWm f = a2_HWm h * (C.mapMatrix G.transpose) := by
    refine Matrix.ext fun μ k' => ?_
    rw [Matrix.mul_apply]
    simp only [a2_HWm, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply]
    rw [hf, map_sum (hasseDeriv (μ : ℕ))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_C_mul, mul_comm]
  rw [this, Matrix.det_mul, ← RingHom.map_det, Matrix.det_transpose, mul_comm]

lemma a2_HW_map {m : ℕ} (f : Fin m → ℤ[X]) :
    a2_HW (fun k => (f k).map (Int.castRingHom ℚ)) = (a2_HW f).map (Int.castRingHom ℚ) := by
  unfold a2_HW
  rw [← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext μ k
  simp [a2_HWm, hasseDeriv_map]

noncomputable def a2_vecZ (n : ℕ) (v : Fin n → ℤ) : ℤ[X] := ∑ i : Fin n, monomial (i : ℕ) (v i)

lemma a2_vecZ_map (n : ℕ) (v : Fin n → ℤ) :
    (a2_vecZ n v).map (Int.castRingHom ℚ) = a2_L n (fun i => (v i : ℚ)) := by
  simp [a2_vecZ, a2_L_apply, Polynomial.map_sum]

lemma a2_L1_hD_vecZ (n : ℕ) (v : Fin (n+1) → ℤ) (H : ℝ) (hH : ∀ i, |(v i : ℝ)| ≤ H) (μ : ℕ) :
    L1 (fun a : ℤ => (|a| : ℝ)) (hasseDeriv μ (a2_vecZ (n+1) v)) ≤ (n + 1) * 2 ^ n * H := by
  have hν := L1_normLike normLike_abs
  rw [a2_vecZ, map_sum]
  refine le_trans (normLike_sum hν _ _) ?_
  have : ∀ i : Fin (n+1), L1 (fun a : ℤ => (|a| : ℝ)) (hasseDeriv μ (monomial (i : ℕ) (v i))) ≤
      2 ^ n * H := by
    intro i
    rw [hasseDeriv_monomial, L1_monomial normLike_abs]
    push_cast
    rw [abs_mul]
    have h1 : |((i : ℕ).choose μ : ℝ)| ≤ 2 ^ n := by
      rw [abs_of_nonneg (by positivity)]
      have := Nat.choose_le_two_pow (i : ℕ) μ
      have h2 : 2 ^ (i : ℕ) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp i.2)
      exact_mod_cast le_trans this h2
    exact mul_le_mul h1 (hH i) (abs_nonneg _) (by positivity)
  refine le_trans (Finset.sum_le_sum fun i _ => this i) ?_
  simp [mul_assoc]

lemma a2_gauss_bound {l : ℕ} (f : Fin l → ℤ[X]) (h : ℚ[X]) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime p (q : ℤ)) (B : ℝ)
    (hB : ∀ (μ : ℕ) k, L1 (fun a : ℤ => (|a| : ℝ)) (hasseDeriv μ (f k)) ≤ B)
    (hne : a2_HW (fun k => (f k).map (Int.castRingHom ℚ)) ≠ 0)
    (hdvd : h ∣ a2_HW (fun k => (f k).map (Int.castRingHom ℚ))) :
    (q : ℝ) ^ (rootMultiplicity ((p : ℚ) / q) h) ≤ (l.factorial : ℝ) * B ^ l := by
  rw [a2_HW_map] at hne hdvd
  set U := a2_HW f with hU
  have hU0 : U ≠ 0 := by rintro h0; apply hne; rw [h0, Polynomial.map_zero]
  have hd := gauss_order_bound U p q hq hcop _ (dvd_trans (pow_rootMultiplicity_dvd h _) hdvd)
  have hlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU0
  have h1 : q ^ (rootMultiplicity ((p : ℚ) / q) h) ≤ U.leadingCoeff.natAbs := by
    apply Nat.le_of_dvd (Int.natAbs_pos.mpr hlc)
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa [Int.natAbs_pow] using this
  have h2 : ((U.leadingCoeff.natAbs : ℕ) : ℝ) ≤ L1 (fun a : ℤ => (|a| : ℝ)) U := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact le_L1 normLike_abs U U.natDegree
  have h3 : L1 (fun a : ℤ => (|a| : ℝ)) U ≤ (l.factorial : ℝ) * B ^ l := by
    rw [hU, a2_HW]
    exact normLike_det (L1_normLike normLike_abs) _ B (fun μ k => hB μ k)
  calc (q : ℝ) ^ (rootMultiplicity ((p : ℚ) / q) h)
      = ((q ^ (rootMultiplicity ((p : ℚ) / q) h) : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := by exact_mod_cast h1
    _ ≤ _ := h2
    _ ≤ _ := h3

lemma a2_comp_expand (f : ℚ[X]) (x : ℚ) (r N : ℕ) (hN : f.natDegree < N) :
    f.comp (C x + X ^ r) = ∑ m ∈ range N, C ((hasseDeriv m f).eval x) * X ^ (r * m) := by
  have h1 : f.comp (C x + X ^ r) = (taylor x f).comp (X ^ r) := by
    rw [taylor_apply, comp_assoc]; congr 1; simp [add_comm]
  rw [h1]
  conv_lhs => rw [as_sum_range' (taylor x f) N (by rwa [natDegree_taylor])]
  rw [← coe_compRingHom_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_compRingHom_apply, monomial_comp, taylor_coeff, pow_mul]

lemma a2_det_dvd {R : Type*} [CommRing R] {l : ℕ} (M : Matrix (Fin l) (Fin l) R[X])
    (d : Fin l → ℕ) (h : ∀ i j, X ^ d j ∣ M i j) : X ^ (∑ j, d j) ∣ M.det := by
  rw [Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, Units.smul_def, zsmul_eq_mul]
  exact dvd_mul_of_dvd_right (Finset.prod_dvd_prod_of_dvd _ _ fun j _ => h _ _) _

lemma a2_entry_dvd {l : ℕ} (φ ψ : Fin l → ℚ[X]) (x y : ℚ) (r1 r2 N1 N2 d μ ν : ℕ)
    (h1 : ∀ k, (hasseDeriv μ (φ k)).natDegree < N1)
    (h2 : ∀ k, (hasseDeriv ν (ψ k)).natDegree < N2)
    (hT : ∀ m n, r2 * m + r1 * n < d →
      ∑ k, (hasseDeriv (m + μ) (φ k)).eval x * (hasseDeriv (n + ν) (ψ k)).eval y = 0) :
    X ^ d ∣ ∑ k, (hasseDeriv μ (φ k)).comp (C x + X ^ r2) *
      (hasseDeriv ν (ψ k)).comp (C y + X ^ r1) := by
  simp only [fun k => a2_comp_expand _ x r2 N1 (h1 k), fun k => a2_comp_expand _ y r1 N2 (h2 k),
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun n _ => ?_
  have key : ∑ k, C ((hasseDeriv m (hasseDeriv μ (φ k))).eval x) * X ^ (r2 * m) *
      (C ((hasseDeriv n (hasseDeriv ν (ψ k))).eval y) * X ^ (r1 * n)) =
      C (∑ k, (hasseDeriv m (hasseDeriv μ (φ k))).eval x *
        (hasseDeriv n (hasseDeriv ν (ψ k))).eval y) * X ^ (r2 * m + r1 * n) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul, pow_add]; ring
  rw [key]
  by_cases hd : d ≤ r2 * m + r1 * n
  · exact dvd_mul_of_dvd_right (pow_dvd_pow X hd) _
  · have hz : ∑ k, (hasseDeriv m (hasseDeriv μ (φ k))).eval x *
        (hasseDeriv n (hasseDeriv ν (ψ k))).eval y = 0 := by
      have e1 : ∀ f : ℚ[X], hasseDeriv m (hasseDeriv μ f) = (m + μ).choose m • hasseDeriv (m + μ) f :=
        fun f => LinearMap.congr_fun (hasseDeriv_comp m μ) f
      have e2 : ∀ f : ℚ[X], hasseDeriv n (hasseDeriv ν f) = (n + ν).choose n • hasseDeriv (n + ν) f :=
        fun f => LinearMap.congr_fun (hasseDeriv_comp n ν) f
      simp only [e1, e2, eval_smul, nsmul_eq_mul]
      have := hT m n (not_le.mp hd)
      calc _ = ((m + μ).choose m : ℚ) * ((n + ν).choose n : ℚ) * ∑ k, (hasseDeriv (m + μ) (φ k)).eval x
              * (hasseDeriv (n + ν) (ψ k)).eval y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by simp only [eval_mul, eval_natCast]; ring
        _ = 0 := by rw [this, mul_zero]
    rw [hz, C_0, zero_mul]
    exact dvd_zero _

lemma a2_ord_le (U V : ℚ[X]) (x y : ℚ) (r1 r2 D : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    (hU : U ≠ 0) (hV : V ≠ 0)
    (h : X ^ D ∣ U.comp (C x + X ^ r2) * V.comp (C y + X ^ r1)) :
    D ≤ r2 * rootMultiplicity x U + r1 * rootMultiplicity y V := by
  obtain ⟨R1, hU1, hR1⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd U hU x
  obtain ⟨R2, hV1, hR2⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd V hV y
  set e1 := rootMultiplicity x U
  set e2 := rootMultiplicity y V
  have hc1 : (X - C x).comp (C x + X ^ r2) = X ^ r2 := by simp
  have hc2 : (X - C y).comp (C y + X ^ r1) = X ^ r1 := by simp
  rw [hU1, hV1, mul_comp, mul_comp, pow_comp, pow_comp, hc1, hc2] at h
  have hG : (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)).eval 0 ≠ 0 := by
    rw [eval_mul, eval_comp, eval_comp]
    simp only [eval_add, eval_C, eval_pow, eval_X, zero_pow (by omega : r2 ≠ 0),
      zero_pow (by omega : r1 ≠ 0), add_zero]
    rw [dvd_iff_isRoot] at hR1 hR2
    exact mul_ne_zero hR1 hR2
  have hh : (X ^ r2) ^ e1 * R1.comp (C x + X ^ r2) * ((X ^ r1) ^ e2 * R2.comp (C y + X ^ r1)) =
      X ^ (r2 * e1 + r1 * e2) * (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)) := by
    rw [pow_add, pow_mul, pow_mul]; ring
  rw [hh] at h
  by_contra hlt
  push_neg at hlt
  have h' : X ^ (r2 * e1 + r1 * e2) * X ∣
      X ^ (r2 * e1 + r1 * e2) * (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)) :=
    dvd_trans (by rw [← pow_succ]; exact pow_dvd_pow X hlt) h
  rw [mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero), X_dvd_iff, coeff_zero_eq_eval_zero] at h'
  exact hG h'

lemma a2_lower {l : ℕ} (φ ψ : Fin l → ℚ[X]) (x y : ℚ) (r1 r2 N1 N2 : ℕ) (hr1 : 1 ≤ r1)
    (hr2 : 1 ≤ r2) (hU : a2_HW φ ≠ 0) (hV : a2_HW ψ ≠ 0) (d : Fin l → ℕ)
    (h1 : ∀ (μ : ℕ) k, (hasseDeriv μ (φ k)).natDegree < N1)
    (h2 : ∀ (ν : ℕ) k, (hasseDeriv ν (ψ k)).natDegree < N2)
    (hT : ∀ (μ ν : Fin l) (m n : ℕ), r2 * m + r1 * n < d ν →
      ∑ k, (hasseDeriv (m + μ) (φ k)).eval x * (hasseDeriv (n + ν) (ψ k)).eval y = 0) :
    ∑ ν, d ν ≤ r2 * rootMultiplicity x (a2_HW φ) + r1 * rootMultiplicity y (a2_HW ψ) := by
  apply a2_ord_le _ _ x y r1 r2 _ hr1 hr2 hU hV
  let A := (compRingHom (C x + X ^ r2)).mapMatrix (a2_HWm φ)
  let B := ((compRingHom (C y + X ^ r1)).mapMatrix (a2_HWm ψ)).transpose
  have hdet : (A * B).det = (a2_HW φ).comp (C x + X ^ r2) * (a2_HW ψ).comp (C y + X ^ r1) := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det]
    rfl
  rw [← hdet]
  apply a2_det_dvd
  intro μ ν
  have : (A * B) μ ν = ∑ k, (hasseDeriv μ (φ k)).comp (C x + X ^ r2) *
      (hasseDeriv ν (ψ k)).comp (C y + X ^ r1) := by
    simp [A, B, Matrix.mul_apply, a2_HWm]
  rw [this]
  exact a2_entry_dvd φ ψ x y r1 r2 N1 N2 (d ν) μ ν (h1 μ) (h2 ν) (hT μ ν)

lemma a2_basis {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℚ) : ∃ (l : ℕ) (I : Fin l → Fin n),
    LinearIndependent ℚ (fun k => M (I k)) ∧
    (∀ i, M i ∈ Submodule.span ℚ (Set.range fun k => M (I k))) ∧ l = M.transpose.rank := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ M
  haveI : Fintype κ := Fintype.ofInjective a ha
  let e := Fintype.equivFin κ
  have hli' : LinearIndependent ℚ ((M ∘ a) ∘ e.symm) := hli.comp e.symm e.symm.injective
  have hr : Set.range ((M ∘ a) ∘ e.symm) = Set.range (M ∘ a) := e.symm.surjective.range_comp _
  refine ⟨Fintype.card κ, a ∘ e.symm, hli', ?_, ?_⟩
  · intro i
    change M i ∈ Submodule.span ℚ (Set.range ((M ∘ a) ∘ e.symm))
    rw [hr, hspan]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Matrix.rank_eq_finrank_span_cols, ← finrank_span_eq_card hli, hspan]
    rfl

lemma a2_decomp (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) : ∃ (l : ℕ) (I : Fin l → Fin (r1+1))
    (J : Fin l → Fin (r2+1)) (g : Fin (r1+1) → Fin l → ℚ),
    LinearIndependent ℚ (fun k => a2_L (r2+1) (fun j => (c (I k) j : ℚ))) ∧
    LinearIndependent ℚ (fun k => a2_L (r1+1) (fun i => (c i (J k) : ℚ))) ∧
    ∀ (i : Fin (r1+1)) (j : Fin (r2+1)), (c i j : ℚ) = ∑ k, g i k * c (I k) j := by
  let M : Matrix (Fin (r1+1)) (Fin (r2+1)) ℚ := Matrix.of fun i j => (c i j : ℚ)
  obtain ⟨l, I, hI, hspan, hl⟩ := a2_basis M
  obtain ⟨l', J, hJ, -, hl'⟩ := a2_basis M.transpose
  have hll : l' = l := by rw [hl, hl', Matrix.transpose_transpose, Matrix.rank_transpose]
  subst hll
  have hex := fun i => (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hspan i)
  refine ⟨l', I, J, fun i => (hex i).choose, ?_, ?_, ?_⟩
  · exact hI.map' (a2_L _) (a2_L_ker _)
  · exact hJ.map' (a2_L _) (a2_L_ker _)
  · intro i j
    have := congr_fun (hex i).choose_spec j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, Matrix.of_apply] at this
    exact this.symm

lemma a2_hasseEval_eq (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) {l : ℕ} (I : Fin l → Fin (r1+1))
    (g : Fin (r1+1) → Fin l → ℚ)
    (hg : ∀ (i : Fin (r1+1)) (j : Fin (r2+1)), (c i j : ℚ) = ∑ k, g i k * c (I k) j)
    (i1 i2 : ℕ) (x y : ℚ) :
    hasseEval r1 r2 c i1 i2 (x : ℝ) (y : ℝ) =
     ((∑ k, (hasseDeriv i1 (a2_L (r1+1) (fun i => g i k))).eval x *
        (hasseDeriv i2 (a2_L (r2+1) (fun j => (c (I k) j : ℚ)))).eval y : ℚ) : ℝ) := by
  have h0 : hasseEval r1 r2 c i1 i2 (x : ℝ) (y : ℝ) = ((∑ i : Fin (r1+1), ∑ j : Fin (r2+1),
      (c i j : ℚ) * ((i : ℕ).choose i1 : ℚ) * ((j : ℕ).choose i2 : ℚ) * x ^ ((i : ℕ) - i1) *
        y ^ ((j : ℕ) - i2) : ℚ) : ℝ) := by
    unfold hasseEval
    simp_rw [Finset.sum_range]
    push_cast
    rfl
  rw [h0]
  congr 1
  simp only [a2_eval_hD_L, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hg i j, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma a2_hE_zero (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (x y : ℝ) (h : r1 < i1 ∨ r2 < i2) :
    hasseEval r1 r2 c i1 i2 x y = 0 := by
  unfold hasseEval
  refine Finset.sum_eq_zero fun k1 hk1 => Finset.sum_eq_zero fun k2 hk2 => ?_
  rw [Finset.mem_range] at hk1 hk2
  rcases h with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega : k1 < i1)]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : k2 < i2)]; simp

lemma a2_trivial (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (hc : BoxNonzero r1 r2 c) (x y : ℝ) :
    ∃ i1 ≤ r1, ∃ i2 ≤ r2, hasseEval r1 r2 c i1 i2 x y ≠ 0 := by
  classical
  let S1 := (range (r1+1)).filter (fun k1 => ∃ k2 ≤ r2, c k1 k2 ≠ 0)
  have hS1 : S1.Nonempty := by
    obtain ⟨k1, hk1, k2, hk2, hne⟩ := hc
    exact ⟨k1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), k2, hk2, hne⟩⟩
  let a := S1.max' hS1
  have ha := Finset.mem_filter.1 (S1.max'_mem hS1)
  have hamax : ∀ k1, k1 ∈ S1 → k1 ≤ a := fun k1 hk => S1.le_max' k1 hk
  let S2 := (range (r2+1)).filter (fun k2 => c a k2 ≠ 0)
  have hS2 : S2.Nonempty := by
    obtain ⟨k2, hk2, hne⟩ := ha.2
    exact ⟨k2, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hne⟩⟩
  let b := S2.max' hS2
  have hb := Finset.mem_filter.1 (S2.max'_mem hS2)
  have hbmax : ∀ k2, k2 ∈ S2 → k2 ≤ b := fun k2 hk => S2.le_max' k2 hk
  have har := Finset.mem_range.1 ha.1
  have hbr := Finset.mem_range.1 hb.1
  refine ⟨a, by omega, b, by omega, ?_⟩
  unfold hasseEval
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simpa using hb.2
  · intro k2 hk2 hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · have : c a k2 = 0 := by
        by_contra hc'
        have := hbmax k2 (Finset.mem_filter.2 ⟨hk2, hc'⟩); omega
      simp [this]
  · intro h; exact absurd hb.1 h
  · intro k1 hk1 hne
    refine Finset.sum_eq_zero fun k2 hk2 => ?_
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · have : c k1 k2 = 0 := by
        by_contra hc'
        have := hamax k1 (Finset.mem_filter.2 ⟨hk1, k2,
          Nat.lt_succ_iff.mp (Finset.mem_range.1 hk2), hc'⟩); omega
      simp [this]
  · intro h; exact absurd ha.1 h

lemma a2_sum_id (n : ℕ) : (∑ ν ∈ range n, (ν : ℝ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

lemma a2_S_big (r2 l : ℕ) (η : ℝ) (hr2 : 1 ≤ r2) (hl : 1 ≤ l) (hl2 : l ≤ r2 + 1) (hη : 0 < η)
    (hη4 : η ≤ 1/4) :
    2 * l * η < ∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2) := by
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hss : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
  set s := Real.sqrt η with hs
  have hs2 : s ≤ 1/2 := by nlinarith
  set T := 4 * s - η with hTdef
  have hT : 7/2 * s ≤ T := by nlinarith
  have hr2' : (0:ℝ) < r2 := by exact_mod_cast hr2
  have hl' : (1:ℝ) ≤ l := by exact_mod_cast hl
  have gen : ∀ n ≤ l, ((n:ℝ) - 1) ≤ T * r2 →
      n * T / 2 ≤ ∑ ν ∈ range l, max 0 (T - ν / r2) := by
    intro n hn hnT
    have hsum : (∑ ν ∈ range n, (ν:ℝ)) = n * (n - 1) / 2 := by linarith [a2_sum_id n]
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (∑ ν ∈ range n, (ν:ℝ)) / r2 ≤ n * T / 2 := by
      rw [div_le_iff₀ hr2', hsum]
      nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hnT)]
    calc (n:ℝ) * T / 2 ≤ ∑ ν ∈ range n, (T - ν / r2) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_div]
          linarith
      _ ≤ ∑ ν ∈ range n, max 0 (T - ν / r2) := Finset.sum_le_sum fun ν _ => le_max_right _ _
      _ ≤ ∑ ν ∈ range l, max 0 (T - ν / r2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn)
            (fun _ _ _ => le_max_left _ _)
  have hTr : 0 ≤ T * r2 := mul_nonneg (by linarith) hr2'.le
  by_cases hA : l ≤ ⌊T * r2⌋₊ + 1
  · have h1 : ((l:ℝ) - 1) ≤ T * r2 := by
      have : ((l:ℝ) - 1) ≤ (⌊T * r2⌋₊ : ℝ) := by
        have : (l:ℝ) ≤ (⌊T * r2⌋₊ : ℝ) + 1 := by exact_mod_cast hA
        linarith
      exact le_trans this (Nat.floor_le hTr)
    have := gen l le_rfl h1
    have h4 : 4 * η < T := by nlinarith
    have := mul_lt_mul_of_pos_left h4 (by linarith : (0:ℝ) < l)
    linarith
  · push_neg at hA
    set n := ⌊T * r2⌋₊ + 1 with hn
    have h1 : ((n:ℝ) - 1) ≤ T * r2 := by rw [hn]; push_cast; linarith [Nat.floor_le hTr]
    have := gen n hA.le h1
    have h2 : T * r2 < n := by rw [hn]; push_cast; exact Nat.lt_floor_add_one _
    have h3 : (l:ℝ) ≤ 2 * r2 := by
      have : (l:ℝ) ≤ r2 + 1 := by exact_mod_cast hl2
      have : (1:ℝ) ≤ r2 := by exact_mod_cast hr2
      linarith
    have hT0 : 0 < T := by linarith
    have h5 : T * r2 * T / 2 ≤ n * T / 2 := by
      have := mul_le_mul_of_nonneg_right h2.le hT0.le
      linarith
    have h6 : 49/4 * η ≤ T * T := by
      have h7 : 7/2 * s * (7/2 * s) ≤ T * T := mul_self_le_mul_self (by positivity) hT
      nlinarith
    have h7 : 49/8 * η * r2 ≤ T * r2 * T / 2 := by
      have := mul_le_mul_of_nonneg_right h6 hr2'.le
      nlinarith
    have h8 : 2 * l * η ≤ 4 * r2 * η := by
      have := mul_le_mul_of_nonneg_right h3 hη.le
      linarith
    have h9 : 0 < η * r2 := mul_pos hη hr2'
    nlinarith

lemma a2_final (r1 r2 l e1 e2 : ℕ) (H η : ℝ) (q1 q2 : ℕ)
    (hr2 : 1 ≤ r2) (hl : 1 ≤ l) (hl2 : l ≤ r2 + 1) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hr21 : (r2:ℝ) ≤ η * r1) (hH : 1 ≤ H) (hq1 : 0 < q1)
    (hq12 : (q1:ℝ) ^ r1 ≤ (q2:ℝ) ^ r2) (hbig : 64 ^ r1 * H ≤ (q1:ℝ) ^ (η * r1))
    (hu1 : (q1:ℝ) ^ e1 ≤ (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l)
    (hu2 : (q2:ℝ) ^ e2 ≤ (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l)
    (hlow : (r1:ℝ) * r2 * (∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2)) ≤
      r2 * e1 + r1 * e2) : False := by
  set S := ∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2) with hSdef
  have hS := a2_S_big r2 l η hr2 hl hl2 hη hη4
  rw [← hSdef] at hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hr2' : (1:ℝ) ≤ r2 := by exact_mod_cast hr2
  have hr1' : (1:ℝ) ≤ r1 := by
    rcases Nat.eq_zero_or_pos r1 with h | h
    · subst h; simp at hr21; linarith
    · exact_mod_cast h
  have hr1n : 1 ≤ r1 := by exact_mod_cast hr1'
  have h64 : (64:ℝ) ≤ 64 ^ r1 := le_self_pow₀ (by norm_num) (by omega)
  have hq1' : (1:ℝ) < q1 := by
    by_contra h
    push_neg at h
    have : q1 = 1 := by
      have : q1 ≤ 1 := by exact_mod_cast h
      omega
    subst this
    simp at hbig
    have := mul_le_mul h64 hH (by norm_num) (by positivity)
    linarith
  have hq1pos : (0:ℝ) < q1 := by linarith
  have hq2pos : (0:ℝ) < q2 := by
    rcases Nat.eq_zero_or_pos q2 with h | h
    · subst h
      have : (0:ℝ) < (q1:ℝ) ^ r1 := by positivity
      simp [zero_pow (by omega : r2 ≠ 0)] at hq12; linarith
    · exact_mod_cast h
  set B := (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l with hB
  have hBpos : 0 < B := by positivity
  set L := Real.log q1 with hL
  have hLpos : 0 < L := Real.log_pos hq1'
  have he1 : (e1:ℝ) * L ≤ Real.log B := by
    have := Real.log_le_log (by positivity) hu1
    rwa [Real.log_pow] at this
  have he2 : (e2:ℝ) * Real.log q2 ≤ Real.log B := by
    have := Real.log_le_log (by positivity) hu2
    rwa [Real.log_pow] at this
  have hq12L : (r1:ℝ) * L ≤ r2 * Real.log q2 := by
    have := Real.log_le_log (by positivity) hq12
    rwa [Real.log_pow, Real.log_pow] at this

  have hchain : (r1:ℝ) * S * L ≤ 2 * Real.log B := by
    have e0 : (0:ℝ) ≤ e2 := Nat.cast_nonneg _
    have k1' : (r1:ℝ) * r2 * S * L ≤ (r2 * e1 + r1 * e2) * L := mul_le_mul_of_nonneg_right hlow hLpos.le
    have k2 : (e2:ℝ) * (r1 * L) ≤ e2 * (r2 * Real.log q2) := mul_le_mul_of_nonneg_left hq12L e0
    have k3 : (r2:ℝ) * (e1 * L) ≤ r2 * Real.log B := mul_le_mul_of_nonneg_left he1 (by linarith)
    have k4 : (r2:ℝ) * (e2 * Real.log q2) ≤ r2 * Real.log B := mul_le_mul_of_nonneg_left he2 (by linarith)
    have : (r1:ℝ) * S * L * r2 ≤ 2 * Real.log B * r2 := by
      calc (r1:ℝ) * S * L * r2 = (r1 * r2 * S) * L := by ring
        _ ≤ (r2 * e1 + r1 * e2) * L := k1'
        _ = r2 * (e1 * L) + e2 * (r1 * L) := by ring
        _ ≤ r2 * Real.log B + e2 * (r2 * Real.log q2) := add_le_add k3 k2
        _ = r2 * Real.log B + r2 * (e2 * Real.log q2) := by ring
        _ ≤ r2 * Real.log B + r2 * Real.log B := add_le_add le_rfl k4
        _ = 2 * Real.log B * r2 := by ring
    exact le_of_mul_le_mul_right this (by linarith)

  have hA64 : Real.log (64 ^ r1 * H) ≤ η * r1 * L := by
    have := Real.log_le_log (by positivity) hbig
    rwa [Real.log_rpow hq1pos] at this
  have hB8 : B ≤ (8 ^ r1 * H) ^ l := by
    have hf : (l.factorial : ℝ) ≤ ((r1:ℝ) + 1) ^ l := by
      have h1 : l.factorial ≤ l ^ l := Nat.factorial_le_pow l
      have h2 : l ^ l ≤ (r1 + 1) ^ l := Nat.pow_le_pow_left (by
        have : (r2:ℝ) ≤ r1 := le_trans hr21 (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith))
        have : r2 ≤ r1 := by exact_mod_cast this
        omega) l
      exact_mod_cast le_trans h1 h2
    have hr : ((r1:ℝ) + 1) ≤ 2 ^ r1 := by
      have := Nat.lt_two_pow_self (n := r1)
      exact_mod_cast this
    calc B ≤ ((r1:ℝ) + 1) ^ l * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l :=
          mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (((r1:ℝ) + 1) * ((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l := by rw [← mul_pow]; ring_nf
      _ ≤ (2 ^ r1 * 2 ^ r1 * 2 ^ r1 * H) ^ l := by
          gcongr
      _ = (8 ^ r1 * H) ^ l := by
          congr 1; rw [show (8:ℝ) = 2 * 2 * 2 by norm_num, mul_pow, mul_pow]
  have hlogB : Real.log B ≤ l * Real.log (8 ^ r1 * H) := by
    have := Real.log_le_log hBpos hB8
    rwa [Real.log_pow] at this
  have hA8pos : 0 < Real.log (8 ^ r1 * H) := Real.log_pos (by
    have : (8:ℝ) ≤ 8 ^ r1 := le_self_pow₀ (by norm_num) (by omega)
    calc (1:ℝ) < 8 := by norm_num
      _ ≤ 8 ^ r1 := this
      _ ≤ 8 ^ r1 * H := le_mul_of_one_le_right (by positivity) hH)
  have hA8 : Real.log (8 ^ r1 * H) < Real.log (64 ^ r1 * H) := by
    apply Real.log_lt_log (by positivity)
    have : (8:ℝ) ^ r1 < 64 ^ r1 := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    exact mul_lt_mul_of_pos_right this (by linarith)

  have c1 : S * Real.log (64 ^ r1 * H) ≤ S * (η * r1 * L) := mul_le_mul_of_nonneg_left hA64 hS0
  have c2 : S * (η * r1 * L) ≤ η * (2 * Real.log B) := by
    have := mul_le_mul_of_nonneg_left hchain hη.le
    calc S * (η * r1 * L) = η * (r1 * S * L) := by ring
      _ ≤ _ := this
  have c3 : η * (2 * Real.log B) ≤ η * (2 * (l * Real.log (8 ^ r1 * H))) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hl0 : (0:ℝ) < l := by exact_mod_cast hl
  have c4 : 2 * l * η * Real.log (64 ^ r1 * H) < S * Real.log (64 ^ r1 * H) :=
    mul_lt_mul_of_pos_right hS (by linarith)
  have c5 : η * (2 * (l * Real.log (8 ^ r1 * H))) ≤ 2 * l * η * Real.log (64 ^ r1 * H) := by
    have := mul_le_mul_of_nonneg_left hA8.le (by positivity : (0:ℝ) ≤ 2 * l * η)
    calc η * (2 * (l * Real.log (8 ^ r1 * H))) = 2 * l * η * Real.log (8 ^ r1 * H) := by ring
      _ ≤ _ := this
  linarith

end RL2

theorem roth_lemma_two (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (H η : ℝ) (p1 p2 : ℤ) (q1 q2 : ℕ)
    (hr2 : 1 ≤ r2) (hη : 0 < η) (hη1 : η ≤ 1) (hr21 : (r2 : ℝ) ≤ η * r1)
    (hc : BoxNonzero r1 r2 c) (hH : ∀ k1 k2, |(c k1 k2 : ℝ)| ≤ H)
    (hq1 : 0 < q1) (hq2 : 0 < q2) (hcop1 : IsCoprime p1 (q1 : ℤ))
    (hcop2 : IsCoprime p2 (q2 : ℤ))
    (hq12 : (q1 : ℝ) ^ r1 ≤ (q2 : ℝ) ^ r2)
    (hbig : 64 ^ r1 * H ≤ (q1 : ℝ) ^ (η * r1)) :
    ∃ i1 ≤ r1, ∃ i2 ≤ r2, (i1 : ℝ) / r1 + (i2 : ℝ) / r2 < 4 * Real.sqrt η ∧
      hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) ≠ 0 := by
  classical
  by_cases hη4 : η ≤ 1/4
  swap
  · obtain ⟨i1, hi1, i2, hi2, hne⟩ := RL2.a2_trivial r1 r2 c hc ((p1:ℝ)/q1) ((p2:ℝ)/q2)
    refine ⟨i1, hi1, i2, hi2, ?_, hne⟩
    have h1 : (i1:ℝ)/r1 ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hi1) (Nat.cast_nonneg _)
    have h2 : (i2:ℝ)/r2 ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hi2) (Nat.cast_nonneg _)
    have : 1/2 < Real.sqrt η := by
      rw [Real.lt_sqrt (by norm_num)]; push_neg at hη4; linarith
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨l, I, J, g, hLIrow, hLIcol, hg⟩ := RL2.a2_decomp r1 r2 c
  have hr2' : (1:ℝ) ≤ r2 := by exact_mod_cast hr2
  have hr2r1 : r2 ≤ r1 := by
    have : (r2:ℝ) ≤ r1 := le_trans hr21 (mul_le_of_le_one_left (Nat.cast_nonneg _) hη1)
    exact_mod_cast this
  have hr1 : 1 ≤ r1 := le_trans hr2 hr2r1
  have hr1' : (1:ℝ) ≤ r1 := by exact_mod_cast hr1

  have hH1 : 1 ≤ H := by
    obtain ⟨k1, _, k2, _, hne⟩ := hc
    have : (1:ℝ) ≤ |(c k1 k2 : ℝ)| := by
      have := Int.one_le_abs hne
      rw [← Int.cast_abs]; exact_mod_cast this
    exact le_trans this (hH k1 k2)

  have hl : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0
      obtain ⟨k1, hk1, k2, hk2, hne⟩ := hc
      have := hg ⟨k1, by omega⟩ ⟨k2, by omega⟩
      simp at this
      exact absurd this hne
    · exact h0

  have hl2 : l ≤ r2 + 1 := by
    have hinj : Function.Injective J := by
      have := hLIcol.injective
      exact Function.Injective.of_comp (f := fun j : Fin (r2+1) =>
        RL2.a2_L (r1+1) (fun i => (c i j : ℚ))) this
    simpa using Fintype.card_le_of_injective J hinj

  set φ : Fin l → ℚ[X] := fun k => RL2.a2_L (r1+1) (fun i => g i k) with hφ
  set ψ : Fin l → ℚ[X] := fun k => RL2.a2_L (r2+1) (fun j => (c (I k) j : ℚ)) with hψ
  set colQ : Fin l → ℚ[X] := fun k => RL2.a2_L (r1+1) (fun i => (c i (J k) : ℚ)) with hcolQ
  have hcomb : ∀ k', colQ k' = ∑ k, (c (I k) (J k') : ℚ) • φ k := by
    intro k'
    have : (fun i : Fin (r1+1) => (c i (J k') : ℚ)) =
        ∑ k, (c (I k) (J k') : ℚ) • (fun i : Fin (r1+1) => g i k) := by
      funext i
      rw [Finset.sum_apply, hg i (J k')]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    simp only [hcolQ, hφ]
    rw [this, map_sum]
    simp
  have hWcol := RL2.a2_HW_comb colQ φ (Matrix.of fun k' k => (c (I k) (J k') : ℚ))
    (fun k' => by rw [hcomb k']; rfl)
  have hWcol_ne : RL2.a2_HW colQ ≠ 0 := RL2.a2_HW_ne_zero colQ hLIcol
  have hφ_ne : RL2.a2_HW φ ≠ 0 := by
    intro h0; apply hWcol_ne; rw [hWcol, h0, mul_zero]
  have hψ_ne : RL2.a2_HW ψ ≠ 0 := RL2.a2_HW_ne_zero ψ hLIrow
  set xq : ℚ := (p1 : ℚ) / q1 with hxq
  set yq : ℚ := (p2 : ℚ) / q2 with hyq

  have hmapc : (fun k => (RL2.a2_vecZ (r1+1) (fun i : Fin (r1+1) => c i (J k))).map
      (Int.castRingHom ℚ)) = colQ := funext fun k => by rw [RL2.a2_vecZ_map]
  have hmapr : (fun k => (RL2.a2_vecZ (r2+1) (fun j : Fin (r2+1) => c (I k) j)).map
      (Int.castRingHom ℚ)) = ψ := funext fun k => by rw [RL2.a2_vecZ_map]
  have hu1 := RL2.a2_gauss_bound (fun k => RL2.a2_vecZ (r1+1) (fun i : Fin (r1+1) => c i (J k)))
    (RL2.a2_HW φ) p1 q1 hq1 hcop1 (((r1:ℝ) + 1) * 2 ^ r1 * H)
    (fun μ k => RL2.a2_L1_hD_vecZ r1 _ H (fun i => hH _ _) μ)
    (by rw [hmapc]; exact hWcol_ne) (by rw [hmapc, hWcol]; exact dvd_mul_left _ _)
  have hu2' := RL2.a2_gauss_bound (fun k => RL2.a2_vecZ (r2+1) (fun j : Fin (r2+1) => c (I k) j))
    (RL2.a2_HW ψ) p2 q2 hq2 hcop2 (((r2:ℝ) + 1) * 2 ^ r2 * H)
    (fun μ k => RL2.a2_L1_hD_vecZ r2 _ H (fun i => hH _ _) μ)
    (by rw [hmapr]; exact hψ_ne) (by rw [hmapr])
  have hu2 : (q2:ℝ) ^ (rootMultiplicity yq (RL2.a2_HW ψ)) ≤
      (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l := by
    refine le_trans hu2' (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine pow_le_pow_left₀ (by positivity) ?_ l
    have a1 : ((r2:ℝ) + 1) ≤ r1 + 1 := by
      have : (r2:ℝ) ≤ r1 := by exact_mod_cast hr2r1
      linarith
    have a2 : (2:ℝ) ^ r2 ≤ 2 ^ r1 := pow_le_pow_right₀ (by norm_num) hr2r1
    have a3 : 0 ≤ H := by linarith
    gcongr

  set T : ℝ := 4 * Real.sqrt η - η with hT
  let d : Fin l → ℕ := fun ν => ⌈(r1:ℝ) * r2 * (T - (ν : ℕ) / r2)⌉₊
  have hlow := RL2.a2_lower φ ψ xq yq r1 r2 (r1+1) (r2+1) hr1 hr2 hφ_ne hψ_ne d
    (fun μ k => RL2.a2_L_natDegree r1 _ μ) (fun ν k => RL2.a2_L_natDegree r2 _ ν) (by
      intro μ ν m n hmn
      have hcast := RL2.a2_hasseEval_eq r1 r2 c I g hg (m + μ) (n + ν) xq yq
      have hz : hasseEval r1 r2 c (m + μ) (n + ν) (xq : ℝ) (yq : ℝ) = 0 := by
        by_cases hb : r1 < m + μ ∨ r2 < n + ν
        · exact RL2.a2_hE_zero r1 r2 c _ _ _ _ hb
        · push_neg at hb
          have ex : ((xq : ℚ) : ℝ) = (p1 : ℝ) / q1 := by rw [hxq]; push_cast; rfl
          have ey : ((yq : ℚ) : ℝ) = (p2 : ℝ) / q2 := by rw [hyq]; push_cast; rfl
          rw [ex, ey]
          apply hcon _ hb.1 _ hb.2
          have hlt : ((r2 * m + r1 * n : ℕ) : ℝ) < (r1:ℝ) * r2 * (T - (ν : ℕ) / r2) :=
            Nat.lt_ceil.mp hmn
          have hμ : ((μ : ℕ) : ℝ) ≤ η * r1 := by
            have : (μ : ℕ) ≤ r2 := by have := μ.2; omega
            exact le_trans (by exact_mod_cast this) hr21
          have hr1p : (0:ℝ) < r1 := by linarith
          have hr2p : (0:ℝ) < r2 := by linarith
          rw [div_add_div _ _ hr1p.ne' hr2p.ne', div_lt_iff₀ (mul_pos hr1p hr2p)]
          have e3 : (r1:ℝ) * r2 * (T - (ν : ℕ) / r2) = r1 * r2 * T - r1 * (ν : ℕ) := by
            field_simp
          rw [e3] at hlt
          push_cast at hlt ⊢
          have hμ2 : ((μ : ℕ) : ℝ) * r2 ≤ η * r1 * r2 := mul_le_mul_of_nonneg_right hμ hr2p.le
          rw [hT] at hlt
          nlinarith
      rw [hcast] at hz
      exact_mod_cast hz)

  apply RL2.a2_final r1 r2 l (rootMultiplicity xq (RL2.a2_HW φ))
    (rootMultiplicity yq (RL2.a2_HW ψ)) H η q1 q2 hr2 hl hl2 hη hη4 hr21 hH1 hq1 hq12 hbig hu1 hu2
  have hsum : (r1:ℝ) * r2 * (∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2)) ≤
      ∑ ν : Fin l, (d ν : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_range (fun ν => (r1:ℝ) * r2 * max 0 (4 * Real.sqrt η - η - ν / r2))]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
    exact max_le (Nat.cast_nonneg _) (Nat.le_ceil _)
  refine le_trans hsum ?_
  exact_mod_cast hlow

end OMA494
end

-- TaylorUpperBound
section
namespace OMA494

open Finset

lemma taylor_uni (i k N : ℕ) (hk : k ≤ i + N) (θ u : ℝ) :
    (k.choose i : ℝ) * (θ + u) ^ (k - i) =
      ∑ j ∈ range (N + 1),
        ((i + j).choose i : ℝ) * (k.choose (i + j) : ℝ) * θ ^ (k - (i + j)) * u ^ j := by
  by_cases h : k < i
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [Nat.choose_eq_zero_of_lt (by omega : k < i + j)]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = i + m := ⟨k - i, by omega⟩
    have hm : m ≤ N := by omega
    rw [Nat.add_sub_cancel_left, add_comm θ u, add_pow, Finset.mul_sum]
    have hsub : range (m + 1) ⊆ range (N + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    rw [← Finset.sum_subset hsub (f := fun j =>
      ((i + j).choose i : ℝ) * ((i + m).choose (i + j) : ℝ) * θ ^ (i + m - (i + j)) * u ^ j) ?_]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hc : (i + m).choose (i + j) * (i + j).choose i
          = (i + m).choose i * m.choose j := by
        rw [Nat.choose_mul (by omega)]
        congr 2 <;> omega
      have hc' : ((i + m).choose (i + j) : ℝ) * ((i + j).choose i : ℝ)
          = ((i + m).choose i : ℝ) * (m.choose j : ℝ) := by exact_mod_cast hc
      rw [Nat.add_sub_add_left]
      linear_combination (-(u ^ j * θ ^ (m - j))) * hc'
    · intro j _ hj'
      simp only [Finset.mem_range] at hj'
      rw [Nat.choose_eq_zero_of_lt (by omega : i + m < i + j)]
      simp

lemma hasseEval_eq_zero_left (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (m1 m2 : ℕ) (h : r1 < m1) (x y : ℝ) :
    hasseEval r1 r2 c m1 m2 x y = 0 := by
  unfold hasseEval
  apply Finset.sum_eq_zero
  intro k1 hk1
  apply Finset.sum_eq_zero
  intro k2 _
  simp only [Finset.mem_range] at hk1
  rw [Nat.choose_eq_zero_of_lt (by omega : k1 < m1)]
  simp

lemma hasseEval_eq_zero_right (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (m1 m2 : ℕ) (h : r2 < m2) (x y : ℝ) :
    hasseEval r1 r2 c m1 m2 x y = 0 := by
  unfold hasseEval
  apply Finset.sum_eq_zero
  intro k1 _
  apply Finset.sum_eq_zero
  intro k2 hk2
  simp only [Finset.mem_range] at hk2
  rw [Nat.choose_eq_zero_of_lt (by omega : k2 < m2)]
  simp

lemma hasseEval_taylor (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (θ u v : ℝ) :
    hasseEval r1 r2 c i1 i2 (θ + u) (θ + v) =
      ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1),
        ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ * u ^ j1 * v ^ j2 := by
  have key : ∀ k1 ∈ range (r1 + 1), ∀ k2 ∈ range (r2 + 1),
      (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * (θ + u) ^ (k1 - i1)
        * (θ + v) ^ (k2 - i2) =
      ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1),
        ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          ((c k1 k2 : ℝ) * (k1.choose (i1 + j1) : ℝ) * (k2.choose (i2 + j2) : ℝ) *
            θ ^ (k1 - (i1 + j1)) * θ ^ (k2 - (i2 + j2))) * u ^ j1 * v ^ j2 := by
    intro k1 hk1 k2 hk2
    simp only [Finset.mem_range] at hk1 hk2
    have e1 := taylor_uni i1 k1 (r1 - i1) (by omega) θ u
    have e2 := taylor_uni i2 k2 (r2 - i2) (by omega) θ v
    calc (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * (θ + u) ^ (k1 - i1)
          * (θ + v) ^ (k2 - i2)
        = (c k1 k2 : ℝ) * ((k1.choose i1 : ℝ) * (θ + u) ^ (k1 - i1)) *
            ((k2.choose i2 : ℝ) * (θ + v) ^ (k2 - i2)) := by ring
      _ = _ := by
        rw [e1, e2, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j1 _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j2 _
        ring
  unfold hasseEval
  rw [Finset.sum_congr rfl (fun k1 hk1 => Finset.sum_congr rfl (fun k2 hk2 => key k1 hk1 k2 hk2))]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, k1, 2, j1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j1]; rw [Finset.sum_comm]

lemma hasseEval_abs_le (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (H : ℝ)
    (hH : ∀ k1 k2, |(c k1 k2 : ℝ)| ≤ H) (m1 m2 : ℕ) (θ : ℝ) :
    |hasseEval r1 r2 c m1 m2 θ θ| ≤
      ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) *
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0 0)
  unfold hasseEval
  calc _ ≤ ∑ k1 ∈ range (r1 + 1), ∑ k2 ∈ range (r2 + 1),
        |(c k1 k2 : ℝ) * (k1.choose m1 : ℝ) * (k2.choose m2 : ℝ) * θ ^ (k1 - m1) *
          θ ^ (k2 - m2)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k1 ∈ range (r1 + 1), ∑ k2 ∈ range (r2 + 1),
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) := by
      apply Finset.sum_le_sum
      intro k1 hk1
      apply Finset.sum_le_sum
      intro k2 hk2
      simp only [Finset.mem_range] at hk1 hk2
      have ht1 : |θ| ^ (k1 - m1) ≤ (|θ| + 1) ^ r1 :=
        (pow_le_pow_left₀ (abs_nonneg θ) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg θ]) (by omega))
      have ht2 : |θ| ^ (k2 - m2) ≤ (|θ| + 1) ^ r2 :=
        (pow_le_pow_left₀ (abs_nonneg θ) (by linarith) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg θ]) (by omega))
      have hc1 : (k1.choose m1 : ℝ) ≤ 2 ^ r1 := by
        have : k1.choose m1 ≤ 2 ^ r1 :=
          (Nat.choose_le_two_pow k1 m1).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast this
      have hc2 : (k2.choose m2 : ℝ) ≤ 2 ^ r2 := by
        have : k2.choose m2 ≤ 2 ^ r2 :=
          (Nat.choose_le_two_pow k2 m2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast this
      calc _ = |θ| ^ (k1 - m1) * |θ| ^ (k2 - m2) * (k1.choose m1 : ℝ) * (k2.choose m2 : ℝ) *
            |(c k1 k2 : ℝ)| := by
            simp only [abs_mul, abs_pow, Nat.abs_cast]; ring
        _ ≤ _ := by gcongr; exact hH k1 k2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

theorem taylor_upper_bound (r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) (c : ℕ → ℕ → ℤ) (H : ℝ)
    (hH : ∀ k1 k2, |(c k1 k2 : ℝ)| ≤ H) (θ t Θ0 Λ : ℝ)
    (hvan : ∀ i1 i2 : ℕ, (i1 : ℝ) / r1 + (i2 : ℝ) / r2 < t → hasseEval r1 r2 c i1 i2 θ θ = 0)
    (i1 i2 : ℕ) (hi : (i1 : ℝ) / r1 + (i2 : ℝ) / r2 ≤ Θ0) (hΘ : Θ0 ≤ t)
    (hΛ0 : 0 < Λ) (hΛ1 : Λ ≤ 1) (x y : ℝ)
    (hx : |x - θ| ≤ Λ ^ ((1 : ℝ) / r1)) (hy : |y - θ| ≤ Λ ^ ((1 : ℝ) / r2)) :
    |hasseEval r1 r2 c i1 i2 x y| ≤
      ((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * 8 ^ (r1 + r2) * H * (|θ| + 1) ^ (r1 + r2) *
        Λ ^ (t - Θ0) := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0 0)
  obtain ⟨Bh, hBh0, hBhe, hBh⟩ : ∃ Bh : ℝ, 0 ≤ Bh ∧
      Bh = ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) *
        ((|θ| + 1) ^ r1 * (|θ| + 1) ^ r2 * 2 ^ r1 * 2 ^ r2 * H) ∧
      ∀ m1 m2 : ℕ, |hasseEval r1 r2 c m1 m2 θ θ| ≤ Bh :=
    ⟨_, by positivity, rfl, fun m1 m2 => hasseEval_abs_le r1 r2 c H hH m1 m2 θ⟩
  have hL0 : 0 ≤ Λ ^ (t - Θ0) := Real.rpow_nonneg hΛ0.le _
  have hr1' : (0 : ℝ) < r1 := by exact_mod_cast hr1
  have hr2' : (0 : ℝ) < r2 := by exact_mod_cast hr2
  have hxe : x = θ + (x - θ) := by ring
  have hye : y = θ + (y - θ) := by ring
  rw [hxe, hye, hasseEval_taylor]
  set u := x - θ
  set v := y - θ
  set M : ℝ := 2 ^ r1 * 2 ^ r2 * Bh * Λ ^ (t - Θ0) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ j1 j2 : ℕ,
      |((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ * u ^ j1 * v ^ j2| ≤ M := by
    intro j1 j2
    by_cases hw : (((i1 + j1 : ℕ) : ℝ) / r1 + ((i2 + j2 : ℕ) : ℝ) / r2 < t)
    · rw [hvan _ _ hw]; simpa using hM0
    by_cases h1 : r1 < i1 + j1
    · rw [hasseEval_eq_zero_left _ _ _ _ _ h1]; simpa using hM0
    by_cases h2 : r2 < i2 + j2
    · rw [hasseEval_eq_zero_right _ _ _ _ _ h2]; simpa using hM0
    have hc1 : ((i1 + j1).choose i1 : ℝ) ≤ 2 ^ r1 := by
      have : (i1 + j1).choose i1 ≤ 2 ^ r1 :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have hc2 : ((i2 + j2).choose i2 : ℝ) ≤ 2 ^ r2 := by
      have : (i2 + j2).choose i2 ≤ 2 ^ r2 :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have hexp : t - Θ0 ≤ (j1 : ℝ) / r1 + (j2 : ℝ) / r2 := by
      push_cast [add_div] at hw
      linarith
    have hpow : ∀ (r j : ℕ) (w : ℝ), |w| ≤ Λ ^ ((1 : ℝ) / r) →
        |w| ^ j ≤ Λ ^ ((j : ℝ) / r) := by
      intro r j w hw
      calc |w| ^ j ≤ (Λ ^ ((1 : ℝ) / r)) ^ j := pow_le_pow_left₀ (abs_nonneg w) hw j
        _ = Λ ^ ((j : ℝ) / r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]
          congr 1
          ring
    have huv : |u| ^ j1 * |v| ^ j2 ≤ Λ ^ (t - Θ0) := by
      calc |u| ^ j1 * |v| ^ j2 ≤ Λ ^ ((j1 : ℝ) / r1) * Λ ^ ((j2 : ℝ) / r2) :=
            mul_le_mul (hpow r1 j1 u hx) (hpow r2 j2 v hy) (by positivity)
              (Real.rpow_nonneg hΛ0.le _)
        _ = Λ ^ ((j1 : ℝ) / r1 + (j2 : ℝ) / r2) := (Real.rpow_add hΛ0 _ _).symm
        _ ≤ Λ ^ (t - Θ0) := Real.rpow_le_rpow_of_exponent_ge hΛ0 hΛ1 hexp
    calc _ = ((i1 + j1).choose i1 : ℝ) * ((i2 + j2).choose i2 : ℝ) *
          |hasseEval r1 r2 c (i1 + j1) (i2 + j2) θ θ| * (|u| ^ j1 * |v| ^ j2) := by
          simp only [abs_mul, abs_pow, Nat.abs_cast]; ring
      _ ≤ M := by
        rw [hM]
        gcongr
        exact hBh _ _
  calc _ ≤ ∑ j1 ∈ range (r1 - i1 + 1), ∑ j2 ∈ range (r2 - i2 + 1), M :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j1 _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j2 _ => hterm j1 j2))
    _ = ((r1 - i1 + 1 : ℕ) : ℝ) * ((r2 - i2 + 1 : ℕ) : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) * M := by
      have e1 : ((r1 - i1 + 1 : ℕ) : ℝ) ≤ (r1 : ℝ) + 1 := by
        have : r1 - i1 + 1 ≤ r1 + 1 := by omega
        exact_mod_cast this
      have e2 : ((r2 - i2 + 1 : ℕ) : ℝ) ≤ (r2 : ℝ) + 1 := by
        have : r2 - i2 + 1 ≤ r2 + 1 := by omega
        exact_mod_cast this
      gcongr
    _ = ((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ r1 * 2 ^ r1 * (2 ^ r2 * 2 ^ r2)) *
          H * (|θ| + 1) ^ (r1 + r2) * Λ ^ (t - Θ0) := by
      rw [hM, hBhe, pow_add]; ring
    _ ≤ _ := by
      have h8 : (2 : ℝ) ^ r1 * 2 ^ r1 * (2 ^ r2 * 2 ^ r2) ≤ 8 ^ (r1 + r2) := by
        rw [← mul_pow, ← mul_pow, pow_add]
        gcongr <;> norm_num
      gcongr

end OMA494
end

-- RationalLowerBound
section
namespace OMA494

lemma rlb_pow_clear (p : ℤ) (q : ℕ) (hq : 0 < q) (m r : ℕ) (h : m ≤ r) :
    (q : ℝ) ^ r * ((p : ℝ) / q) ^ m = (p : ℝ) ^ m * (q : ℝ) ^ (r - m) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, div_pow, pow_add]
  field_simp

theorem rational_lower_bound (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (p1 p2 : ℤ) (q1 q2 : ℕ)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hne : hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) ≠ 0) :
    1 ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      |hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)| := by
  set N : ℤ := ∑ k1 ∈ Finset.range (r1 + 1), ∑ k2 ∈ Finset.range (r2 + 1),
    c k1 k2 * (k1.choose i1 : ℤ) * (k2.choose i2 : ℤ) * p1 ^ (k1 - i1) *
      (q1 : ℤ) ^ (r1 - (k1 - i1)) * p2 ^ (k2 - i2) * (q2 : ℤ) ^ (r2 - (k2 - i2)) with hN
  have key : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) = (N : ℝ) := by
    rw [hN, hasseEval]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 hk1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 hk2 => ?_
    have h1 : k1 - i1 ≤ r1 := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1))
    have h2 : k2 - i2 ≤ r2 := le_trans (Nat.sub_le _ _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk2))
    have e1 := rlb_pow_clear p1 q1 hq1 _ _ h1
    have e2 := rlb_pow_clear p2 q2 hq2 _ _ h2
    calc (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
          ((c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) *
            ((p1 : ℝ) / q1) ^ (k1 - i1) * ((p2 : ℝ) / q2) ^ (k2 - i2))
        = (c k1 k2 : ℝ) * (k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) *
            ((q1 : ℝ) ^ r1 * ((p1 : ℝ) / q1) ^ (k1 - i1)) *
            ((q2 : ℝ) ^ r2 * ((p2 : ℝ) / q2) ^ (k2 - i2)) := by ring
      _ = _ := by rw [e1, e2]; ring
  have hNne : N ≠ 0 := by
    intro h0
    have hq1' : (q1 : ℝ) ^ r1 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq1.ne')
    have hq2' : (q2 : ℝ) ^ r2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq2.ne')
    have : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
        hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2) = 0 := by
      rw [key, h0]; simp
    exact hne (by simpa [hq1', hq2'] using this)
  have hpos : (0 : ℝ) ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 := by positivity
  have habs : (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      |hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)| = |(N : ℝ)| := by
    rw [← key, abs_mul, abs_of_nonneg hpos]
  rw [habs]
  have : (1 : ℤ) ≤ |N| := Int.one_le_abs hNne
  exact_mod_cast this

end OMA494
end

-- DysonBinomial
section
namespace OMA494

namespace DysonAux

def Sol (θ κ : ℝ) (pq : ℤ × ℕ) : Prop :=
  0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ θ ∧ |θ - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)

lemma pow_eq_exp (y : ℝ) (hy : 0 < y) (n : ℕ) : y ^ n = Real.exp (n * Real.log y) := by
  rw [Real.exp_nat_mul, Real.exp_log hy]

lemma box_finite (T : Set (ℤ × ℕ)) (B : ℝ)
    (h : ∀ v ∈ T, |(v.1 : ℝ)| ≤ B ∧ (v.2 : ℝ) ≤ B) : T.Finite := by
  apply ((Set.finite_Icc (-(⌈B⌉₊ : ℤ)) (⌈B⌉₊ : ℤ)).prod (Set.finite_Iic ⌈B⌉₊)).subset
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  have h1' : ((|v.1| : ℤ) : ℝ) ≤ ((⌈B⌉₊ : ℤ) : ℝ) := by
    push_cast; exact h1.trans (Nat.le_ceil B)
  have h1'' : |v.1| ≤ (⌈B⌉₊ : ℤ) := by exact_mod_cast h1'
  have h2' : v.2 ≤ ⌈B⌉₊ := by exact_mod_cast h2.trans (Nat.le_ceil B)
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp h1''), Set.mem_Iic.mpr h2'⟩

lemma sol_abs_le (θ κ : ℝ) (hκ : 0 ≤ κ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (h : |θ - (p : ℝ) / q| < (q : ℝ) ^ (-κ)) : |(p : ℝ)| ≤ (|θ| + 1) * q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq' (by linarith)
  have h2 : |(p : ℝ) / q| ≤ |θ| + 1 := by
    have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) θ
    rw [abs_sub_comm] at this
    linarith
  rw [abs_div, Nat.abs_cast, div_le_iff₀ (by linarith)] at h2
  exact h2

lemma choose_degrees (r : ℕ) (hr1 : (1 : ℝ) ≤ r) (η L1 L2 : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηM : η * (12800 * r) = 2) (hL1 : 0 < L1) (hcon : 12800 * (r : ℝ) * L1 ≤ L2) :
    ∃ r1 r2 : ℕ, 16 * r ≤ r2 ∧ r2 ≤ r1 ∧ 1 ≤ r1 ∧ 1 ≤ r2 ∧
      (r1 : ℝ) * L1 ≤ r2 * L2 ∧ (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) ∧ (r2 : ℝ) ≤ η * r1 := by
  have hM1 : (12800 : ℝ) ≤ 12800 * r := by linarith
  have hL2 : 0 < L2 := by
    have := mul_pos (by positivity : (0 : ℝ) < 12800 * r) hL1
    linarith
  set r1 := ⌈12800 * (r : ℝ) * (L2 / L1)⌉₊ with hr1def
  set r2 := ⌈(r1 : ℝ) * L1 / L2⌉₊ with hr2def
  have hρ : 12800 * (r : ℝ) ≤ L2 / L1 := (le_div_iff₀ hL1).mpr hcon
  have hR1 : 12800 * (r : ℝ) * (L2 / L1) ≤ r1 := Nat.le_ceil _
  have hR1L : 12800 * (r : ℝ) * L2 ≤ r1 * L1 := by
    have := mul_le_mul_of_nonneg_right hR1 hL1.le
    rwa [mul_assoc, div_mul_cancel₀ _ hL1.ne'] at this
  have hR1ge : 12800 * (r : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ L2 / L1 by linarith)
      (by positivity : (0 : ℝ) ≤ 12800 * r)
    linarith
  have hR2a : (r1 : ℝ) * L1 / L2 ≤ r2 := Nat.le_ceil _
  have hR2b : (r2 : ℝ) < r1 * L1 / L2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq12L : (r1 : ℝ) * L1 ≤ r2 * L2 := (div_le_iff₀ hL2).mp hR2a
  have hR2L2 : (r2 : ℝ) * L2 < r1 * L1 + L2 := by
    have := mul_lt_mul_of_pos_right hR2b hL2
    rwa [add_mul, div_mul_cancel₀ _ hL2.ne', one_mul] at this
  have hL2η : L2 ≤ η * (r1 * L1) := by
    have e : η * (12800 * r * L2) = 2 * L2 := by rw [← mul_assoc, hηM]
    have := mul_le_mul_of_nonneg_left hR1L hη0.le
    linarith
  have hR1L1 : 0 ≤ (r1 : ℝ) * L1 := by positivity
  have hupper : (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) := by
    linarith [mul_le_mul_of_nonneg_right hη1 hR1L1]
  have hR2ge : 12800 * (r : ℝ) ≤ r2 := by
    have : 12800 * (r : ℝ) ≤ r1 * L1 / L2 := (le_div_iff₀ hL2).mpr hR1L
    linarith
  have hR2η : (r2 : ℝ) ≤ η * r1 := by
    have hsm : (r1 : ℝ) * L1 / L2 ≤ η * r1 / 2 := by
      rw [div_le_iff₀ hL2]
      have hL1le : L1 ≤ η / 2 * L2 := by
        have := mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ η / 2)
        have e : η / 2 * (12800 * r * L1) = L1 := by
          rw [show η / 2 * (12800 * r * L1) = (η * (12800 * r)) / 2 * L1 by ring, hηM]; ring
        linarith
      have := mul_le_mul_of_nonneg_left hL1le (by positivity : (0 : ℝ) ≤ r1)
      linarith
    have hηr1 : 2 ≤ η * r1 := by
      have := mul_le_mul_of_nonneg_left hR1ge hη0.le
      linarith
    linarith
  have hR21 : (r2 : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_right hη1 (by positivity : (0 : ℝ) ≤ r1)
    linarith
  have h16 : 16 * r ≤ r2 := by
    have : ((16 * r : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  have h21 : r2 ≤ r1 := by exact_mod_cast hR21
  have hr1' : 1 ≤ r1 := by
    have : ((1 : ℕ) : ℝ) ≤ r1 := by push_cast; linarith
    exact_mod_cast this
  have hr2' : 1 ≤ r2 := by
    have : ((1 : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  exact ⟨r1, r2, h16, h21, hr1', hr2', hq12L, hupper, hR2η⟩

lemma key_lt (r1 r2 q1 q2 : ℕ) (hq1R : (0 : ℝ) < q1) (hq2R : (0 : ℝ) < q2)
    (K θ κ t : ℝ) (hK1 : 1 ≤ K) (hR1pos : (0 : ℝ) < r1) (hR21 : (r2 : ℝ) ≤ r1)
    (hupper : (r2 : ℝ) * Real.log q2 ≤ 2 * (r1 * Real.log q1))
    (hκt : 9 / 2 ≤ κ * t)
    (hL1X : 8 + 4 * (Real.log 8 + Real.log K + Real.log (|θ| + 1)) < 3 * Real.log q1)
    (hL1 : 0 ≤ Real.log q1) :
    (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      (((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * 8 ^ (r1 + r2) * K ^ (r1 + r2) *
        (|θ| + 1) ^ (r1 + r2) * ((q1 : ℝ) ^ (-(κ * r1))) ^ t) < 1 := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogθ : 0 ≤ Real.log (|θ| + 1) := Real.log_nonneg (by linarith [abs_nonneg θ])
  have hR1L1 : 0 ≤ (r1 : ℝ) * Real.log q1 := mul_nonneg hR1pos.le hL1
  have hb1 : ((r1 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r1) := by
    rw [show (2 : ℝ) * r1 = ((2 : ℕ) : ℝ) * r1 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r1 : ℝ)]
  have hb2 : ((r2 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r2) := by
    rw [show (2 : ℝ) * r2 = ((2 : ℕ) : ℝ) * r2 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r2 : ℝ)]
  rw [pow_eq_exp _ hq1R, pow_eq_exp _ hq2R, pow_eq_exp 8 (by norm_num),
    pow_eq_exp K (by linarith), pow_eq_exp (|θ| + 1) (by positivity),
    ← Real.rpow_mul hq1R.le, Real.rpow_def_of_pos hq1R]
  calc _ ≤ Real.exp (r1 * Real.log q1) * Real.exp (r2 * Real.log q2) *
        (Real.exp (2 * r1) * Real.exp (2 * r2) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log 8) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log K) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log (|θ| + 1)) *
          Real.exp (Real.log q1 * (-(κ * r1) * t))) := by
        gcongr
    _ < 1 := by
        simp only [← Real.exp_add]
        rw [Real.exp_lt_one_iff]
        push_cast
        have e1 := mul_le_mul_of_nonneg_right hR21 hlog8
        have e2 := mul_le_mul_of_nonneg_right hR21 hlogK
        have e3 := mul_le_mul_of_nonneg_right hR21 hlogθ
        have e4 := mul_le_mul_of_nonneg_right hκt hR1L1
        have e5 := mul_lt_mul_of_pos_left hL1X hR1pos
        linarith

lemma core (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) (κ : ℝ)
    (hκ : 10 * Real.sqrt r ≤ κ) :
    ∃ A : ℝ, ∀ (p1 p2 : ℤ) (q1 q2 : ℕ), 0 < q1 → 0 < q2 → IsCoprime p1 (q1 : ℤ) →
      IsCoprime p2 (q2 : ℤ) →
      |binRoot r a b - (p1 : ℝ) / q1| < (q1 : ℝ) ^ (-κ) →
      |binRoot r a b - (p2 : ℝ) / q2| < (q2 : ℝ) ^ (-κ) →
      A ≤ Real.log q1 → Real.log q2 < 12800 * r * Real.log q1 := by
  obtain ⟨K, hK1, hK⟩ := aux_polynomial r a b hr ha hb
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = binRoot r a b := ⟨_, rfl⟩
  rw [← hθ] at hK
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (r : ℝ) := ⟨_, rfl⟩
  rw [← hs] at hK hκ
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by linarith)
  have hss : s * s = r := by rw [hs]; exact Real.mul_self_sqrt (by linarith)
  have hκ0 : 0 < κ := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (6400 * r) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by positivity)]; linarith
  have hηM : η * (12800 * r) = 2 := by
    rw [hη, div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]; ring
  have hsqη : Real.sqrt η = 1 / (80 * s) := by
    rw [show η = (1 / (80 * s)) ^ 2 by rw [hη, ← hss]; ring]
    exact Real.sqrt_sq (by positivity)
  have hΘt : 4 * Real.sqrt η ≤ 1 / (2 * s) := by
    rw [hsqη, show 4 * (1 / (80 * s)) = 1 / (20 * s) by ring]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hκt : 9 / 2 ≤ κ * (1 / (2 * s) - 4 * Real.sqrt η) := by
    rw [hsqη, show 1 / (2 * s) - 4 * (1 / (80 * s)) = 9 / (20 * s) by field_simp; ring,
      ← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogθ : 0 ≤ Real.log (|θ| + 1) := Real.log_nonneg (by linarith [abs_nonneg θ])
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  set X := Real.log 8 + Real.log K + Real.log (|θ| + 1) with hX
  have hX0 : 0 ≤ X := by linarith
  refine ⟨1 + (Real.log 64 + 2 * Real.log K) / η + (8 + 4 * X) / 3, ?_⟩
  intro p1 p2 q1 q2 hq1 hq2 hcop1 hcop2 h1 h2 hA
  rw [← hθ] at h1 h2
  by_contra hcon
  push_neg at hcon
  have hq1R : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
  set L1 := Real.log (q1 : ℝ) with hL1def
  set L2 := Real.log (q2 : ℝ) with hL2def
  have hA1 : 0 ≤ (Real.log 64 + 2 * Real.log K) / η := by positivity
  have hA2 : 0 ≤ (8 + 4 * X) / 3 := by positivity
  have hL1 : 0 < L1 := by linarith
  have hηL1 : Real.log 64 + 2 * Real.log K ≤ η * L1 := by
    have : (Real.log 64 + 2 * Real.log K) / η ≤ L1 := by linarith
    rw [div_le_iff₀ hη0] at this; linarith
  have hL1X : 8 + 4 * X < 3 * L1 := by
    have : (8 + 4 * X) / 3 < L1 := by linarith
    linarith
  have hM1 : (12800 : ℝ) ≤ 12800 * r := by linarith
  have hL2 : 0 < L2 := by
    have := mul_pos (by positivity : (0 : ℝ) < 12800 * r) hL1
    linarith

  obtain ⟨r1, r2, h16, h21, hr1', hr2', hq12L, hupper, hR2η⟩ :=
    choose_degrees r hr1 η L1 L2 hη0 hη1 hηM hL1 hcon
  have hR21 : (r2 : ℝ) ≤ r1 := by exact_mod_cast h21
  have hR1L1 : 0 ≤ (r1 : ℝ) * L1 := by positivity
  have hR1pos : (0 : ℝ) < r1 := by exact_mod_cast hr1'
  have hR2pos : (0 : ℝ) < r2 := by exact_mod_cast hr2'

  obtain ⟨c, hcnz, hcH, hcvan⟩ := hK r1 r2 h16 h21

  have hq12 : (q1 : ℝ) ^ r1 ≤ (q2 : ℝ) ^ r2 := by
    rw [pow_eq_exp _ hq1R, pow_eq_exp _ hq2R]
    exact Real.exp_le_exp.mpr hq12L
  have hbig : (64 : ℝ) ^ r1 * K ^ (r1 + r2) ≤ (q1 : ℝ) ^ (η * r1) := by
    rw [pow_eq_exp 64 (by norm_num), pow_eq_exp K (by linarith), ← Real.exp_add,
      Real.rpow_def_of_pos hq1R]
    apply Real.exp_le_exp.mpr
    push_cast
    have e1 := mul_le_mul_of_nonneg_left hηL1 hR1pos.le
    have e2 := mul_le_mul_of_nonneg_right hR21 hlogK
    rw [← hL1def]
    linarith
  obtain ⟨i1, -, i2, -, hwt, hne⟩ := roth_lemma_two r1 r2 c (K ^ (r1 + r2)) η p1 p2 q1 q2
    hr2' hη0 hη1 hR2η hcnz hcH hq1 hq2 hcop1 hcop2 hq12 hbig

  have hvan : ∀ j1 j2 : ℕ, (j1 : ℝ) / r1 + (j2 : ℝ) / r2 < 1 / (2 * s) →
      hasseEval r1 r2 c j1 j2 θ θ = 0 := by
    intro j1 j2 hj
    exact hcvan j1 j2 ((lt_div_iff₀ (by positivity)).mp hj)
  have hΛ0 : 0 < (q1 : ℝ) ^ (-(κ * r1)) := Real.rpow_pos_of_pos hq1R _
  have hΛ1 : (q1 : ℝ) ^ (-(κ * r1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq1) (by nlinarith)
  have hx : |(p1 : ℝ) / q1 - θ| ≤ ((q1 : ℝ) ^ (-(κ * r1))) ^ ((1 : ℝ) / r1) := by
    rw [← Real.rpow_mul hq1R.le, show -(κ * (r1 : ℝ)) * (1 / r1) = -κ by field_simp,
      abs_sub_comm]
    exact h1.le
  have hy : |(p2 : ℝ) / q2 - θ| ≤ ((q1 : ℝ) ^ (-(κ * r1))) ^ ((1 : ℝ) / r2) := by
    rw [← Real.rpow_mul hq1R.le, abs_sub_comm]
    refine h2.le.trans ?_
    rw [Real.rpow_def_of_pos hq2R, Real.rpow_def_of_pos hq1R]
    apply Real.exp_le_exp.mpr
    rw [← hL1def, ← hL2def,
      show L1 * (-(κ * (r1 : ℝ)) * (1 / r2)) = -(κ * (r1 * L1)) / r2 by field_simp,
      le_div_iff₀ hR2pos]
    linarith [mul_le_mul_of_nonneg_left hq12L hκ0.le]
  have hT := taylor_upper_bound r1 r2 hr1' hr2' c (K ^ (r1 + r2)) hcH θ (1 / (2 * s))
    (4 * Real.sqrt η) ((q1 : ℝ) ^ (-(κ * r1))) hvan i1 i2 hwt.le hΘt hΛ0 hΛ1 _ _ hx hy
  have hL := rational_lower_bound r1 r2 c i1 i2 p1 p2 q1 q2 hq1 hq2 hne
  set D := hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)
  have hQ0 : 0 ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 := by positivity
  have key := key_lt r1 r2 q1 q2 hq1R hq2R K θ κ (1 / (2 * s) - 4 * Real.sqrt η) hK1 hR1pos
    hR21 hupper hκt hL1X hL1.le
  have := mul_le_mul_of_nonneg_left hT hQ0
  linarith

end DysonAux

open DysonAux in
theorem dyson_binomial (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) (κ : ℝ)
    (hκ : 10 * Real.sqrt r ≤ κ) :
    {pq : ℤ × ℕ | 0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ binRoot r a b ∧
        |binRoot r a b - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)}.Finite := by
  obtain ⟨A, hA⟩ := core r a b hr ha hb κ hκ
  have hκ0 : 0 < κ := by
    have : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
    linarith
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = binRoot r a b := ⟨_, rfl⟩
  rw [← hθ] at hA ⊢
  change {pq : ℤ × ℕ | Sol θ κ pq}.Finite
  set R : Set (ℤ × ℕ) := {pq | Sol θ κ pq ∧ IsCoprime pq.1 (pq.2 : ℤ)} with hR
  have hRbd : ∃ B : ℝ, ∀ v ∈ R, (v.2 : ℝ) ≤ B := by
    by_cases h : ∃ v ∈ R, A ≤ Real.log v.2
    · obtain ⟨⟨p1, q1⟩, ⟨⟨hq1, -, h1⟩, hc1⟩, hL⟩ := h
      refine ⟨Real.exp (12800 * r * Real.log q1), ?_⟩
      rintro ⟨p2, q2⟩ ⟨⟨hq2, -, h2⟩, hc2⟩
      have := hA p1 p2 q1 q2 hq1 hq2 hc1 hc2 h1 h2 hL
      have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
      rw [← Real.exp_log hq2R]
      exact (Real.exp_lt_exp.mpr this).le
    · push_neg at h
      refine ⟨Real.exp A, ?_⟩
      rintro ⟨p, q⟩ hv
      have hqR : (0 : ℝ) < q := by exact_mod_cast hv.1.1
      rw [← Real.exp_log hqR]
      exact (Real.exp_lt_exp.mpr (h _ hv)).le
  obtain ⟨B, hB⟩ := hRbd
  have hRfin : R.Finite := by
    apply box_finite R ((|θ| + 1) * |B| + |B|)
    rintro ⟨p, q⟩ hv
    have hq := hB _ hv
    have hqB : (q : ℝ) ≤ |B| := hq.trans (le_abs_self B)
    have hp := sol_abs_le θ κ hκ0.le p q hv.1.1 hv.1.2.2
    have : (|θ| + 1) * (q : ℝ) ≤ (|θ| + 1) * |B| :=
      mul_le_mul_of_nonneg_left hqB (by positivity)
    have : 0 ≤ (|θ| + 1) * |B| := by positivity
    exact ⟨by simp only; linarith [abs_nonneg B], by simp only; linarith⟩

  let F : ℤ × ℕ → Set (ℤ × ℕ) :=
    fun v => {w | Sol θ κ w ∧ (w.1 : ℝ) / w.2 = (v.1 : ℝ) / v.2}
  have hFfin : ∀ v ∈ R, (F v).Finite := by
    rintro ⟨p0, q0⟩ hv
    have hδ : 0 < |θ - (p0 : ℝ) / q0| :=
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hv.1.2.1))
    set E := Real.exp (-Real.log |θ - (p0 : ℝ) / q0| / κ) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    apply box_finite _ ((|θ| + 1) * E + E)
    rintro ⟨p, q⟩ ⟨hw, hpq⟩
    simp only at hpq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hw.1
    have hlt : |θ - (p0 : ℝ) / q0| < (q : ℝ) ^ (-κ) := by rw [← hpq]; exact hw.2.2
    have hlog : Real.log |θ - (p0 : ℝ) / q0| < Real.log q * (-κ) := by
      rw [← Real.exp_lt_exp, Real.exp_log hδ, ← Real.rpow_def_of_pos hqR]; exact hlt
    have hlq : Real.log q < -Real.log |θ - (p0 : ℝ) / q0| / κ := by
      rw [lt_div_iff₀ hκ0]; linarith
    have hqE : (q : ℝ) ≤ E := by
      rw [← Real.exp_log hqR, hE]; exact (Real.exp_lt_exp.mpr hlq).le
    have hp := sol_abs_le θ κ hκ0.le p q hw.1 hw.2.2
    have : (|θ| + 1) * (q : ℝ) ≤ (|θ| + 1) * E :=
      mul_le_mul_of_nonneg_left hqE (by positivity)
    have : 0 ≤ (|θ| + 1) * E := by positivity
    exact ⟨by simp only; linarith, by simp only; linarith⟩
  refine (hRfin.biUnion hFfin).subset ?_
  rintro ⟨p, q⟩ hw
  have hq : 0 < q := hw.1
  set x : ℚ := Rat.divInt p q with hx
  have hval : (x.num : ℝ) / (x.den : ℝ) = (p : ℝ) / q := by
    rw [← Rat.cast_def, hx, ← Rat.intCast_div_eq_divInt]
    push_cast; rfl
  have hden : x.den ≤ q := by
    have h1 : ((x.den : ℤ)) ∣ (q : ℤ) := Rat.den_dvd p q
    have h2 : (x.den : ℤ) ≤ (q : ℤ) := Int.le_of_dvd (by exact_mod_cast hq) h1
    exact_mod_cast h2
  have hdenpos : 0 < x.den := x.den_pos
  refine Set.mem_biUnion (x := (x.num, x.den)) ?_ ?_
  · refine ⟨⟨hdenpos, ?_, ?_⟩, Rat.isCoprime_num_den x⟩
    · show (x.num : ℝ) / (x.den : ℝ) ≠ θ
      rw [hval]; exact hw.2.1
    · show |θ - (x.num : ℝ) / (x.den : ℝ)| < ((x.den : ℕ) : ℝ) ^ (-κ)
      rw [hval]
      refine lt_of_lt_of_le hw.2.2 ?_
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hdenpos)
        (by exact_mod_cast hden) (by linarith)
  · exact ⟨hw, hval.symm⟩

end OMA494
end

-- RidoutSmooth
section
namespace OMA494

lemma ridout_decomp (P r : ℕ) (hr : 0 < r) (x : ℕ) (hx : x ∈ Nat.smoothNumbers P) :
    ∃ a u : ℕ, 0 < a ∧ a ≤ ((P + 1) ^ r) ^ P ∧ 0 < u ∧ x = a * u ^ r := by
  have hx0 : x ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hx
  have hsub : x.primeFactors ⊆ Finset.range P :=
    ((Nat.mem_smoothNumbers_iff_primeFactors_subset.1 hx).2).trans (Finset.filter_subset _ _)
  refine ⟨∏ p ∈ x.primeFactors, p ^ (x.factorization p % r),
    ∏ p ∈ x.primeFactors, p ^ (x.factorization p / r), ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · calc ∏ p ∈ x.primeFactors, p ^ (x.factorization p % r)
          ≤ ∏ _p ∈ x.primeFactors, (P + 1) ^ r := by
            apply Finset.prod_le_prod' fun p hp => ?_
            have hpP : p < P := Finset.mem_range.1 (hsub hp)
            have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
            calc p ^ (x.factorization p % r) ≤ p ^ r :=
                  Nat.pow_le_pow_right hp1 (Nat.mod_lt _ hr).le
              _ ≤ (P + 1) ^ r := Nat.pow_le_pow_left (by omega) _
        _ = ((P + 1) ^ r) ^ x.primeFactors.card := Finset.prod_const _
        _ ≤ ((P + 1) ^ r) ^ P := by
            apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by positivity))
            simpa using Finset.card_le_card hsub
  · exact Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hx0]
    rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add, mul_comm (x.factorization p / r) r, Nat.mod_add_div]

lemma ridout_pow_sub_pow (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    |α - β| * β ^ (n - 1) ≤ |α ^ n - β ^ n| := by
  rw [← geom_sum₂_mul, abs_mul, mul_comm]
  gcongr
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
  have := Finset.single_le_sum (f := fun i => α ^ i * β ^ (n - 1 - i))
    (fun i _ => by positivity) h0
  simpa using this

lemma ridout_core (P : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P →
      Nat.Coprime x y → x ≤ y → B < y →
      ((y : ℕ) : ℝ) ^ (1 - δ) ≤ |(x : ℝ) - y| := by

  obtain ⟨k, hk⟩ : ∃ k : ℕ, 10 / δ < k := exists_nat_gt _
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hkN : 0 < k := by exact_mod_cast hk0
  set r : ℕ := k ^ 2 with hr_def
  have hr : 0 < r := by positivity
  set κ : ℝ := 10 * k with hκ_def
  set ε : ℝ := 10 / k with hε_def
  have hεδ : ε < δ := by
    rw [hε_def, div_lt_iff₀ hk0]; rw [div_lt_iff₀ hδ] at hk; linarith
  have hε0 : 0 < ε := by positivity
  have hκ : 10 * Real.sqrt r ≤ κ := by
    rw [hr_def]; push_cast; rw [Real.sqrt_sq hk0.le]
  set A0 : ℕ := ((P + 1) ^ r) ^ P with hA0
  have hA0pos : 0 < A0 := by positivity
  have hA0R : (1 : ℝ) ≤ A0 := by exact_mod_cast hA0pos

  set S : Set (ℤ × ℕ) := ⋃ a ∈ Finset.Icc 1 A0, ⋃ b ∈ Finset.Icc 1 A0,
    {pq : ℤ × ℕ | 0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ binRoot r a b ∧
        |binRoot r a b - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)} with hS
  have hSfin : S.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun a ha => ?_
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun b hb => ?_
    have ha' := (Finset.mem_Icc.1 ha).1
    have hb' := (Finset.mem_Icc.1 hb).1
    exact dyson_binomial r a b hr ha' hb' κ hκ
  set N : ℕ := hSfin.toFinset.sup (fun pq => pq.2) with hN
  set T : ℝ := ((A0 : ℝ) ^ 2) ^ (1 / (δ - ε)) with hT
  refine ⟨⌈T⌉₊ + A0 * N ^ r + 1, by omega, ?_⟩
  intro x y hx hy hxy hxy' hB
  by_contra hbad
  push Not at hbad
  obtain ⟨a, u, ha0, haA, hu0, rfl⟩ := ridout_decomp P r hr x hx
  obtain ⟨b, v, hb0, hbA, hv0, rfl⟩ := ridout_decomp P r hr y hy

  have hne : a * u ^ r ≠ b * v ^ r := by
    intro h
    rw [h, Nat.coprime_self] at hxy
    omega
  set β : ℝ := binRoot r a b with hβ
  have hβ0 : 0 ≤ β := Real.rpow_nonneg (by positivity) _
  have hβr : β ^ r = (b : ℝ) / a := by
    rw [hβ, binRoot, one_div]
    exact Real.rpow_inv_natCast_pow (by positivity) hr.ne'
  have huv_ne : (u : ℝ) / v ≠ β := by
    intro h
    apply hne
    have h2 : ((u : ℝ) / v) ^ r = (b : ℝ) / a := by rw [h, hβr]
    have hv : (v : ℝ) ≠ 0 := by positivity
    have ha : (a : ℝ) ≠ 0 := by positivity
    rw [div_pow, div_eq_div_iff (by positivity) ha] at h2
    exact_mod_cast (by linarith : (a : ℝ) * u ^ r = b * v ^ r)

  have hnotS : ((u : ℤ), v) ∉ S := by
    intro hmem
    have hle : v ≤ N := by
      rw [hN]
      exact Finset.le_sup (f := fun pq : ℤ × ℕ => pq.2) (hSfin.mem_toFinset.2 hmem)
    have : b * v ^ r ≤ A0 * N ^ r := Nat.mul_le_mul hbA (Nat.pow_le_pow_left hle _)
    omega
  have hlow : (v : ℝ) ^ (-κ) ≤ |β - (u : ℝ) / v| := by
    by_contra hlt
    push Not at hlt
    apply hnotS
    rw [hS]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨a, ⟨ha0, haA⟩, b, ⟨hb0, hbA⟩, hv0, ?_, ?_⟩
    · push_cast; exact huv_ne
    · push_cast; exact hlt

  set w : ℝ := (v : ℝ) ^ r with hw
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv0
  have hw0 : 0 < w := by positivity
  have hwκ : (v : ℝ) ^ (-κ) = w ^ (-ε) := by
    rw [hw, ← Real.rpow_natCast_mul (by positivity)]
    congr 1
    rw [hr_def, hκ_def, hε_def]; push_cast; field_simp
  set M : ℝ := ((b * v ^ r : ℕ) : ℝ) with hM
  have hMw : M = b * w := by rw [hM, hw]; push_cast; ring
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  set D : ℝ := |((a * u ^ r : ℕ) : ℝ) - ((b * v ^ r : ℕ) : ℝ)| with hD

  have hβr1 : 1 / (A0 : ℝ) ≤ β ^ (r - 1) := by
    rcases le_or_gt 1 β with h | h
    · calc 1 / (A0 : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hA0R
        _ ≤ β ^ (r - 1) := one_le_pow₀ h
    · calc 1 / (A0 : ℝ) ≤ (b : ℝ) / a := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have : (1 : ℝ) ≤ b := by exact_mod_cast hb0
            have : (a : ℝ) ≤ A0 := by exact_mod_cast haA
            nlinarith
        _ = β ^ r := hβr.symm
        _ ≤ β ^ (r - 1) := pow_le_pow_of_le_one hβ0 h.le (by omega)

  have hdiff : |((u : ℝ) / v) ^ r - β ^ r| = D / (a * w) := by
    rw [hβr, hD, div_pow, hw]
    have hv : (v : ℝ) ≠ 0 := by positivity
    have ha : (a : ℝ) ≠ 0 := by positivity
    rw [div_sub_div _ _ (pow_ne_zero _ hv) ha, abs_div, abs_of_pos (show (0:ℝ) < v ^ r * a by positivity)]
    congr 1
    · push_cast; congr 1; ring
    · ring
  have hstep : w ^ (-ε) ≤ A0 * D / w := by
    rw [← hwκ]
    refine hlow.trans ?_
    have key := ridout_pow_sub_pow ((u : ℝ) / v) β (by positivity) hβ0 r hr
    rw [hdiff, abs_sub_comm] at key
    have hpos : 0 < β ^ (r - 1) := lt_of_lt_of_le (by positivity) hβr1
    rw [← le_div_iff₀ hpos] at key
    refine key.trans ?_
    rw [div_le_iff₀ hpos]
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have hD0 : 0 ≤ D := abs_nonneg _
    calc D / (a * w) ≤ D / w := by
          apply div_le_div_of_nonneg_left hD0 hw0; nlinarith
      _ = (A0 * D / w) * (1 / A0) := by field_simp
      _ ≤ A0 * D / w * β ^ (r - 1) := by gcongr

  have h1 : w ^ (1 - ε) ≤ A0 * D := by
    rw [sub_eq_add_neg, Real.rpow_add hw0, Real.rpow_one]
    rw [le_div_iff₀ hw0] at hstep
    linarith
  have hbadD : D < M ^ (1 - δ) := hbad
  have hMA : M ≤ A0 * w := by
    rw [hMw]; gcongr
  have h1ε : 0 ≤ 1 - ε := by linarith
  have h2 : M ^ (1 - ε) ≤ A0 * w ^ (1 - ε) := by
    calc M ^ (1 - ε) ≤ ((A0 : ℝ) * w) ^ (1 - ε) :=
          Real.rpow_le_rpow (by linarith) hMA h1ε
      _ = (A0 : ℝ) ^ (1 - ε) * w ^ (1 - ε) := Real.mul_rpow (by positivity) hw0.le
      _ ≤ (A0 : ℝ) ^ (1 : ℝ) * w ^ (1 - ε) := by
          gcongr
          · linarith
      _ = A0 * w ^ (1 - ε) := by rw [Real.rpow_one]
  have hM0 : 0 < M := by linarith
  have h3 : M ^ (δ - ε) * M ^ (1 - δ) < (A0 : ℝ) ^ 2 * M ^ (1 - δ) := by
    rw [← Real.rpow_add hM0, show δ - ε + (1 - δ) = 1 - ε by ring]
    calc M ^ (1 - ε) ≤ A0 * w ^ (1 - ε) := h2
      _ ≤ A0 * (A0 * D) := by gcongr
      _ < A0 * (A0 * M ^ (1 - δ)) := by gcongr
      _ = (A0 : ℝ) ^ 2 * M ^ (1 - δ) := by ring
  have h4 : M ^ (δ - ε) < (A0 : ℝ) ^ 2 :=
    lt_of_mul_lt_mul_right h3 (Real.rpow_nonneg hM0.le _)
  have hMT : T < M := by
    have : (⌈T⌉₊ : ℝ) < M := by
      rw [hM]; exact_mod_cast (show ⌈T⌉₊ < b * v ^ r by omega)
    exact lt_of_le_of_lt (Nat.le_ceil T) this
  have hδε : 0 < δ - ε := by linarith
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  have h5 : T ^ (δ - ε) < M ^ (δ - ε) := Real.rpow_lt_rpow hT0 hMT hδε
  rw [hT, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hδε.ne', Real.rpow_one] at h5
  linarith

end OMA494

namespace OMA494

theorem ridout_smooth (P : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℕ, ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P →
      Nat.Coprime x y → B < max x y →
      ((max x y : ℕ) : ℝ) ^ (1 - δ) ≤ |(x : ℝ) - y| := by
  rcases lt_or_ge δ 1 with hδ1 | hδ1
  · obtain ⟨B, hB1, hB⟩ := ridout_core P δ hδ hδ1
    refine ⟨B, fun x y hx hy hxy hBm => ?_⟩
    rcases le_total x y with h | h
    · rw [max_eq_right h] at hBm ⊢
      exact hB x y hx hy hxy h hBm
    · rw [max_eq_left h] at hBm ⊢
      rw [abs_sub_comm]
      exact hB y x hy hx hxy.symm h hBm
  · refine ⟨1, fun x y hx hy hxy hBm => ?_⟩
    have hne : x ≠ y := by
      rintro rfl
      rw [Nat.coprime_self] at hxy
      subst hxy
      simp at hBm
    have hx0 := Nat.ne_zero_of_mem_smoothNumbers hx
    have hy0 := Nat.ne_zero_of_mem_smoothNumbers hy
    have hm1 : (1 : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ max x y)
    calc ((max x y : ℕ) : ℝ) ^ (1 - δ) ≤ ((max x y : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ = 1 := Real.rpow_zero _
      _ ≤ |(x : ℝ) - y| := by
          rcases lt_or_gt_of_ne hne with h | h
          · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
          · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
            rw [abs_of_nonneg (by linarith)]
            linarith

end OMA494
end

-- SmoothGap
section
namespace OMA494

theorem smooth_gap (P : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X0 : ℕ, ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P → X0 < y →
      |(x : ℝ) - y| ≤ (y : ℝ) ^ (1 - δ) → x = y := by
  set e : ℝ := min δ 1 with he_def
  have he0 : 0 < e := lt_min hδ one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heδ : e ≤ δ := min_le_left _ _
  obtain ⟨B, hB⟩ := ridout_smooth P (e / 2) (by positivity)
  refine ⟨max 1 ⌈((B : ℝ) + 1) ^ (1 / e)⌉₊, ?_⟩
  intro x y hx hy hy0 hxy
  by_contra hne
  have hy1 : 1 < y := lt_of_le_of_lt (le_max_left _ _) hy0
  have hyR : (1 : ℝ) < y := by exact_mod_cast hy1
  have hy0R : (0 : ℝ) < y := by linarith
  have hxy' : |(x : ℝ) - y| ≤ (y : ℝ) ^ (1 - e) :=
    hxy.trans (Real.rpow_le_rpow_of_exponent_le hyR.le (by linarith))
  have hgpos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_right _ (by omega)
  set g := Nat.gcd x y with hg
  have hxg : x = g * (x / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)).symm
  have hyg : y = g * (y / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)).symm
  have hcop : Nat.Coprime (x / g) (y / g) := Nat.coprime_div_gcd_div_gcd hgpos
  set a := x / g
  set b := y / g
  have ha : a ∈ Nat.smoothNumbers P := Nat.mem_smoothNumbers_of_dvd hx (Dvd.intro_left _ hxg.symm)
  have hb : b ∈ Nat.smoothNumbers P := Nat.mem_smoothNumbers_of_dvd hy (Dvd.intro_left _ hyg.symm)
  have hab : a ≠ b := by
    intro h; apply hne; rw [hxg, hyg, h]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hgpos
  have hxR : (x : ℝ) = g * a := by rw [hxg]; push_cast; ring
  have hyR' : (y : ℝ) = g * b := by rw [hyg]; push_cast; ring
  have habs : |(x : ℝ) - y| = g * |(a : ℝ) - b| := by
    rw [hxR, hyR', ← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ g)]
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hpow_pos : (0 : ℝ) < (y : ℝ) ^ (1 - e) := Real.rpow_pos_of_pos hy0R _
  rcases le_or_gt (max a b) B with hM | hM
  ·
    have hbB : (b : ℝ) ≤ B := by exact_mod_cast (le_max_right a b).trans hM
    have hg_le : (g : ℝ) ≤ (y : ℝ) ^ (1 - e) := by
      calc (g : ℝ) = g * 1 := by ring
        _ ≤ g * |(a : ℝ) - b| := by gcongr
        _ = |(x : ℝ) - y| := habs.symm
        _ ≤ _ := hxy'
    have hyc : (⌈((B : ℝ) + 1) ^ (1 / e)⌉₊ : ℝ) < y := by
      exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hy0
    have hye : ((B : ℝ) + 1) < (y : ℝ) ^ e := by
      have h2 : ((B : ℝ) + 1) ^ (1 / e) < y := lt_of_le_of_lt (Nat.le_ceil _) hyc
      have h3 := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) h2 he0
      rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ he0.ne', Real.rpow_one]
        at h3
    have hsplit : (y : ℝ) = (y : ℝ) ^ (1 - e) * (y : ℝ) ^ e := by
      rw [← Real.rpow_add hy0R]; simp
    have : (y : ℝ) ≤ (y : ℝ) ^ (1 - e) * B := by
      calc (y : ℝ) = g * b := hyR'
        _ ≤ (y : ℝ) ^ (1 - e) * B := by
          apply mul_le_mul hg_le hbB (by positivity) hpow_pos.le
    have : (y : ℝ) ^ (1 - e) * B < (y : ℝ) ^ (1 - e) * (y : ℝ) ^ e := by
      apply mul_lt_mul_of_pos_left _ hpow_pos; linarith
    linarith
  ·
    have hR := hB a b ha hb hcop hM
    have hlt : (y : ℝ) ^ (1 - e) < (y : ℝ) ^ (1 - e / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hyR (by linarith)
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hbM : (b : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_right a b
    have hge : (y : ℝ) ^ (1 - e / 2) ≤ |(x : ℝ) - y| := by
      rw [habs, hyR', Real.mul_rpow (by linarith) hb0]
      calc (g : ℝ) ^ (1 - e / 2) * (b : ℝ) ^ (1 - e / 2)
          ≤ (g : ℝ) * ((max a b : ℕ) : ℝ) ^ (1 - e / 2) := by
            apply mul_le_mul
            · calc (g : ℝ) ^ (1 - e / 2) ≤ (g : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le hgR (by linarith)
                _ = g := Real.rpow_one _
            · exact Real.rpow_le_rpow hb0 hbM (by linarith)
            · exact Real.rpow_nonneg hb0 _
            · linarith
        _ ≤ g * |(a : ℝ) - b| := by gcongr
    linarith

end OMA494
end

-- Main
section
open Filter

namespace OMA494

private lemma smooth_of_dvd_factorial_mul_pow {s j m : ℕ}
    (h : m ∣ (s - 1).factorial * s ^ (j - 1)) (hs : 1 ≤ s) :
    m ∈ Nat.smoothNumbers (s + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpm
  have hpd := dvd_trans hpm h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.Prime.dvd_factorial hp).1 h1
    omega
  · have := Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow h1)
    omega

private lemma smooth_pow_of_le {s i e : ℕ} (hi0 : 0 < i) (his : i ≤ s) :
    i ^ e ∈ Nat.smoothNumbers (s + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpm
  have := Nat.le_of_dvd hi0 (hp.dvd_of_dvd_pow hpm)
  omega

theorem gfs_core : GFSCore := by
  intro s hs
  have hs3 : 3 ≤ s := hs
  obtain ⟨δ, hδ0, -, J0, hTT⟩ := two_term_approx s hs3
  obtain ⟨N1, hBJ⟩ := bounded_j s (by omega) J0
  obtain ⟨N2, hEx⟩ := exact_case s hs3
  obtain ⟨X0, hSG⟩ := smooth_gap (s + 1) δ hδ0
  rw [Filter.eventually_atTop]
  refine ⟨N1 + N2 + 2 * X0 + s + 1, fun n hn j hj hf => ?_⟩
  by_cases hjJ : j < J0
  · exact hBJ n j (by omega) hjJ hf
  replace hjJ := not_lt.1 hjJ
  obtain ⟨i, hi, happrox, hn2⟩ := hTT n j (by omega) hjJ hf
  have hi' := Finset.mem_Icc.1 hi
  have hdvd := gfs_dvd s n j (by omega) (by omega) hf
  have hnsm : n ∈ Nat.smoothNumbers (s + 1) :=
    smooth_of_dvd_factorial_mul_pow hdvd (by omega)
  have hx : n * i ^ (j - 1) ∈ Nat.smoothNumbers (s + 1) :=
    Nat.mul_mem_smoothNumbers hnsm (smooth_pow_of_le (by omega) (by omega))
  have hsi : s - i ∈ Nat.smoothNumbers (s + 1) := by
    simpa using smooth_pow_of_le (s := s) (i := s - i) (e := 1) (by omega) (by omega)
  have hy : (s - i) * (i + 1) ^ (j - 1) ∈ Nat.smoothNumbers (s + 1) :=
    Nat.mul_mem_smoothNumbers hsi (smooth_pow_of_le (by omega) (by omega))
  have hy0 : X0 < (s - i) * (i + 1) ^ (j - 1) := by omega
  have heq := hSG _ _ hx hy hy0 happrox
  exact hEx n j i (by omega) hj hi heq hf

theorem unique_of_gfsPoly_ne_zero (s n : ℕ) (hcore : ∀ j, 1 ≤ j → gfsPoly s n j ≠ 0) :
    Erdos494Unique s n := by
  intro A B hA hB hAB
  have hall : ∀ j, 1 ≤ j → psum A j = psum B j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hlow : ∀ l, 1 ≤ l → l < j → psum A l = psum B l := fun l hl hlj => ih l hlj hl
      have key := ksum_power_sum A B n s j hA hB hj hlow
      have hk : ksumPsum A s j = ksumPsum B s j := by simp [ksumPsum, hAB]
      rw [hk, sub_self] at key
      have hne : (gfsPoly s n j : ℂ) ≠ 0 := by exact_mod_cast hcore j hj
      exact sub_eq_zero.1 ((mul_eq_zero.1 key.symm).resolve_left hne)
  exact power_sums_determine A B n hA hB fun j hj _ => hall j hj

theorem gordon_fraenkel_straus : GFSStatement := by
  intro k hk
  filter_upwards [gfs_core k hk] with n hn
  exact unique_of_gfsPoly_ne_zero k n hn

theorem erdos_494 : Erdos494Full :=
  ⟨kruyt_counterexample, tao_counterexample, gordon_fraenkel_straus⟩

end OMA494
end

/-! ### Bridge to the statement in FormalConjectures.ErdosProblems.494 -/

theorem OMA.solution : type_of% @Erdos494.erdos_494.variants.gordon_fraenkel_straus :=
  OMA494.gordon_fraenkel_straus
