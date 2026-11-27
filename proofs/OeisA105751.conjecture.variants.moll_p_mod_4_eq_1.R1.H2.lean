import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib

/-!
The dyadic nonvanishing proof is taken from Sheikh Azizul Hakim's
second reduction in open-math-agents PR #2836. This file instantiates
the nonvanishing step of the first reduction.
-/

namespace OMA.MollNonvanishing

open Finset Filter Topology

lemma prod_complex_eq_gaussianInt (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ) * Complex.I) =
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re : ℂ) +
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) * Complex.I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ (n := n + 1), Finset.prod_range_succ (n := n + 1), ih]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) *
      ((n : ℂ) + 1) * hI2

lemma a_eq_gaussianInt_im (n : ℕ) :
    OeisA105751.a n = (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im := by
  unfold OeisA105751.a
  dsimp only
  rw [prod_complex_eq_gaussianInt]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

lemma gaussianInt_prod_congr_mod (W₁ W₂ : ℕ → GaussianInt) (M : ℤ) (a L : ℕ)
    (h : ∀ j, M ∣ (W₁ j).re - (W₂ j).re ∧ M ∣ (W₁ j).im - (W₂ j).im) :
    M ∣ (∏ j ∈ Finset.Ico a (a + L), W₁ j).re - (∏ j ∈ Finset.Ico a (a + L), W₂ j).re ∧
    M ∣ (∏ j ∈ Finset.Ico a (a + L), W₁ j).im - (∏ j ∈ Finset.Ico a (a + L), W₂ j).im := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hsp : Finset.Ico a (a + (L + 1)) = insert (a + L) (Finset.Ico a (a + L)) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : a + L ∉ Finset.Ico a (a + L) := by simp
    rw [hsp, Finset.prod_insert hnot, Finset.prod_insert hnot]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    rcases h (a + L) with ⟨hr, hi⟩
    rcases ih with ⟨ihr, ihi⟩
    set z₁ := ∏ j ∈ Finset.Ico a (a + L), W₁ j
    set z₂ := ∏ j ∈ Finset.Ico a (a + L), W₂ j
    constructor
    · have hid :
          ((W₁ (a + L)).re * z₁.re + -1 * (W₁ (a + L)).im * z₁.im) -
            ((W₂ (a + L)).re * z₂.re + -1 * (W₂ (a + L)).im * z₂.im) =
          ((W₁ (a + L)).re - (W₂ (a + L)).re) * z₁.re + (W₂ (a + L)).re * (z₁.re - z₂.re) -
          (((W₁ (a + L)).im - (W₂ (a + L)).im) * z₁.im + (W₂ (a + L)).im * (z₁.im - z₂.im)) := by ring
      rw [hid]
      exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hr _) (dvd_mul_of_dvd_right ihr _))
        (dvd_add (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_right ihi _))
    · have hid :
          ((W₁ (a + L)).re * z₁.im + (W₁ (a + L)).im * z₁.re) -
            ((W₂ (a + L)).re * z₂.im + (W₂ (a + L)).im * z₂.re) =
          ((W₁ (a + L)).re - (W₂ (a + L)).re) * z₁.im + (W₂ (a + L)).re * (z₁.im - z₂.im) +
          (((W₁ (a + L)).im - (W₂ (a + L)).im) * z₁.re + (W₂ (a + L)).im * (z₁.re - z₂.re)) := by ring
      rw [hid]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left hr _) (dvd_mul_of_dvd_right ihi _))
        (dvd_add (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_right ihr _))

lemma dyadic_block_pow2 (W : ℕ → GaussianInt)
    (hre : ∀ k, Odd (W k).re)
    (him : ∀ k, (W k).im % 8 = 4)
    (hper : ∀ m k, ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).re - (W k).re ∧
                   ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).im - (W k).im) :
    ∀ m a : ℕ,
      Odd (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).re ∧
      ((2 : ℤ) ^ (m + 2)) ∣ (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).im ∧
      ¬ (((2 : ℤ) ^ (m + 3)) ∣ (∏ j ∈ Finset.Ico a (a + 2 ^ m), W j).im) := by
  intro m
  induction m with
  | zero =>
    intro a
    have hIco : Finset.Ico a (a + 2 ^ 0) = {a} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton, pow_zero]; omega
    rw [hIco, Finset.prod_singleton]
    have h4 := him a
    refine ⟨hre a, ?_, ?_⟩
    · refine ⟨(W a).im / 4, ?_⟩; omega
    · rintro ⟨q, hq⟩; omega
  | succ m ih =>
    intro a
    have hsp : Finset.Ico a (a + 2 ^ (m + 1)) =
        Finset.Ico a (a + 2 ^ m) ∪ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m) := by
      have : a + 2 ^ (m + 1) = a + 2 ^ m + 2 ^ m := by ring
      rw [this]
      exact (Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a (2 ^ m))
        (Nat.le_add_right (a + 2 ^ m) (2 ^ m))).symm
    have hdisj : Disjoint (Finset.Ico a (a + 2 ^ m)) (Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m)) :=
      Finset.Ico_disjoint_Ico_consecutive a (a + 2 ^ m) (a + 2 ^ m + 2 ^ m)
    rw [hsp, Finset.prod_union hdisj]
    set z₁ := ∏ j ∈ Finset.Ico a (a + 2 ^ m), W j
    set z₂ := ∏ j ∈ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + 2 ^ m), W j
    obtain ⟨hre1, hd1, hnd1⟩ := ih a
    obtain ⟨hre2, hd2, _⟩ := ih (a + 2 ^ m)
    have hshift : z₂ = ∏ j ∈ Finset.Ico a (a + 2 ^ m), W (j + 2 ^ m) := by
      refine Finset.prod_bij (fun x _ => x - 2 ^ m) ?_ ?_ ?_ ?_
      · intro x hx; rw [Finset.mem_Ico] at hx ⊢; omega
      · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_Ico] at hx₁ hx₂; omega
      · intro j hj; rw [Finset.mem_Ico] at hj
        exact ⟨j + 2 ^ m, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro x hx; rw [Finset.mem_Ico] at hx; congr 1; omega
    have hcong := gaussianInt_prod_congr_mod (fun j => W (j + 2 ^ m)) W ((2 : ℤ) ^ (m + 4)) a (2 ^ m)
      (fun j => hper m j)
    rw [← hshift] at hcong
    rcases hcong with ⟨hcr, hci⟩
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    refine ⟨?_, ?_, ?_⟩
    · have hev1 : Even z₁.im := even_iff_two_dvd.mpr
        ((dvd_pow_self (2 : ℤ) (by omega : m + 2 ≠ 0)).trans hd1)
      have hmul_odd : Odd (z₁.re * z₂.re) := hre1.mul hre2
      have hmul_ev : Even (-1 * z₁.im * z₂.im) := (hev1.mul_left (-1)).mul_right _
      exact hmul_odd.add_even hmul_ev
    · have h2m3_1 : ((2 : ℤ) ^ (m + 3)) ∣ 2 * z₁.re * z₁.im := by
        rcases hd1 with ⟨q, hq⟩
        refine ⟨z₁.re * q, ?_⟩
        rw [hq, pow_succ']; ring
      have hdiff : ((2 : ℤ) ^ (m + 4)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im := by
        have hid : (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im =
            z₁.re * (z₂.im - z₁.im) + z₁.im * (z₂.re - z₁.re) := by ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_right hci _) (dvd_mul_of_dvd_right hcr _)
      have hdiff3 : ((2 : ℤ) ^ (m + 3)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im :=
        (pow_dvd_pow (2 : ℤ) (by omega : m + 3 ≤ m + 4)).trans hdiff
      have := dvd_add hdiff3 h2m3_1
      simpa using this
    · intro hd4
      have hdiff : ((2 : ℤ) ^ (m + 4)) ∣
          (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im := by
        have hid : (z₁.re * z₂.im + z₁.im * z₂.re) - 2 * z₁.re * z₁.im =
            z₁.re * (z₂.im - z₁.im) + z₁.im * (z₂.re - z₁.re) := by ring
        rw [hid]
        exact dvd_add (dvd_mul_of_dvd_right hci _) (dvd_mul_of_dvd_right hcr _)
      have h2r : ((2 : ℤ) ^ (m + 4)) ∣ 2 * z₁.re * z₁.im := by
        have := dvd_sub hd4 hdiff
        simpa using this
      have hri : ((2 : ℤ) ^ (m + 3)) ∣ z₁.re * z₁.im := by
        rcases h2r with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [pow_succ'] at hq
        linarith
      rcases hd1 with ⟨c, hc⟩
      have hc_odd : Odd c := by
        rw [Int.odd_iff]
        by_contra hev
        have h2c : (2 : ℤ) ∣ c := ⟨c / 2, by omega⟩
        rcases h2c with ⟨c', rfl⟩
        apply hnd1
        refine ⟨c', ?_⟩
        rw [hc, pow_succ']; ring
      have h2_dvd : (2 : ℤ) ∣ z₁.re * c := by
        rcases hri with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have h2m3 : (2 : ℤ) ^ (m + 3) = (2 : ℤ) ^ (m + 2) * 2 := pow_succ (2 : ℤ) (m + 2)
        rw [hc, h2m3] at hq
        have hpos : (2 : ℤ) ^ (m + 2) ≠ 0 := by positivity
        have : (2 : ℤ) ^ (m + 2) * (z₁.re * c) = (2 : ℤ) ^ (m + 2) * (2 * q) := by linarith
        exact mul_left_cancel₀ hpos this
      exact (Int.not_even_iff_odd.mpr (hre1.mul hc_odd)) (even_iff_two_dvd.mpr h2_dvd)

lemma dyadic_block_prod (W : ℕ → GaussianInt)
    (hre : ∀ k, Odd (W k).re)
    (him : ∀ k, (W k).im % 8 = 4)
    (hper : ∀ m k, ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).re - (W k).re ∧
                   ((2 : ℤ) ^ (m + 4)) ∣ (W (k + 2 ^ m)).im - (W k).im) :
    ∀ k a : ℕ, 1 ≤ k →
      Odd (∏ j ∈ Finset.Ico a (a + k), W j).re ∧
      ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ (∏ j ∈ Finset.Ico a (a + k), W j).im ∧
      ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ (∏ j ∈ Finset.Ico a (a + k), W j).im) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a hk
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set m := padicValNat 2 k
    have h2m_dvd : 2 ^ m ∣ k := pow_padicValNat_dvd
    have h2m_le : 2 ^ m ≤ k := Nat.le_of_dvd (by omega) h2m_dvd
    by_cases hkeq : k = 2 ^ m
    · rw [hkeq]
      exact dyadic_block_pow2 W hre him hper m a
    · set k' := k - 2 ^ m
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < k := by have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide); omega
      have h2m1_dvd_k' : 2 ^ (m + 1) ∣ k' := by
        obtain ⟨q, hq⟩ := h2m_dvd
        have hq_odd : Odd q := by
          rw [Nat.odd_iff]
          by_contra hev
          have h2q : 2 ∣ q := ⟨q / 2, by omega⟩
          rcases h2q with ⟨q', rfl⟩
          have hd : 2 ^ (m + 1) ∣ k := ⟨q', by rw [hq, pow_succ]; ring⟩
          have hle := (padicValNat_dvd_iff_le (by omega : k ≠ 0)).mp hd
          change m + 1 ≤ m at hle
          omega
        obtain ⟨t, ht⟩ := hq_odd
        refine ⟨t, ?_⟩
        have hk'_eq : k' = 2 ^ m * (q - 1) := by
          calc k' = k - 2 ^ m := rfl
            _ = 2 ^ m * q - 2 ^ m * 1 := by rw [hq, mul_one]
            _ = 2 ^ m * (q - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
        rw [hk'_eq, pow_succ]
        have : q - 1 = 2 * t := by omega
        rw [this]; ring
      have hm'_ge : m + 1 ≤ padicValNat 2 k' :=
        (padicValNat_dvd_iff_le (by omega : k' ≠ 0)).mp h2m1_dvd_k'
      have hsp : Finset.Ico a (a + k) =
          Finset.Ico a (a + 2 ^ m) ∪ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k') := by
        have : a + k = a + 2 ^ m + k' := by omega
        rw [this]
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a (2 ^ m))
          (Nat.le_add_right (a + 2 ^ m) k')).symm
      have hdisj : Disjoint (Finset.Ico a (a + 2 ^ m)) (Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k')) :=
        Finset.Ico_disjoint_Ico_consecutive a (a + 2 ^ m) (a + 2 ^ m + k')
      rw [hsp, Finset.prod_union hdisj]
      set z₁ := ∏ j ∈ Finset.Ico a (a + 2 ^ m), W j
      set z₂ := ∏ j ∈ Finset.Ico (a + 2 ^ m) (a + 2 ^ m + k'), W j
      obtain ⟨hre1, hd1, hnd1⟩ := dyadic_block_pow2 W hre him hper m a
      obtain ⟨hre2, hd2, _⟩ := ih k' hk'_lt (a + 2 ^ m) hk'_pos
      have hd2' : ((2 : ℤ) ^ (m + 3)) ∣ z₂.im :=
        (pow_dvd_pow (2 : ℤ) (by omega : m + 3 ≤ padicValNat 2 k' + 2)).trans hd2
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine ⟨?_, ?_, ?_⟩
      · have hev1 : Even z₁.im := even_iff_two_dvd.mpr
          ((dvd_pow_self (2 : ℤ) (by omega : m + 2 ≠ 0)).trans hd1)
        exact (hre1.mul hre2).add_even ((hev1.mul_left (-1)).mul_right _)
      · exact dvd_add (dvd_mul_of_dvd_right ((pow_dvd_pow (2 : ℤ) (by omega : m + 2 ≤ m + 3)).trans hd2') _)
          (dvd_mul_of_dvd_left hd1 _)
      · intro h3
        have h13 : ((2 : ℤ) ^ (m + 3)) ∣ z₁.im * z₂.re := by
          have := dvd_sub h3 (dvd_mul_of_dvd_right hd2' z₁.re)
          simpa using this
        rcases hd1 with ⟨c, hc⟩
        have hc_odd : Odd c := by
          rw [Int.odd_iff]
          by_contra hev
          have h2c : (2 : ℤ) ∣ c := ⟨c / 2, by omega⟩
          rcases h2c with ⟨c', rfl⟩
          exact hnd1 ⟨c', by rw [hc, pow_succ]; ring⟩
        have h2_dvd : (2 : ℤ) ∣ c * z₂.re := by
          rcases h13 with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have h2m3 : (2 : ℤ) ^ (m + 3) = (2 : ℤ) ^ (m + 2) * 2 := pow_succ (2 : ℤ) (m + 2)
          rw [hc, h2m3] at hq
          have hpos : (2 : ℤ) ^ (m + 2) ≠ 0 := by positivity
          have : (2 : ℤ) ^ (m + 2) * (c * z₂.re) = (2 : ℤ) ^ (m + 2) * (2 * q) := by linarith
          exact mul_left_cancel₀ hpos this
        exact (Int.not_even_iff_odd.mpr (hc_odd.mul hre2)) (even_iff_two_dvd.mpr h2_dvd)

lemma prod_Ico_eight (f : ℕ → GaussianInt) (a : ℕ) :
    ∏ j ∈ Finset.Ico a (a + 8), f j =
      f a * f (a + 1) * f (a + 2) * f (a + 3) * f (a + 4) * f (a + 5) * f (a + 6) * f (a + 7) := by
  have h1 : a + 8 = (a + 7) + 1 := by omega
  have h2 : a + 7 = (a + 6) + 1 := by omega
  have h3 : a + 6 = (a + 5) + 1 := by omega
  have h4 : a + 5 = (a + 4) + 1 := by omega
  have h5 : a + 4 = (a + 3) + 1 := by omega
  have h6 : a + 3 = (a + 2) + 1 := by omega
  have h7 : a + 2 = (a + 1) + 1 := by omega
  rw [h1, Finset.prod_Ico_succ_top (by omega), h2, Finset.prod_Ico_succ_top (by omega),
    h3, Finset.prod_Ico_succ_top (by omega), h4, Finset.prod_Ico_succ_top (by omega),
    h5, Finset.prod_Ico_succ_top (by omega), h6, Finset.prod_Ico_succ_top (by omega),
    h7, Finset.prod_Ico_succ_top (by omega), Finset.prod_Ico_succ_top (by omega),
    Finset.Ico_self, Finset.prod_empty, one_mul]

lemma block8_zero_identity (k : ℕ) :
    ∏ j ∈ Finset.Ico (8 * k + 1) (8 * k + 9), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨4, 0⟩ : GaussianInt) *
      ⟨-13975 + (-139680) * (k : ℤ) + (-134528) * (k : ℤ) ^ 2 + 2967552 * (k : ℤ) ^ 3 +
         14672896 * (k : ℤ) ^ 4 + 30965760 * (k : ℤ) ^ 5 + 33947648 * (k : ℤ) ^ 6 +
         18874368 * (k : ℤ) ^ 7 + 4194304 * (k : ℤ) ^ 8,
       -11700 + (-299440) * (k : ℤ) + (-2515968) * (k : ℤ) ^ 2 + (-10103296) * (k : ℤ) ^ 3 +
         (-21934080) * (k : ℤ) ^ 4 + (-26378240) * (k : ℤ) ^ 5 + (-16515072) * (k : ℤ) ^ 6 +
         (-4194304) * (k : ℤ) ^ 7⟩ := by
  rw [show 8 * k + 9 = (8 * k + 1) + 8 by omega, prod_Ico_eight]
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> push_cast <;> ring

lemma block8_three_identity (k : ℕ) :
    ∏ j ∈ Finset.Ico (8 * k + 4) (8 * k + 12), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨4, 0⟩ : GaussianInt) *
      ⟨706745 + 9081120 * (k : ℤ) + 45249664 * (k : ℤ) ^ 2 + 119132160 * (k : ℤ) ^ 3 +
         184984576 * (k : ℤ) ^ 4 + 175472640 * (k : ℤ) ^ 5 + 100007936 * (k : ℤ) ^ 6 +
         31457280 * (k : ℤ) ^ 7 + 4194304 * (k : ℤ) ^ 8,
       -1690260 + (-14500144) * (k : ℤ) + (-51851520) * (k : ℤ) ^ 2 + (-100420096) * (k : ℤ) ^ 3 +
         (-113971200) * (k : ℤ) ^ 4 + (-75923456) * (k : ℤ) ^ 5 + (-27525120) * (k : ℤ) ^ 6 +
         (-4194304) * (k : ℤ) ^ 7⟩ := by
  rw [show 8 * k + 12 = (8 * k + 4) + 8 by omega, prod_Ico_eight]
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> push_cast <;> ring

lemma gaussianInt_8k_structure (k : ℕ) :
    ∃ A B : ℤ,
      ∏ j ∈ Finset.range (8 * k + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        ⟨(2 : ℤ) ^ (2 * k) * A, (2 : ℤ) ^ (2 * k) * B⟩ ∧
      Odd A ∧
      (k = 0 → B = 0) ∧
      (1 ≤ k → ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ B ∧
               ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ B)) := by
  let W0 : ℕ → GaussianInt := fun j =>
    ⟨-13975 + (-139680) * (j : ℤ) + (-134528) * (j : ℤ) ^ 2 + 2967552 * (j : ℤ) ^ 3 +
       14672896 * (j : ℤ) ^ 4 + 30965760 * (j : ℤ) ^ 5 + 33947648 * (j : ℤ) ^ 6 +
       18874368 * (j : ℤ) ^ 7 + 4194304 * (j : ℤ) ^ 8,
     -11700 + (-299440) * (j : ℤ) + (-2515968) * (j : ℤ) ^ 2 + (-10103296) * (j : ℤ) ^ 3 +
       (-21934080) * (j : ℤ) ^ 4 + (-26378240) * (j : ℤ) ^ 5 + (-16515072) * (j : ℤ) ^ 6 +
       (-4194304) * (j : ℤ) ^ 7⟩
  have hprod : ∏ j ∈ Finset.range (8 * k + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨(2 : ℤ) ^ (2 * k), 0⟩ : GaussianInt) * ∏ j ∈ Finset.Ico 0 k, W0 j := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hsp : Finset.range (8 * (k + 1) + 1) =
          Finset.range (8 * k + 1) ∪ Finset.Ico (8 * k + 1) (8 * k + 9) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (8 * k + 1)) (Finset.Ico (8 * k + 1) (8 * k + 9)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      have hIco_succ : Finset.Ico 0 (k + 1) = insert k (Finset.Ico 0 k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsp, Finset.prod_union hdisj, ih, block8_zero_identity k,
        hIco_succ, Finset.prod_insert (by simp)]
      have hpow : (⟨(2 : ℤ) ^ (2 * (k + 1)), 0⟩ : GaussianInt) =
          (⟨(2 : ℤ) ^ (2 * k), 0⟩ : GaussianInt) * ⟨4, 0⟩ := by
        ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
        · rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; ring
        · ring
      rw [hpow]; ring
  set Z := ∏ j ∈ Finset.Ico 0 k, W0 j
  have hre : ∀ j, Odd (W0 j).re := fun j => ⟨-6988 - 69840 * j - 67264 * j ^ 2 +
    1483776 * j ^ 3 + 7336448 * j ^ 4 + 15482880 * j ^ 5 + 16973824 * j ^ 6 +
    9437184 * j ^ 7 + 2097152 * j ^ 8, by simp only [W0]; ring⟩
  have him : ∀ j, (W0 j).im % 8 = 4 := fun j => by
    have : (W0 j).im = 4 + 8 * (-1463 - 37430 * j - 314496 * j ^ 2 - 1262912 * j ^ 3 -
        2741760 * j ^ 4 - 3297280 * j ^ 5 - 2064384 * j ^ 6 - 524288 * j ^ 7) := by
      simp only [W0]; ring
    omega
  have hper : ∀ m j, ((2 : ℤ) ^ (m + 4)) ∣ (W0 (j + 2 ^ m)).re - (W0 j).re ∧
                     ((2 : ℤ) ^ (m + 4)) ∣ (W0 (j + 2 ^ m)).im - (W0 j).im := by
    intro m j
    have h16 : (2 : ℤ) ^ (m + 4) = 16 * ((2 : ℤ) ^ m) := by
      rw [pow_add]; norm_num; ring
    rw [h16]
    set d : ℤ := (2 : ℤ) ^ m
    have hcast : ((j + 2 ^ m : ℕ) : ℤ) = (j : ℤ) + d := by push_cast; rfl
    simp only [W0, hcast]
    constructor
    · refine ⟨-8730 + (-8408) * (2 * j + d) + 185472 * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        917056 * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        1935360 * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        2121728 * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        1179648 * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6) +
        262144 * (8 * j ^ 7 + 28 * j ^ 6 * d + 56 * j ^ 5 * d ^ 2 + 70 * j ^ 4 * d ^ 3 + 56 * j ^ 3 * d ^ 4 + 28 * j ^ 2 * d ^ 5 + 8 * j * d ^ 6 + d ^ 7), by ring⟩
    · refine ⟨-18715 + (-157248) * (2 * j + d) + (-631456) * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        (-1370880) * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        (-1648640) * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        (-1032192) * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        (-262144) * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6), by ring⟩
  refine ⟨Z.re, Z.im, ?_, ?_, ?_, ?_⟩
  · rw [hprod]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Z]
    · simpa [Z] using (dyadic_block_prod W0 hre him hper k 0 (by omega)).1
  · rintro rfl; simp [Z]
  · intro hk1
    simpa [Z] using (dyadic_block_prod W0 hre him hper k 0 hk1).2

lemma gaussianInt_8k3_structure (k : ℕ) :
    ∃ A B : ℤ,
      ∏ j ∈ Finset.range (8 * k + 4), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        ⟨(2 : ℤ) ^ (2 * k + 1) * (-5 * A), (2 : ℤ) ^ (2 * k + 1) * (-5 * B)⟩ ∧
      Odd A ∧
      (k = 0 → B = 0) ∧
      (1 ≤ k → ((2 : ℤ) ^ (padicValNat 2 k + 2)) ∣ B ∧
               ¬ (((2 : ℤ) ^ (padicValNat 2 k + 3)) ∣ B)) := by
  let W3 : ℕ → GaussianInt := fun j =>
    ⟨706745 + 9081120 * (j : ℤ) + 45249664 * (j : ℤ) ^ 2 + 119132160 * (j : ℤ) ^ 3 +
       184984576 * (j : ℤ) ^ 4 + 175472640 * (j : ℤ) ^ 5 + 100007936 * (j : ℤ) ^ 6 +
       31457280 * (j : ℤ) ^ 7 + 4194304 * (j : ℤ) ^ 8,
     -1690260 + (-14500144) * (j : ℤ) + (-51851520) * (j : ℤ) ^ 2 + (-100420096) * (j : ℤ) ^ 3 +
       (-113971200) * (j : ℤ) ^ 4 + (-75923456) * (j : ℤ) ^ 5 + (-27525120) * (j : ℤ) ^ 6 +
       (-4194304) * (j : ℤ) ^ 7⟩
  have hbase3 : ∏ j ∈ Finset.range 4, (⟨1, (j : ℤ)⟩ : GaussianInt) = ⟨-10, 0⟩ := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hprod : ∏ j ∈ Finset.range (8 * k + 4), (⟨1, (j : ℤ)⟩ : GaussianInt) =
      (⟨(2 : ℤ) ^ (2 * k + 1) * (-5), 0⟩ : GaussianInt) * ∏ j ∈ Finset.Ico 0 k, W3 j := by
    induction k with
    | zero =>
      simpa using hbase3
    | succ k ih =>
      have hsp : Finset.range (8 * (k + 1) + 4) =
          Finset.range (8 * k + 4) ∪ Finset.Ico (8 * k + 4) (8 * k + 12) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range (8 * k + 4)) (Finset.Ico (8 * k + 4) (8 * k + 12)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
      have hIco_succ : Finset.Ico 0 (k + 1) = insert k (Finset.Ico 0 k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsp, Finset.prod_union hdisj, ih, block8_three_identity k,
        hIco_succ, Finset.prod_insert (by simp)]
      have hpow : (⟨(2 : ℤ) ^ (2 * (k + 1) + 1) * (-5), 0⟩ : GaussianInt) =
          (⟨(2 : ℤ) ^ (2 * k + 1) * (-5), 0⟩ : GaussianInt) * ⟨4, 0⟩ := by
        ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
        · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]; ring
        · ring
      rw [hpow]; ring
  set Z := ∏ j ∈ Finset.Ico 0 k, W3 j
  have hre : ∀ j, Odd (W3 j).re := fun j => ⟨353372 + 4540560 * j + 22624832 * j ^ 2 +
    59566080 * j ^ 3 + 92492288 * j ^ 4 + 87736320 * j ^ 5 + 50003968 * j ^ 6 +
    15728640 * j ^ 7 + 2097152 * j ^ 8, by simp only [W3]; ring⟩
  have him : ∀ j, (W3 j).im % 8 = 4 := fun j => by
    have : (W3 j).im = 4 + 8 * (-211283 - 1812518 * j - 6481440 * j ^ 2 - 12552512 * j ^ 3 -
        14246400 * j ^ 4 - 9490432 * j ^ 5 - 3440640 * j ^ 6 - 524288 * j ^ 7) := by
      simp only [W3]; ring
    omega
  have hper : ∀ m j, ((2 : ℤ) ^ (m + 4)) ∣ (W3 (j + 2 ^ m)).re - (W3 j).re ∧
                     ((2 : ℤ) ^ (m + 4)) ∣ (W3 (j + 2 ^ m)).im - (W3 j).im := by
    intro m j
    have h16 : (2 : ℤ) ^ (m + 4) = 16 * ((2 : ℤ) ^ m) := by
      rw [pow_add]; norm_num; ring
    rw [h16]
    set d : ℤ := (2 : ℤ) ^ m
    have hcast : ((j + 2 ^ m : ℕ) : ℤ) = (j : ℤ) + d := by push_cast; rfl
    simp only [W3, hcast]
    constructor
    · refine ⟨567570 + 2828104 * (2 * j + d) + 7445760 * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        11561536 * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        10967040 * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        6250496 * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        1966080 * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6) +
        262144 * (8 * j ^ 7 + 28 * j ^ 6 * d + 56 * j ^ 5 * d ^ 2 + 70 * j ^ 4 * d ^ 3 + 56 * j ^ 3 * d ^ 4 + 28 * j ^ 2 * d ^ 5 + 8 * j * d ^ 6 + d ^ 7), by ring⟩
    · refine ⟨-906259 + (-3240720) * (2 * j + d) + (-6276256) * (3 * j ^ 2 + 3 * j * d + d ^ 2) +
        (-7123200) * (4 * j ^ 3 + 6 * j ^ 2 * d + 4 * j * d ^ 2 + d ^ 3) +
        (-4745216) * (5 * j ^ 4 + 10 * j ^ 3 * d + 10 * j ^ 2 * d ^ 2 + 5 * j * d ^ 3 + d ^ 4) +
        (-1720320) * (6 * j ^ 5 + 15 * j ^ 4 * d + 20 * j ^ 3 * d ^ 2 + 15 * j ^ 2 * d ^ 3 + 6 * j * d ^ 4 + d ^ 5) +
        (-262144) * (7 * j ^ 6 + 21 * j ^ 5 * d + 35 * j ^ 4 * d ^ 2 + 35 * j ^ 3 * d ^ 3 + 21 * j ^ 2 * d ^ 4 + 7 * j * d ^ 5 + d ^ 6), by ring⟩
  refine ⟨Z.re, Z.im, ?_, ?_, ?_, ?_⟩
  · rw [hprod]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  · by_cases hk0 : k = 0
    · subst hk0; simp [Z]
    · simpa [Z] using (dyadic_block_prod W3 hre him hper k 0 (by omega)).1
  · rintro rfl; simp [Z]
  · intro hk1
    simpa [Z] using (dyadic_block_prod W3 hre him hper k 0 hk1).2

lemma a_ne_zero_of_three_lt (n : ℕ) (hn : 3 < n) : OeisA105751.a n ≠ 0 := by
  rw [a_eq_gaussianInt_im]
  set k := n / 8
  have hmod : n % 8 < 8 := Nat.mod_lt n (by decide)
  have hdiv : n = 8 * k + n % 8 := (Nat.div_add_mod n 8).symm
  have hr : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
            n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hk1 : 1 ≤ k := by omega
    rw [show n = 8 * k by omega]
    obtain ⟨A, B, hZ, _, _, hB⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, false_or]
    rintro rfl
    exact (hB hk1).2 (dvd_zero _)
  · rw [show n = 8 * k + 1 by omega, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd ((8 * (k : ℤ) + 1) * A + B) := by
      have h1 : Odd (8 * (k : ℤ) + 1) := ⟨4 * k, by ring⟩
      exact (h1.mul hA).add_even hBeven
    have hfac : (2 : ℤ) ^ (2 * k) * A * ↑(8 * k + 1) + (2 : ℤ) ^ (2 * k) * B * 1 =
        (2 : ℤ) ^ (2 * k) * ((8 * (k : ℤ) + 1) * A + B) := by push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 2 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd ((16 * (k : ℤ) + 3) * A + (1 - (8 * k + 1) * (8 * k + 2)) * B) := by
      have h1 : Odd (16 * (k : ℤ) + 3) := ⟨8 * k + 1, by ring⟩
      exact (h1.mul hA).add_even (hBeven.mul_left _)
    have hfac :
        ((2 : ℤ) ^ (2 * k) * A * 1 + -1 * ((2 : ℤ) ^ (2 * k) * B) * ↑(8 * k + 1)) * ↑(8 * k + 2) +
        ((2 : ℤ) ^ (2 * k) * A * ↑(8 * k + 1) + (2 : ℤ) ^ (2 * k) * B * 1) * 1 =
        (2 : ℤ) ^ (2 * k) * ((16 * (k : ℤ) + 3) * A + (1 - (8 * k + 1) * (8 * k + 2)) * B) := by
      push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · have hk1 : 1 ≤ k := by omega
    rw [show n = 8 * k + 3 by omega]
    obtain ⟨A, B, hZ, _, _, hB⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    intro hzero
    have hB0 : B = 0 := by
      have hpow : (2 : ℤ) ^ (2 * k + 1) ≠ 0 := by positivity
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 hpow
      · linarith
    rw [hB0] at hB
    exact (hB hk1).2 (dvd_zero _)
  · rw [show n = 8 * k + 4 by omega]
    intro him0
    have hsp : Finset.range (8 * (k + 1) + 1) =
        Finset.range (8 * k + 5) ∪ Finset.Ico (8 * k + 5) (8 * k + 9) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range (8 * k + 5)) (Finset.Ico (8 * k + 5) (8 * k + 9)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      rw [Finset.mem_range] at hx1; rw [Finset.mem_Ico] at hx2; omega
    set z4 := ∏ j ∈ Finset.range (8 * k + 5), (⟨1, (j : ℤ)⟩ : GaussianInt)
    have hprod8 : ∏ j ∈ Finset.range (8 * (k + 1) + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        z4 * ⟨2 * (715 + 3952 * (k : ℤ) + 7840 * (k : ℤ) ^ 2 + 6656 * (k : ℤ) ^ 3 + 2048 * (k : ℤ) ^ 4),
              2 * (-8 * ((k : ℤ) + 1) * (128 * ((k : ℤ) + 1) ^ 2 - 72 * ((k : ℤ) + 1) + 9))⟩ := by
      rw [hsp, Finset.prod_union hdisj]
      congr 1
      have h4step : ∏ j ∈ Finset.Ico (8 * k + 5) (8 * k + 9), (⟨1, (j : ℤ)⟩ : GaussianInt) =
          ⟨1, (8 * k + 5 : ℤ)⟩ * ⟨1, (8 * k + 6 : ℤ)⟩ * ⟨1, (8 * k + 7 : ℤ)⟩ * ⟨1, (8 * k + 8 : ℤ)⟩ := by
        rw [show 8 * k + 9 = (8 * k + 8) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 8 = (8 * k + 7) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 7 = (8 * k + 6) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          show 8 * k + 6 = (8 * k + 5) + 1 by omega, Finset.prod_Ico_succ_top (by omega),
          Finset.Ico_self, Finset.prod_empty, one_mul]
        push_cast; rfl
      rw [h4step]
      ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
    obtain ⟨A, B, hZ8, _, _, hB8⟩ := gaussianInt_8k_structure (k + 1)
    rw [hprod8] at hZ8
    have hre8 := congr_arg Zsqrtd.re hZ8
    have him8 := congr_arg Zsqrtd.im hZ8
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, him0, zero_mul, mul_zero, add_zero] at hre8 him8
    set Xg : ℤ := 715 + 3952 * (k : ℤ) + 7840 * (k : ℤ) ^ 2 + 6656 * (k : ℤ) ^ 3 + 2048 * (k : ℤ) ^ 4
    have hXg_odd : Odd Xg := ⟨357 + 1976 * k + 3920 * k ^ 2 + 3328 * k ^ 3 + 1024 * k ^ 4, by
      simp only [Xg]; ring⟩
    have h2k1_z4 : ((2 : ℤ) ^ (2 * k + 1)) ∣ z4.re := by
      have hdvd : ((2 : ℤ) ^ (2 * k + 1)) ∣ z4.re * Xg := by
        refine ⟨A, ?_⟩
        have hpow : (2 : ℤ) ^ (2 * (k + 1)) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ']
        rw [hpow] at hre8
        linarith
      have hcop : IsCoprime ((2 : ℤ) ^ (2 * k + 1)) Xg := by
        have hc2 : IsCoprime (2 : ℤ) Xg := by
          rw [Int.prime_two.irreducible.coprime_iff_not_dvd]
          intro h2; exact (Int.not_even_iff_odd.mpr hXg_odd) (even_iff_two_dvd.mpr h2)
        exact hc2.pow_left
      exact hcop.dvd_of_dvd_mul_right hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk1_dvd : ((2 : ℤ) ^ padicValNat 2 (k + 1)) ∣ ((k : ℤ) + 1) := by
      have : 2 ^ padicValNat 2 (k + 1) ∣ k + 1 := pow_padicValNat_dvd
      exact_mod_cast this
    have hB_dvd : ((2 : ℤ) ^ (padicValNat 2 (k + 1) + 3)) ∣ B := by
      rcases h2k1_z4 with ⟨c, hc⟩
      rcases hk1_dvd with ⟨d, hd⟩
      refine ⟨c * (-d) * (128 * ((k : ℤ) + 1) ^ 2 - 72 * ((k : ℤ) + 1) + 9), ?_⟩
      have hpow1 : (2 : ℤ) ^ (2 * (k + 1)) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ']
      have hpow2 : (2 : ℤ) ^ (padicValNat 2 (k + 1) + 3) = 8 * (2 : ℤ) ^ padicValNat 2 (k + 1) := by
        rw [pow_add]; norm_num; ring
      have hpos : (2 : ℤ) ^ (2 * (k + 1)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      have hd_sub : -8 * ((k : ℤ) + 1) = -8 * ((2 : ℤ) ^ padicValNat 2 (k + 1) * d) := by rw [hd]
      rw [← him8, hc, hpow1, hpow2, hd_sub]
      ring
    exact (hB8 (by omega)).2 hB_dvd
  · rw [show n = 8 * k + 5 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    have hodd : Odd (-5 * ((16 * (k : ℤ) + 9) * A + (1 - (8 * k + 4) * (8 * k + 5)) * B)) := by
      have h1 : Odd (16 * (k : ℤ) + 9) := ⟨8 * k + 4, by ring⟩
      have h5 : Odd (-5 : ℤ) := ⟨-3, by ring⟩
      exact h5.mul ((h1.mul hA).add_even (hBeven.mul_left _))
    have hfac :
        ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * ↑(8 * k + 5) +
        ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * 1 =
        (2 : ℤ) ^ (2 * k + 1) * (-5 * ((16 * (k : ℤ) + 9) * A + (1 - (8 * k + 4) * (8 * k + 5)) * B)) := by
      push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 6 by omega, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    obtain ⟨A, B, hZ, hA, hB0, hB1⟩ := gaussianInt_8k3_structure k
    rw [hZ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    have hBeven : Even B := by
      by_cases hk0 : k = 0
      · rw [hB0 hk0]; exact Even.zero
      · exact even_iff_two_dvd.mpr ((dvd_pow_self (2 : ℤ) (by omega)).trans (hB1 (by omega)).1)
    set cA : ℤ := (16 * (k : ℤ) + 9) + (8 * k + 6) * (1 - (8 * k + 4) * (8 * k + 5))
    set cB : ℤ := (1 - (8 * k + 4) * (8 * k + 5)) - (8 * k + 6) * (16 * k + 9)
    have hcA_odd : Odd cA := by
      have h1 : Odd (16 * (k : ℤ) + 9) := ⟨8 * k + 4, by ring⟩
      have h2 : Even (8 * (k : ℤ) + 6) := ⟨4 * k + 3, by ring⟩
      exact h1.add_even (h2.mul_right _)
    have hodd : Odd (-5 * (cA * A + cB * B)) := by
      have h5 : Odd (-5 : ℤ) := ⟨-3, by ring⟩
      exact h5.mul ((hcA_odd.mul hA).add_even (hBeven.mul_left _))
    have hfac :
        (((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * 1 +
          -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * ↑(8 * k + 5)) * ↑(8 * k + 6) +
        (((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * 1 + -1 * ((2 : ℤ) ^ (2 * k + 1) * (-5 * B)) * ↑(8 * k + 4)) * ↑(8 * k + 5) +
          ((2 : ℤ) ^ (2 * k + 1) * (-5 * A) * ↑(8 * k + 4) + (2 : ℤ) ^ (2 * k + 1) * (-5 * B) * 1) * 1) * 1 =
        (2 : ℤ) ^ (2 * k + 1) * (-5 * (cA * A + cB * B)) := by
      simp only [cA, cB]; push_cast; ring
    rw [hfac]
    intro hzero
    rcases mul_eq_zero.mp hzero with hpow | hsum
    · exact absurd hpow (by positivity)
    · rw [hsum] at hodd
      exact (Int.not_even_iff_odd.mpr hodd) Even.zero
  · rw [show n = 8 * k + 7 by omega]
    intro him0
    obtain ⟨A, B, hZ8, _, _, hB8⟩ := gaussianInt_8k_structure (k + 1)
    have hstep : ∏ j ∈ Finset.range (8 * (k + 1) + 1), (⟨1, (j : ℤ)⟩ : GaussianInt) =
        (∏ j ∈ Finset.range (8 * k + 8), (⟨1, (j : ℤ)⟩ : GaussianInt)) * ⟨1, (8 * k + 8 : ℤ)⟩ := by
      rw [show 8 * (k + 1) + 1 = (8 * k + 8) + 1 by omega, Finset.prod_range_succ]
      push_cast; rfl
    rw [hstep] at hZ8
    have hre8 := congr_arg Zsqrtd.re hZ8
    have him8 := congr_arg Zsqrtd.im hZ8
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, him0, zero_mul, mul_zero, add_zero, mul_one] at hre8 him8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk1_dvd : ((2 : ℤ) ^ padicValNat 2 (k + 1)) ∣ ((k : ℤ) + 1) := by
      have : 2 ^ padicValNat 2 (k + 1) ∣ k + 1 := pow_padicValNat_dvd
      exact_mod_cast this
    have hB_dvd : ((2 : ℤ) ^ (padicValNat 2 (k + 1) + 3)) ∣ B := by
      rcases hk1_dvd with ⟨d, hd⟩
      refine ⟨A * d, ?_⟩
      have hpos : (2 : ℤ) ^ (2 * (k + 1)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      rw [← him8, hre8]
      have hpow2 : (2 : ℤ) ^ (padicValNat 2 (k + 1) + 3) = 8 * (2 : ℤ) ^ padicValNat 2 (k + 1) := by
        rw [pow_add]; norm_num; ring
      rw [hpow2]
      have h8k : (8 * (k : ℤ) + 8) = 8 * ((k : ℤ) + 1) := by ring
      rw [h8k, hd]; ring
    exact (hB8 (by omega)).2 hB_dvd

end OMA.MollNonvanishing

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H2 :=
  fun n hn => OMA.MollNonvanishing.a_ne_zero_of_three_lt n (by omega)
