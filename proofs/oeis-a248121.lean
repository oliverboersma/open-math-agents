import OMAStatements.S_oeis_a248121
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Filter Topology

noncomputable section

private def fMinus (x : ℝ) : ℝ :=
  1 / (x + 1 / 2) - 1 / (12 * (x + 1 / 2) ^ 3)

private def fPlus (x : ℝ) : ℝ :=
  1 / (x + 1 / 2) - 1 / (12 * (x + 1 / 2) ^ 3) + 1 / (20 * (x + 1 / 2) ^ 5)

private lemma fMinus_sub_lt (k : ℕ) :
    fMinus (k : ℝ) - fMinus ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1) ^ 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 0 < 2 * (k : ℝ) + 1 := by linarith
  have h2 : 0 < 2 * (k : ℝ) + 3 := by linarith
  have h3 : 0 < (k : ℝ) + 1 := by linarith
  have hdiff :
      1 / ((k : ℝ) + 1) ^ 2 - (fMinus (k : ℝ) - fMinus ((k : ℝ) + 1)) =
        (28 * ((k : ℝ) + 1) ^ 2 - 3) /
          (3 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 3 * (2 * (k : ℝ) + 3) ^ 3) := by
    simp only [fMinus]
    field_simp
    ring
  have hpos :
      0 < (28 * ((k : ℝ) + 1) ^ 2 - 3) /
        (3 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 3 * (2 * (k : ℝ) + 3) ^ 3) := by
    refine div_pos ?_ (by positivity)
    nlinarith
  linarith

private lemma lt_fPlus_sub (k : ℕ) :
    1 / ((k : ℝ) + 1) ^ 2 < fPlus (k : ℝ) - fPlus ((k : ℝ) + 1) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 0 < 2 * (k : ℝ) + 1 := by linarith
  have h2 : 0 < 2 * (k : ℝ) + 3 := by linarith
  have h3 : 0 < (k : ℝ) + 1 := by linarith
  have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hdiff :
      (fPlus (k : ℝ) - fPlus ((k : ℝ) + 1)) - 1 / ((k : ℝ) + 1) ^ 2 =
        (1600 * ((k : ℝ) + 1) ^ 6 + 3068 * ((k : ℝ) + 1) ^ 4 +
          212 * ((k : ℝ) + 1) ^ 2 * (((k : ℝ) + 1) ^ 2 - 1) + 15) /
          (15 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 5 * (2 * (k : ℝ) + 3) ^ 5) := by
    simp only [fPlus]
    field_simp
    ring
  have hpos :
      0 < (1600 * ((k : ℝ) + 1) ^ 6 + 3068 * ((k : ℝ) + 1) ^ 4 +
          212 * ((k : ℝ) + 1) ^ 2 * (((k : ℝ) + 1) ^ 2 - 1) + 15) /
        (15 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 5 * (2 * (k : ℝ) + 3) ^ 5) := by
    refine div_pos ?_ (by positivity)
    have hsub : 0 ≤ ((k : ℝ) + 1) ^ 2 - 1 := by linarith
    positivity
  linarith

private lemma tendsto_fMinus : Tendsto (fun N : ℕ => fMinus (N : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h1 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1 / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h0
  have h3p : Tendsto (fun N : ℕ => 12 * ((N : ℝ) + 1 / 2) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0) |>.comp h0).const_mul_atTop (by norm_num)
  have h3 : Tendsto (fun N : ℕ => 1 / (12 * ((N : ℝ) + 1 / 2) ^ 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h3p
  simpa [fMinus] using h1.sub h3

private lemma tendsto_fPlus : Tendsto (fun N : ℕ => fPlus (N : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h5p : Tendsto (fun N : ℕ => 20 * ((N : ℝ) + 1 / 2) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 5 ≠ 0) |>.comp h0).const_mul_atTop (by norm_num)
  have h5 : Tendsto (fun N : ℕ => 1 / (20 * ((N : ℝ) + 1 / 2) ^ 5)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h5p
  simpa [fPlus, fMinus] using tendsto_fMinus.add h5

private lemma sum_Ico_sub_succ (g : ℕ → ℝ) (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.Ico n N, (g j - g (j + 1)) = g n - g N := by
  induction N with
  | zero =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero h
    subst hn
    simp
  | succ N ih =>
    rcases eq_or_lt_of_le h with rfl | hlt
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega : n ≤ N), ih (by omega)]
      ring

private lemma tail_bounds (n : ℕ) :
    fMinus n ≤ Real.pi ^ 2 / 6 - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ∧
    Real.pi ^ 2 / 6 - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2 ≤ fPlus n := by
  have hsum := (hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity) (Real.pi ^ 2 / 6)).1
    hasSum_zeta_two
  have hsum1 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6)) :=
    hsum.comp (tendsto_add_atTop_nat 1)
  have htail_eq : ∀ N : ℕ, n ≤ N →
      ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 -
          ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 =
        ∑ j ∈ Finset.Ico n N, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
    intro N hN
    have hsplit : ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 =
        ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 +
          ∑ k ∈ Finset.Ico (n + 1) (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
      have h0 : ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 =
          ∑ k ∈ Finset.Ico 1 (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
        simp
      rw [h0, ← Finset.sum_Ico_consecutive (fun k => (1 : ℝ) / (k : ℝ) ^ 2)
        (by omega : 1 ≤ n + 1) (by omega : n + 1 ≤ N + 1)]
      rfl
    rw [hsplit, add_sub_cancel_left]
    rw [← Finset.sum_Ico_add' (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) n N 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hlim_tail :
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 -
        ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2)
      atTop (𝓝 (Real.pi ^ 2 / 6 - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2)) :=
    hsum1.sub tendsto_const_nhds
  constructor
  · have hle : ∀ᶠ (N : ℕ) in atTop,
        fMinus n - fMinus N ≤
          ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 -
            ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 := by
      rw [Filter.eventually_atTop]
      refine ⟨n, fun N hN => ?_⟩
      rw [htail_eq N hN, ← sum_Ico_sub_succ (fun j : ℕ => fMinus (j : ℝ)) n N hN]
      refine Finset.sum_le_sum fun j _ => ?_
      simpa [Nat.cast_add, Nat.cast_one] using (fMinus_sub_lt j).le
    have hlim_lhs : Tendsto (fun N : ℕ => fMinus n - fMinus N) atTop (𝓝 (fMinus n)) := by
      simpa using (tendsto_const_nhds (x := fMinus (n : ℝ))).sub tendsto_fMinus
    exact le_of_tendsto_of_tendsto hlim_lhs hlim_tail hle
  · have hle : ∀ᶠ (N : ℕ) in atTop,
        ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 2 -
            ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 ≤
          fPlus n - fPlus N := by
      rw [Filter.eventually_atTop]
      refine ⟨n, fun N hN => ?_⟩
      rw [htail_eq N hN, ← sum_Ico_sub_succ (fun j : ℕ => fPlus (j : ℝ)) n N hN]
      refine Finset.sum_le_sum fun j _ => ?_
      simpa [Nat.cast_add, Nat.cast_one] using (lt_fPlus_sub j).le
    have hlim_rhs : Tendsto (fun N : ℕ => fPlus n - fPlus N) atTop (𝓝 (fPlus n)) := by
      simpa using (tendsto_const_nhds (x := fPlus (n : ℝ))).sub tendsto_fPlus
    exact le_of_tendsto_of_tendsto hlim_tail hlim_rhs hle

private def b (n : ℕ) : ℤ := (6 * (n : ℤ) ^ 2 + 2 * (n : ℤ)) / 3

private lemma b_mod_zero (m : ℕ) : b (3 * m) = 18 * (m : ℤ) ^ 2 + 2 * (m : ℤ) := by
  simp only [b]
  push_cast
  have h : 6 * (3 * (m : ℤ)) ^ 2 + 2 * (3 * (m : ℤ)) =
      (18 * (m : ℤ) ^ 2 + 2 * (m : ℤ)) * 3 := by ring
  rw [h, Int.mul_ediv_cancel _ (by norm_num)]

private lemma b_mod_one (m : ℕ) : b (3 * m + 1) = 18 * (m : ℤ) ^ 2 + 14 * (m : ℤ) + 2 := by
  simp only [b]
  push_cast
  have h : 6 * (3 * (m : ℤ) + 1) ^ 2 + 2 * (3 * (m : ℤ) + 1) =
      2 + (18 * (m : ℤ) ^ 2 + 14 * (m : ℤ) + 2) * 3 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num)]
  norm_num

private lemma b_mod_two (m : ℕ) : b (3 * m + 2) = 18 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 9 := by
  simp only [b]
  push_cast
  have h : 6 * (3 * (m : ℤ) + 2) ^ 2 + 2 * (3 * (m : ℤ) + 2) =
      1 + (18 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 9) * 3 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num)]
  norm_num

private lemma a_eq_b (n : ℕ) : OMA.S_oeis_a248121.a n = b n := by
  by_cases hn : n = 0
  · subst hn
    simp [OMA.S_oeis_a248121.a, b]
  · simp only [OMA.S_oeis_a248121.a, hn, ↓reduceIte]
    set d : ℝ := 1 / (n : ℝ) - Real.pi ^ 2 / 6 + ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2
    have hd_eq : d = 1 / (n : ℝ) - (Real.pi ^ 2 / 6 - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 2) := by
      simp only [d]; ring
    have htb := tail_bounds n
    have hd_lo : 1 / (n : ℝ) - fPlus n ≤ d := by linarith
    have hd_hi : d ≤ 1 / (n : ℝ) - fMinus n := by linarith
    have hkey : (b n : ℝ) * (1 / (n : ℝ) - fMinus n) < 1 ∧
        1 < ((b n : ℝ) + 1) * (1 / (n : ℝ) - fPlus n) ∧ 0 ≤ b n := by
      have hm_cases : n = 3 * (n / 3) ∨ n = 3 * (n / 3) + 1 ∨ n = 3 * (n / 3) + 2 := by omega
      rcases hm_cases with h | h | h <;> rw [h]
      · set m := n / 3
        have hm1 : 1 ≤ m := by omega
        have hm_pos : (0 : ℝ) < m := by positivity
        rw [b_mod_zero]
        have hn_pos : (0 : ℝ) < 3 * (m : ℝ) := by positivity
        have h6m : (0 : ℝ) < 6 * (m : ℝ) + 1 := by positivity
        have h1 : 1 - ((18 * (m : ℤ) ^ 2 + 2 * (m : ℤ) : ℤ) : ℝ) *
            (1 / ((3 * m : ℕ) : ℝ) - fMinus ((3 * m : ℕ) : ℝ)) =
            (8 * (m : ℝ) + 1) / (3 * (6 * (m : ℝ) + 1) ^ 3) := by
          simp only [fMinus]
          push_cast
          field_simp
          ring
        have h2 : (((18 * (m : ℤ) ^ 2 + 2 * (m : ℤ) : ℤ) : ℝ) + 1) *
            (1 / ((3 * m : ℕ) : ℝ) - fPlus ((3 * m : ℕ) : ℝ)) - 1 =
            (5040 * (m : ℝ) ^ 4 + 3588 * (m : ℝ) ^ 3 + 1052 * (m : ℝ) ^ 2 + 101 * (m : ℝ) + 5) /
              (15 * (m : ℝ) * (6 * (m : ℝ) + 1) ^ 5) := by
          simp only [fPlus]
          push_cast
          field_simp
          ring
        refine ⟨?_, ?_, by positivity⟩
        · have hp : 0 < (8 * (m : ℝ) + 1) / (3 * (6 * (m : ℝ) + 1) ^ 3) := by positivity
          linarith
        · have hp : 0 < (5040 * (m : ℝ) ^ 4 + 3588 * (m : ℝ) ^ 3 + 1052 * (m : ℝ) ^ 2 +
              101 * (m : ℝ) + 5) / (15 * (m : ℝ) * (6 * (m : ℝ) + 1) ^ 5) := by positivity
          linarith
      · set m := n / 3
        have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        rw [b_mod_one]
        have h2m : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
        have h3m : (0 : ℝ) < 3 * (m : ℝ) + 1 := by positivity
        have h1 : 1 - ((18 * (m : ℤ) ^ 2 + 14 * (m : ℤ) + 2 : ℤ) : ℝ) *
            (1 / ((3 * m + 1 : ℕ) : ℝ) - fMinus ((3 * m + 1 : ℕ) : ℝ)) =
            (96 * (m : ℝ) ^ 2 + 95 * (m : ℝ) + 23) /
              (81 * (2 * (m : ℝ) + 1) ^ 3 * (3 * (m : ℝ) + 1)) := by
          simp only [fMinus]
          push_cast
          field_simp
          ring
        have h2 : (((18 * (m : ℤ) ^ 2 + 14 * (m : ℤ) + 2 : ℤ) : ℝ) + 1) *
            (1 / ((3 * m + 1 : ℕ) : ℝ) - fPlus ((3 * m + 1 : ℕ) : ℝ)) - 1 =
            (720 * (m : ℝ) ^ 4 + 1428 * (m : ℝ) ^ 3 + 1200 * (m : ℝ) ^ 2 + 461 * (m : ℝ) + 66) /
              (1215 * (2 * (m : ℝ) + 1) ^ 5 * (3 * (m : ℝ) + 1)) := by
          simp only [fPlus]
          push_cast
          field_simp
          ring
        refine ⟨?_, ?_, by positivity⟩
        · have hp : 0 < (96 * (m : ℝ) ^ 2 + 95 * (m : ℝ) + 23) /
              (81 * (2 * (m : ℝ) + 1) ^ 3 * (3 * (m : ℝ) + 1)) := by positivity
          linarith
        · have hp : 0 < (720 * (m : ℝ) ^ 4 + 1428 * (m : ℝ) ^ 3 + 1200 * (m : ℝ) ^ 2 +
              461 * (m : ℝ) + 66) / (1215 * (2 * (m : ℝ) + 1) ^ 5 * (3 * (m : ℝ) + 1)) := by
            positivity
          linarith
      · set m := n / 3
        have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        rw [b_mod_two]
        have h3m : (0 : ℝ) < 3 * (m : ℝ) + 2 := by positivity
        have h6m : (0 : ℝ) < 6 * (m : ℝ) + 5 := by positivity
        have h1 : 1 - ((18 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 9 : ℤ) : ℝ) *
            (1 / ((3 * m + 2 : ℕ) : ℝ) - fMinus ((3 * m + 2 : ℕ) : ℝ)) =
            (4 * (m : ℝ) + 3) * (15 * (m : ℝ) + 13) /
              (3 * (3 * (m : ℝ) + 2) * (6 * (m : ℝ) + 5) ^ 3) := by
          simp only [fMinus]
          push_cast
          field_simp
          ring
        have h2 : (((18 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 9 : ℤ) : ℝ) + 1) *
            (1 / ((3 * m + 2 : ℕ) : ℝ) - fPlus ((3 * m + 2 : ℕ) : ℝ)) - 1 =
            (8640 * (m : ℝ) ^ 4 + 29124 * (m : ℝ) ^ 3 + 37164 * (m : ℝ) ^ 2 +
              21157 * (m : ℝ) + 4520) /
              (15 * (3 * (m : ℝ) + 2) * (6 * (m : ℝ) + 5) ^ 5) := by
          simp only [fPlus]
          push_cast
          field_simp
          ring
        refine ⟨?_, ?_, by positivity⟩
        · have hp : 0 < (4 * (m : ℝ) + 3) * (15 * (m : ℝ) + 13) /
              (3 * (3 * (m : ℝ) + 2) * (6 * (m : ℝ) + 5) ^ 3) := by positivity
          linarith
        · have hp : 0 < (8640 * (m : ℝ) ^ 4 + 29124 * (m : ℝ) ^ 3 + 37164 * (m : ℝ) ^ 2 +
              21157 * (m : ℝ) + 4520) / (15 * (3 * (m : ℝ) + 2) * (6 * (m : ℝ) + 5) ^ 5) := by
            positivity
          linarith
    rcases hkey with ⟨hup, hlo, hb_nn⟩
    have hb_real_nn : (0 : ℝ) ≤ (b n : ℝ) := by exact_mod_cast hb_nn
    have hb1_pos : (0 : ℝ) < (b n : ℝ) + 1 := by linarith
    have hmul_lo : 1 < ((b n : ℝ) + 1) * d := by
      have := mul_le_mul_of_nonneg_left hd_lo hb1_pos.le
      linarith
    have hd_pos : 0 < d := by
      by_contra hle
      push Not at hle
      have : ((b n : ℝ) + 1) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb1_pos.le hle
      linarith
    have hmul_hi : (b n : ℝ) * d < 1 := by
      have := mul_le_mul_of_nonneg_left hd_hi hb_real_nn
      linarith
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hd_pos]
      exact hmul_hi.le
    · rw [div_lt_iff₀ hd_pos]
      exact hmul_lo

private lemma b_add_three (n : ℕ) : b (n + 3) = b n + 12 * (n : ℤ) + 20 := by
  simp only [b]
  push_cast
  have h : 6 * ((n : ℤ) + 3) ^ 2 + 2 * ((n : ℤ) + 3) =
      (6 * (n : ℤ) ^ 2 + 2 * (n : ℤ)) + (12 * (n : ℤ) + 20) * 3 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

private lemma b_rec (n : ℕ) (hn : 5 < n) :
    b n = 2 * b (n - 1) - b (n - 2) + b (n - 3) - 2 * b (n - 4) + b (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h1 := b_add_three (k + 2)
  have h2 := b_add_three (k + 1)
  have h3 := b_add_three k
  have hk2 : k + 2 + 3 = k + 5 := by omega
  have hk1 : k + 1 + 3 = k + 4 := by omega
  rw [hk2] at h1
  rw [hk1] at h2
  have s1 : k + 5 - 1 = k + 4 := by omega
  have s2 : k + 5 - 2 = k + 3 := by omega
  have s3 : k + 5 - 3 = k + 2 := by omega
  have s4 : k + 5 - 4 = k + 1 := by omega
  have s5 : k + 5 - 5 = k := by omega
  rw [s1, s2, s3, s4, s5]
  push_cast at h1 h2 h3
  linarith

end

theorem OMA.solution : type_of% @OMA.S_oeis_a248121.main := by
  have ha : ∀ n, OMA.S_oeis_a248121.a n = b n := a_eq_b
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [ha]
    exact b_rec n hn
  · ext n
    have hpoly :
        (1 - (PowerSeries.X : PowerSeries ℤ)) ^ 3 *
            (1 + PowerSeries.X + PowerSeries.X ^ 2) * PowerSeries.mk OMA.S_oeis_a248121.a =
          PowerSeries.mk OMA.S_oeis_a248121.a -
            (2 : ℕ) • (PowerSeries.mk OMA.S_oeis_a248121.a * PowerSeries.X ^ 1) +
            PowerSeries.mk OMA.S_oeis_a248121.a * PowerSeries.X ^ 2 -
            PowerSeries.mk OMA.S_oeis_a248121.a * PowerSeries.X ^ 3 +
            (2 : ℕ) • (PowerSeries.mk OMA.S_oeis_a248121.a * PowerSeries.X ^ 4) -
            PowerSeries.mk OMA.S_oeis_a248121.a * PowerSeries.X ^ 5 := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one]
      ring
    have hrhs :
        (PowerSeries.X : PowerSeries ℤ) * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X + 2) =
          (2 : ℕ) • PowerSeries.X ^ 1 + (5 : ℕ) • PowerSeries.X ^ 2 +
            (4 : ℕ) • PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one]
      ring
    rw [hpoly, hrhs]
    simp only [map_sub, map_add, map_nsmul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    rcases le_or_gt n 5 with hn | hn
    · interval_cases n <;> simp [ha, b]
    · have hrec := b_rec n hn
      have hs : ¬(n = 1) ∧ ¬(n = 2) ∧ ¬(n = 3) ∧ ¬(n = 4) := by omega
      have h1 : 1 ≤ n := by omega
      have h2 : 2 ≤ n := by omega
      have h3 : 3 ≤ n := by omega
      have h5 : 5 ≤ n := by omega
      simp only [h1, h2, h3, h5, hs, ↓reduceIte, ha]
      omega
