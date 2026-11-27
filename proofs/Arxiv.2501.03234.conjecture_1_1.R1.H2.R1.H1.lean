import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1
import Mathlib

/-! Step H1: the odd harmonic sum up to a square is at most twice the sum up to its root.
The sum over k below m of 1/(2k+1) is at least half of log (2m+1), and a block from a to b
costs at most half of log b minus log a. -/

-- Step Arxiv.2501.03234.conjecture_1_1.R1.H2.R1.H1: hypothesis H1 of reduction Arxiv.2501.03234.conjecture_1_1.R1.H2.R1
-- Credit: @ivillar

open Finset

lemma oddHarm_lower (m : ℕ) :
    (1 / 2 : ℝ) * Real.log (2 * (m : ℝ) + 1) ≤ ∑ k ∈ range m, (1 : ℝ) / (2 * (k : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have h1 : Real.log ((2 * ((m + 1 : ℕ) : ℝ) + 1) / (2 * (m : ℝ) + 1)) ≤
        (2 * ((m + 1 : ℕ) : ℝ) + 1) / (2 * (m : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at h1
    have h2 : (2 * ((m + 1 : ℕ) : ℝ) + 1) / (2 * (m : ℝ) + 1) - 1 =
        2 * (1 / (2 * (m : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    rw [h2] at h1
    linarith

lemma oddHarm_block (a : ℕ) (ha : 1 ≤ a) (b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ range b, (1 : ℝ) / (2 * (k : ℝ) + 1)) - ∑ k ∈ range a, (1 : ℝ) / (2 * (k : ℝ) + 1) ≤
      (1 / 2 : ℝ) * (Real.log b - Real.log a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_range_succ]
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast ha.trans hb
    have hbpos : (0 : ℝ) < b := by linarith
    have h1 := Real.le_log_one_add_of_nonneg (x := 1 / (b : ℝ)) (by positivity)
    have h2 : 2 * (1 / (b : ℝ)) / (1 / (b : ℝ) + 2) = 2 * (1 / (2 * (b : ℝ) + 1)) := by
      field_simp
      ring
    have h3 : Real.log (1 + 1 / (b : ℝ)) = Real.log ((b + 1 : ℕ) : ℝ) - Real.log b := by
      rw [← Real.log_div (by positivity) hbpos.ne']
      congr 1
      push_cast
      field_simp
    rw [h2, h3] at h1
    linarith

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1.H1 := by
  intro n L hLn hnL
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have hn : n = 0 := by simpa using hnL
    subst hn
    simp
  · have hlow := oddHarm_lower L
    have hblock := oddHarm_block L hL n hLn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hL.trans_le hLn
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have h1 : Real.log n ≤ 2 * Real.log L := by
      have h3 : Real.log n ≤ Real.log ((L : ℝ) ^ 2) :=
        Real.log_le_log hn0 (by exact_mod_cast hnL)
      rw [Real.log_pow] at h3
      push_cast at h3
      exact h3
    have h2 : Real.log L ≤ Real.log (2 * (L : ℝ) + 1) := Real.log_le_log hLpos (by linarith)
    linarith
