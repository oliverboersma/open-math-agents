import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1
import Mathlib

-- Step Green3.green_3.R1.H2.R1.H2.R1.H3: hypothesis H3 of reduction Green3.green_3.R1.H2.R1.H2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Weight the hypothesis at `n` by `q ^ n` and sum over all `n`. The left side becomes
`∑ t ∈ T, (q ^ (t + a + 1) + q ^ (t + 1) + q ^ (t + 1 - a)) / (1 - q)` (three geometric tails per
element of `T`), the right side is `∑ n, n * q ^ n = q / (1 - q) ^ 2`. Since
`q ^ (2 * a) + 1 ≥ 2 * q ^ a`, each bracket is at least `3 * q ^ (t + 1)`, which gives
`3 * (1 - q) * ∑ t ∈ T, q ^ t ≤ 1`.
-/

namespace Green3StepH3

open Finset

/-- Geometric tail: the sum of `q ^ n` over `n ≥ k`. -/
lemma hasSum_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    HasSum (fun n : ℕ => if k ≤ n then q ^ n else 0) (q ^ k * (1 - q)⁻¹) := by
  rw [← hasSum_nat_add_iff' k]
  have h : (fun n : ℕ => if k ≤ n + k then q ^ (n + k) else 0) = fun n => q ^ k * q ^ n := by
    funext n
    simp [pow_add, mul_comm]
  have hz : ∑ i ∈ range k, (if k ≤ i then q ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [not_le.mpr (Finset.mem_range.mp hi)]
  rw [h, hz, sub_zero]
  exact (hasSum_geometric_of_lt_one hq0 hq1).mul_left _

/-- A sum of indicator weights is the size of the filtered set times the weight. -/
lemma sum_ite_eq_card_mul (T : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (w : ℝ) :
    ∑ t ∈ T, (if P t then w else 0) = ((T.filter P).card : ℝ) * w := by
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem main_bound (T : Finset ℕ) (a : ℕ) (hTa : ∀ i ∈ T, a ≤ i)
    (hcnt : ∀ n : ℕ, (T.filter (· < n - a)).card + (T.filter (· < n)).card +
      (T.filter (· < n + a)).card ≤ n)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : (1 - q) * (∑ i ∈ T, q ^ i) ≤ 1 / 3 := by
  have h1q : 0 < 1 - q := by linarith
  have hq0' : q ≠ 0 := hq0.ne'
  have h1q' : 1 - q ≠ 0 := h1q.ne'
  -- the weighted hypothesis, pointwise in `n`
  have hL : ∀ n : ℕ,
      (∑ t ∈ T, ((if t + a + 1 ≤ n then q ^ n else 0) + (if t + 1 ≤ n then q ^ n else 0)
        + (if t + 1 - a ≤ n then q ^ n else 0))) ≤ (n : ℝ) * q ^ n := by
    intro n
    have f1 : T.filter (fun t => t + a + 1 ≤ n) = T.filter (· < n - a) := by
      apply Finset.filter_congr
      intro t _
      omega
    have f2 : T.filter (fun t => t + 1 ≤ n) = T.filter (· < n) := by
      apply Finset.filter_congr
      intro t _
      omega
    have f3 : T.filter (fun t => t + 1 - a ≤ n) = T.filter (· < n + a) := by
      apply Finset.filter_congr
      intro t ht
      have := hTa t ht
      omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_eq_card_mul, sum_ite_eq_card_mul,
      sum_ite_eq_card_mul, f1, f2, f3, ← add_mul, ← add_mul]
    have hc : (((T.filter (· < n - a)).card + (T.filter (· < n)).card +
        (T.filter (· < n + a)).card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcnt n
    push_cast at hc
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hS : HasSum (fun n : ℕ => ∑ t ∈ T, ((if t + a + 1 ≤ n then q ^ n else 0)
      + (if t + 1 ≤ n then q ^ n else 0) + (if t + 1 - a ≤ n then q ^ n else 0)))
      (∑ t ∈ T, (q ^ (t + a + 1) * (1 - q)⁻¹ + q ^ (t + 1) * (1 - q)⁻¹
        + q ^ (t + 1 - a) * (1 - q)⁻¹)) :=
    hasSum_sum fun t _ => ((hasSum_tail hq0.le hq1 _).add (hasSum_tail hq0.le hq1 _)).add
      (hasSum_tail hq0.le hq1 _)
  have hR : HasSum (fun n : ℕ => (n : ℝ) * q ^ n) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have key := hasSum_le hL hS hR
  have hlow : ∑ t ∈ T, 3 * q ^ (t + 1) * (1 - q)⁻¹ ≤
      ∑ t ∈ T, (q ^ (t + a + 1) * (1 - q)⁻¹ + q ^ (t + 1) * (1 - q)⁻¹
        + q ^ (t + 1 - a) * (1 - q)⁻¹) := by
    apply Finset.sum_le_sum
    intro t ht
    have hat := hTa t ht
    have e1 : q ^ (t + a + 1) = q ^ (t + 1 - a) * (q ^ a) ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have e2 : q ^ (t + 1) = q ^ (t + 1 - a) * q ^ a := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2]
    have hy : 0 ≤ q ^ (t + 1 - a) := by positivity
    have hinv : 0 ≤ (1 - q)⁻¹ := by positivity
    nlinarith [mul_nonneg (mul_nonneg hy hinv) (sq_nonneg (q ^ a - 1))]
  have h3 : 3 * (1 - q)⁻¹ * (q * ∑ t ∈ T, q ^ t) ≤ q / (1 - q) ^ 2 := by
    have e : 3 * (1 - q)⁻¹ * (q * ∑ t ∈ T, q ^ t) = ∑ t ∈ T, 3 * q ^ (t + 1) * (1 - q)⁻¹ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [e]
    exact hlow.trans key
  have h4 := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ (1 - q) ^ 2 / q by positivity)
  have e3 : 3 * (1 - q)⁻¹ * (q * ∑ t ∈ T, q ^ t) * ((1 - q) ^ 2 / q)
      = 3 * ((1 - q) * ∑ t ∈ T, q ^ t) := by
    field_simp
  have e4 : q / (1 - q) ^ 2 * ((1 - q) ^ 2 / q) = 1 := by
    field_simp
  rw [e3, e4] at h4
  linarith

end Green3StepH3

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H3 := by
  intro T a hTa hcnt q hq0 hq1
  exact Green3StepH3.main_bound T a hTa hcnt q hq0 hq1
