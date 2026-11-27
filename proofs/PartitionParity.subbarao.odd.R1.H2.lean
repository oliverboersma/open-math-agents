import OMAReductions.R_PartitionParity_subbarao_odd_R1

/-! If S were finite, its counting function would be bounded by the size of S, while
sqrt X / log X tends to infinity: log X ≤ 4 X^(1/4), so the quotient is at least X^(1/4) / 4. -/

namespace OMASubbaraoOdd
open Filter

lemma tendsto_sqrt_div_log :
    Tendsto (fun X : ℝ => Real.sqrt X / Real.log X) atTop atTop := by
  have h1 : Tendsto (fun X : ℝ => X ^ (1 / 4 : ℝ) / 4) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  have h2 : Real.log X ≤ X ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2' : Real.log X ≤ 4 * X ^ (1 / 4 : ℝ) := by
    calc Real.log X ≤ X ^ (1 / 4 : ℝ) / (1 / 4) := h2
      _ = 4 * X ^ (1 / 4 : ℝ) := by ring
  have h3 : Real.sqrt X = X ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    norm_num
  have h4 : 0 < X ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [le_div_iff₀ hlog, h3]
  nlinarith [mul_le_mul_of_nonneg_left h2' h4.le]

end OMASubbaraoOdd

theorem OMA.solution : OMA.R_PartitionParity_subbarao_odd_R1.H2 := by
  intro S h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨C, hC⟩ := h.bound
  have hbound : ∀ X : ℝ, (({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℕ) : ℝ) ≤ (S.ncard : ℝ) := by
    intro X
    have hsub : {n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S} ⊆ S := fun n hn => hn.2
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have h3 := OMASubbaraoOdd.tendsto_sqrt_div_log.eventually_gt_atTop (|C| * (S.ncard : ℝ))
  obtain ⟨X, ⟨h4, h5⟩, hX1⟩ := ((hC.and h3).and (Filter.eventually_gt_atTop (1 : ℝ))).exists
  have hnn : 0 ≤ Real.sqrt X / Real.log X :=
    div_nonneg (Real.sqrt_nonneg X) (Real.log_pos hX1).le
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (Nat.cast_nonneg _)] at h4
  have h6 : C * (({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℕ) : ℝ) ≤ |C| * (S.ncard : ℝ) :=
    mul_le_mul (le_abs_self C) (hbound X) (Nat.cast_nonneg _) (abs_nonneg C)
  linarith
