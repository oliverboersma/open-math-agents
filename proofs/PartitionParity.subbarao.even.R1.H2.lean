import OMAReductions.R_PartitionParity_subbarao_even_R1

/-! If S were finite, its counting function would be bounded by the size of S, while sqrt X
tends to infinity. -/

theorem OMA.solution : OMA.R_PartitionParity_subbarao_even_R1.H2 := by
  intro S h
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨C, hC⟩ := h.bound
  have hbound : ∀ X : ℝ, (({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℕ) : ℝ) ≤ (S.ncard : ℝ) := by
    intro X
    have hsub : {n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S} ⊆ S := fun n hn => hn.2
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have h3 := Real.tendsto_sqrt_atTop.eventually_gt_atTop (|C| * (S.ncard : ℝ))
  obtain ⟨X, h4, h5⟩ := (hC.and h3).exists
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg X), Real.norm_of_nonneg (Nat.cast_nonneg _)] at h4
  have h6 : C * (({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℕ) : ℝ) ≤ |C| * (S.ncard : ℝ) :=
    mul_le_mul (le_abs_self C) (hbound X) (Nat.cast_nonneg _) (abs_nonneg C)
  linarith
