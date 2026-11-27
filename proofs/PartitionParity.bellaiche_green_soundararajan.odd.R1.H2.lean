import OMAReductions.R_PartitionParity_bellaiche_green_soundararajan_odd_R1

-- Step PartitionParity.bellaiche_green_soundararajan.odd.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_PartitionParity_bellaiche_green_soundararajan_odd_R1.H2 := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlog2 : ∀ᶠ X : ℝ in atTop, (1 : ℝ) ≤ Real.log (Real.log X) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  filter_upwards [hlog2] with X hX
  have hsq : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hlhs : 0 ≤ Real.sqrt X / Real.log (Real.log X) := div_nonneg hsq (by linarith)
  rw [Real.norm_of_nonneg hlhs, Real.norm_of_nonneg hsq, one_mul]
  exact div_le_self hsq hX
