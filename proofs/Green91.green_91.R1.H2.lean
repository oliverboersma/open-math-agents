import OMAReductions.R_Green91_green_91_R1

-- Step Green91.green_91.R1.H2: hypothesis H2 of reduction Green91.green_91.R1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Green91_green_91_R1.H2 := by
  intro f hf
  have h := hf.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast] at hn
  have := le_abs_self (f n)
  linarith
