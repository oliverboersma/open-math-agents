import OMAReductions.R_Erdos651_erdos_651_R1
import Mathlib

-- Step Erdos651.erdos_651.R1.H2: hypothesis H2 of reduction Erdos651.erdos_651.R1
-- Credit: @ivillar (original proof).
-- Strategy. With eps = log_2 (1 + c) > 0, eventually F n <= 2^(eps n) = (1 + c)^n < F n.

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1.H2 := by
  intro F hF ⟨c, hc, hlow⟩
  have hc1 : (1 : ℝ) < 1 + c := by linarith
  have hε : 0 < Real.logb 2 (1 + c) := Real.logb_pos (by norm_num) hc1
  obtain ⟨n, hn1, hn2⟩ := ((hF _ hε).and hlow).exists
  have hpow : (2 : ℝ) ^ (Real.logb 2 (1 + c) * (n : ℝ)) = (1 + c) ^ n := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_natCast]
  rw [hpow] at hn1
  linarith
