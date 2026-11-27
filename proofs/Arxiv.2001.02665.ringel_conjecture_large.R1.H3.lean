import OMAReductions.R_Arxiv_2001_02665_ringel_conjecture_large_R1
import Mathlib

-- Step Arxiv.2001.02665.ringel_conjecture_large.R1.H3: hypothesis H3 of reduction Arxiv.2001.02665.ringel_conjecture_large.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! `C(2n+1, 2) = (2n+1)(2n)/2 = (2n+1) n`. -/

theorem OMA.solution : OMA.R_Arxiv_2001_02665_ringel_conjecture_large_R1.H3 := by
  intro n
  rw [Nat.choose_two_right, show 2 * n + 1 - 1 = 2 * n by omega,
    show (2 * n + 1) * (2 * n) = 2 * ((2 * n + 1) * n) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
