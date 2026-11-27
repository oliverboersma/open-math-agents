import OMAReductions.R_Mills_exists_least_R2
import Mathlib

-- Step Mills.exists_least.R2.H2: hypothesis H2 of reduction Mills.exists_least.R2
-- Credit: @ivillar. The reduction file itself proves H2 as `dyadicRich`; this step applies it.

/-! Hypothesis H2 of the Mills reduction. -/

theorem OMA.solution : OMA.R_Mills_exists_least_R2.H2 :=
  OMA.R_Mills_exists_least_R2.dyadicRich
