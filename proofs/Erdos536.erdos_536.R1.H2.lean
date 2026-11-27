import OMAReductions.R_Erdos536_erdos_536_R1
import Mathlib

-- Step Erdos536.erdos_536.R1.H2: hypothesis H2 of reduction Erdos536.erdos_536.R1
-- Credit: @ivillar. The reduction file itself proves H2 as `roth_bound` (Roth/corners theorem in
-- (ZMod 3)^h); this step applies it.

/-! The density bound for 3-AP-free sets in (ZMod 3)^h. -/

theorem OMA.solution : OMA.R_Erdos536_erdos_536_R1.H2 :=
  OMA.R_Erdos536_erdos_536_R1.roth_bound
