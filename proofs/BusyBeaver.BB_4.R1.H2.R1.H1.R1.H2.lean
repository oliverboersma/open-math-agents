import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

/-! Early-halt mono for write-0 first transition. -/
-- Credit: @pageman

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H2 := by
  intro M _hFirst
  rintro ⟨k, hk, hhalt⟩
  exact Machine.multiStep_eq_none_mono hhalt (Nat.succ_le_succ hk)
