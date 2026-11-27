import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1
import Mathlib

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H1: hypothesis H1 of reduction BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1
-- Credit: @ivillar

/-! A machine all of whose transitions continue never halts
(`Turing.BusyBeaver.Machine.not_isHalting_of_forall_isSome` from FormalConjectures). -/

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1.H1 := by
  unfold OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1.H1
  intro M _ htot
  exact Turing.BusyBeaver.Machine.not_isHalting_of_forall_isSome M htot
