import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1

-- Step BusyBeaver.BB_4.R1.H2.R1.H2.R1.H2: hypothesis H2 of reduction BusyBeaver.BB_4.R1.H2.R1.H2.R1
-- Credit: @ishaanzee
-- Proof: multiStep_eq_none_mono: once the run is none it stays none.

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1.H2 := by
  unfold OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1.H2
  rintro M - ⟨k, hk, h⟩
  exact Machine.multiStep_eq_none_mono h (by omega)
