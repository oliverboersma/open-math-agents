import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1

/-!
The reduction file already proves this hypothesis as `frobeniusKernel`; this file applies it.
-/

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1.H1 :=
  OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1.frobeniusKernel
