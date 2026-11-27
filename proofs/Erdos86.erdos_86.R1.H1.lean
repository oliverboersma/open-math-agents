import OMAReductions.R_Erdos86_erdos_86_R1

/-!
The reduction file already proves this hypothesis as `face_averaging`; this file applies it.
-/

theorem OMA.solution : OMA.R_Erdos86_erdos_86_R1.H1 :=
  OMA.R_Erdos86_erdos_86_R1.face_averaging
