import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1

/-!
Split the write-1 length-1 left-turn early-halt bound (target state 2)
by the written blank bit:

* H1 — write 0 left into state 2 (overlaps @hyprspacecoyote R2.H2.R1.H2)
* H2 — write 1 left into state 2 (overlaps R2.H2.R1.H4 / RepWL special)

Donors: @hyprspacecoyote R2.H2.R1, @henry10101001 freeze_bound, @marcusbuffett H3.R1.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H2_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some 2, Stmt.write 0 Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some 2, Stmt.write 1 Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1.H2 := by
  intro h0 h1 M a hFirst hSecond hHalts
  fin_cases a
  · exact h0 M hFirst hSecond hHalts
  · exact h1 M hFirst hSecond hHalts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H2_R1
