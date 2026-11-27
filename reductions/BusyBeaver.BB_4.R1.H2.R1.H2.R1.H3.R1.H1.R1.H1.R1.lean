import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1

/-!
Split the write-1 length-1 left-turn early-halt bound (target state 0 or 1)
by the written blank bit. Each leaf overlaps a left-turn branch of
@hyprspacecoyote `BusyBeaver.BB_4.R2.H2.R1.H1` (via freeze_bound).

Donors: @hyprspacecoyote R2.H2.R1.H1, @henry10101001 R2 freeze_bound,
@marcusbuffett H3.R1 sweeps.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
    q.val ≤ 1 →
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some q, Stmt.write 0 Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
    q.val ≤ 1 →
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some q, Stmt.write 1 Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1.H1 := by
  intro h0 h1 M a q hq hFirst hSecond hHalts
  fin_cases a
  · exact h0 M q hq hFirst hSecond hHalts
  · exact h1 M q hq hFirst hSecond hHalts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1
