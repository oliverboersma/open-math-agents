import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1

/-!
Split the write-1 length-1 left-turn bound by the target state of `M 1 0`:

* H1 — turn left into state 0 or 1 (overlaps henry/hyprspacecoyote R2.H2.R1.H1)
* H2 — turn left into state 2 (overlaps R2.H2.R1.H2 / H4 by written bit)

Donors: @marcusbuffett H3.R1 sweeps, @hyprspacecoyote R2.H2.R1.H1, @henry10101001 R2.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)) (a : Fin 2) (q : Fin 4),
    q.val ≤ 1 →
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some q, Stmt.write a Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)) (a : Fin 2),
    M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
    M 1 0 = some (some 2, Stmt.write a Dir.left) →
    M.IsHalting → M.HaltsAfter (Machine.init []) 107

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1.H1 := by
  intro h01 h2 M a q hq hFirst hSecond hHalts
  fin_cases q
  · exact h01 M a 0 (by decide) hFirst hSecond hHalts
  · exact h01 M a 1 (by decide) hFirst hSecond hHalts
  · exact h2 M a hFirst hSecond hHalts
  · -- q = 3 contradicts q.val ≤ 2
    exact (Nat.not_le.mpr (by decide : 2 < 3) hq).elim

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1
