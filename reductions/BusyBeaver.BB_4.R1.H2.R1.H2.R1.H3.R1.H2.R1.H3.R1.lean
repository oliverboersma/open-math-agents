import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1

/-!
Hanan Beer (@hananzlt), assisted by Codex, groups this one/zero-write family
by return state. The middle pair shares one proof component within the
submission size limit. This is an exhaustive auxiliary reduction.
The parent normalization is by Marcus Buffett (@marcusbuffett), adapting
James Halldon (@Halldon); their attribution is retained.
-/

namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 1 .right) →
  M 2 0 = some (some 0, Stmt.write 0 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
  (q = 1 ∨ q = 2) →
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 1 .right) →
  M 2 0 = some (some q, Stmt.write 0 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

def H3 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 1 .right) →
  M 2 0 = some (some 3, Stmt.write 0 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

theorem main : H1 → H2 → H3 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1.H3 := by
  intro h0 h12 h3 M q h00 h10 h20 hm
  fin_cases q
  · exact h0 M h00 h10 h20 hm
  · exact h12 M 1 (by decide) h00 h10 h20 hm
  · exact h12 M 2 (by decide) h00 h10 h20 hm
  · exact h3 M h00 h10 h20 hm

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1
