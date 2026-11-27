import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1

/-! Two write-bit branches after the fixed zero/one-write prefix returns to state3.
New reduction and three-step trace: Hanan Beer (@hananzlt).
Residual specification: @pageman PR6963, using @henry10101001's freeze reduction
and Hanan Beer's PR6134. This is an auxiliary reduction; both finite bounds
remain separate hypotheses and the full Busy Beaver theorem is not asserted. -/
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1_H4_R1
open Turing Turing.BusyBeaver

def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (r : Fin 4) (left : Bool),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 0 .right) →
  M 2 0 = some (some 3, Stmt.write 1 .left) →
  M 3 0 = some (some r, Stmt.write 0 (if left then .left else .right)) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 106

def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (r : Fin 4) (left : Bool),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 0 .right) →
  M 2 0 = some (some 3, Stmt.write 1 .left) →
  M 3 0 = some (some r, Stmt.write 1 (if left then .left else .right)) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 106

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H4 := by
  intro bound0 bound1 M h0 h1 h2 hRun hUsed _hForm _hMissing _hLoop hHalts
  let t0 : Tape (Fin 2) := Tape.mk₁ []
  let t1 := (t0.write 1).move Dir.right
  let t2 := (t1.write 0).move Dir.right
  let t3 := (t2.write 1).move Dir.left
  have hd0 : t0.head = 0 := rfl
  have hd1 : t1.head = 0 := by decide
  have hd2 : t2.head = 0 := by decide
  have hd3 : t3.head = 0 := by decide
  have step1 : M.multiStep (Machine.init []) 1 = some ⟨some 1, t1⟩ := by
    rw [Machine.multiStep_one]
    change M.step ⟨some 0, t0⟩ = some ⟨some 1, t1⟩
    simp [Machine.step, hd0, h0, t1]
  have step2 : M.multiStep (Machine.init []) 2 = some ⟨some 2, t2⟩ := by
    change M.multiStep (Machine.init []) (Nat.succ 1) = some ⟨some 2, t2⟩
    rw [Machine.multiStep_succ, step1]
    simp [Machine.step, hd1, h1, t2]
  have step3 : M.multiStep (Machine.init []) 3 = some ⟨some 3, t3⟩ := by
    change M.multiStep (Machine.init []) (Nat.succ 2) = some ⟨some 3, t3⟩
    rw [Machine.multiStep_succ, step2]
    simp [Machine.step, hd2, h2, t3]
  obtain ⟨r,z,h3⟩ := (hUsed 3 0).mp ⟨3, by decide, t3, step3, hd3⟩
  have stopped : M.HaltsAfter (Machine.init []) 106 := by
    obtain ⟨a,d⟩ := z
    fin_cases a <;> cases d
    · exact bound0 M r true h0 h1 h2 h3 hHalts
    · exact bound0 M r false h0 h1 h2 h3 hHalts
    · exact bound1 M r true h0 h1 h2 h3 hHalts
    · exact bound1 M r false h0 h1 h2 h3 hHalts
  change M.multiStep (Machine.init []) 107 = none at stopped
  obtain ⟨q,t,live⟩ := hRun
  rw [live] at stopped
  contradiction
end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1_H4_R1
