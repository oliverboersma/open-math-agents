import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1

/-!
# Split the two-cell initial sweep by its write symbols

The four obligations fix the two write symbols. In the all-zero family, return
states zero and one are eliminated: the first has a three-step sweep advancing
right forever, and the second has a two-step loop after the initial move.

Reduction and loop proofs: Hanan Beer (@hananzlt). The parent sweep normalization
is by @marcusbuffett (PR4509), adapting the first-transition normalization of
James Halldon (@Halldon). This is an auxiliary reduction of the four-state
Busy Beaver upper bound, not a proof of the complete bound.
-/

namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1
open Turing Turing.BusyBeaver

private theorem zero_return_nonhalting (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 0, Stmt.write 0 .left)) : ¬ M.IsHalting := by
  let blank : ListBlank (Fin 2) := ListBlank.mk []
  have hb : (ListBlank.mk [0] : ListBlank (Fin 2)) = ListBlank.mk [] :=
    ListBlank.cons_head_tail blank
  have trace (n : ℕ) : ∃ L : ListBlank (Fin 2),
      M.multiStep (Machine.init []) (3*n) = some ⟨some 0, ⟨0,L,blank⟩⟩ := by
    induction n with
    | zero => exact ⟨blank,rfl⟩
    | succ n ih =>
      obtain ⟨L,ih⟩ := ih
      refine ⟨L.cons 1,?_⟩
      rw [show 3*(n+1) = 3*n+1+1+1 by omega]
      rw [Machine.multiStep_succ,Machine.multiStep_succ,Machine.multiStep_succ,ih]
      simp [Machine.step,h0,h1,h2,Tape.write,Tape.move,blank,hb]
  intro halts
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have stopped := Machine.multiStep_eq_none_mono hn (show n+1 ≤ 3*(n+1) by omega)
  obtain ⟨L,hL⟩ := trace (n+1)
  rw [hL] at stopped
  contradiction

private theorem one_return_nonhalting (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 1, Stmt.write 0 .left)) : ¬ M.IsHalting := by
  let blank : ListBlank (Fin 2) := ListBlank.mk []
  have hb : (ListBlank.mk [0] : ListBlank (Fin 2)) = ListBlank.mk [] :=
    ListBlank.cons_head_tail blank
  have trace (n : ℕ) : M.multiStep (Machine.init []) (2*n+1) =
      some ⟨some 1, ⟨0,blank.cons 1,blank⟩⟩ := by
    induction n with
    | zero => simp [Machine.init,Tape.mk₁,Tape.mk₂,Tape.mk',Machine.step,h0,Tape.write,Tape.move,blank]
    | succ n ih =>
      rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega]
      rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
      simp [Machine.step,h1,h2,Tape.write,Tape.move,blank,hb]
  intro halts
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have stopped := Machine.multiStep_eq_none_mono hn (show n+1 ≤ 2*(n+1)+1 by omega)
  rw [trace (n+1)] at stopped
  contradiction

/-- Both later writes are zero, and the return state is two or three. -/
def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4), 2 ≤ q.val →
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 0 .right) →
  M 2 0 = some (some q, Stmt.write 0 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

/-- The second write is zero and the left-turn write is one. -/
def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 0 .right) →
  M 2 0 = some (some q, Stmt.write 1 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

/-- The second write is one and the left-turn write is zero. -/
def H3 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 1 .right) →
  M 2 0 = some (some q, Stmt.write 0 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

/-- Both later writes are one. -/
def H4 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)) (q : Fin 4),
  M 0 0 = some (some 1, Stmt.write 1 .right) →
  M 1 0 = some (some 2, Stmt.write 1 .right) →
  M 2 0 = some (some q, Stmt.write 1 .left) →
  M.IsHalting → M.HaltsAfter (Machine.init []) 107

theorem main : H1 → H2 → H3 → H4 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1.H2 := by
  intro h00 h01 h10 h11 M a b q h0 h1 h2 halts
  fin_cases a <;> fin_cases b
  · by_cases hq : 2 ≤ q.val
    · exact h00 M q hq h0 h1 h2 halts
    · fin_cases q
      · exact (zero_return_nonhalting M h0 h1 h2 halts).elim
      · exact (one_return_nonhalting M h0 h1 h2 halts).elim
      · contradiction
      · contradiction
  · exact h01 M q h0 h1 h2 halts
  · exact h10 M q h0 h1 h2 halts
  · exact h11 M q h0 h1 h2 halts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1
