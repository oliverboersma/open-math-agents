import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

/-! Split the last write-zero case by the next state and, for a new state,
the symbol and direction of its first move on the blank tape. -/
namespace OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q : Fin 4, (q = 0 ∨ q = 1) ∧ M 1 0 = some (some q, Stmt.write 1 Dir.left)) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q : Fin 4, (q = 2 ∨ q = 3) ∧ M 1 0 = some (some q, Stmt.write 1 Dir.left) ∧ ∃ (r : Fin 4) (d : Dir), M q 0 = some (some r, Stmt.write 0 d)) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H3 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q : Fin 4, (q = 2 ∨ q = 3) ∧ M 1 0 = some (some q, Stmt.write 1 Dir.left) ∧ ∃ r : Fin 4, M q 0 = some (some r, Stmt.write 1 Dir.right)) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

def H4 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q : Fin 4, (q = 2 ∨ q = 3) ∧ M 1 0 = some (some q, Stmt.write 1 Dir.left) ∧ ∃ r : Fin 4, M q 0 = some (some r, Stmt.write 1 Dir.left)) →
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) →
  (∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
    ∃ q' z, M q a = some (some q', z)) →
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) →
  (∃ q a, M q a = none) →
  (∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')) →
  ¬ M.IsHalting

theorem main : H1 → H2 → H3 → H4 → OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := by
  intro old zero oneRight oneLeft M first second live used form missing loop
  obtain ⟨q, hsecond⟩ := second
  by_cases hOld : q = 0 ∨ q = 1
  · exact old M first ⟨q, hOld, hsecond⟩ live used form missing loop
  have partition : ∀ v : Fin 4, (v = 0 ∨ v = 1) ∨ (v = 2 ∨ v = 3) := by decide
  have hNew := (partition q).resolve_left hOld
  let t1 : Tape (Fin 2) := ((Tape.mk₁ []).write 0).move .right
  have step1 : M.multiStep (Machine.init []) 1 = some ⟨some (1 : Fin 4), t1⟩ := by
    rw [Machine.multiStep_one]
    change (M 0 0).map _ = _
    rw [first]
    rfl
  have seen : ∃ i < 107, ∃ t : Tape (Fin 2),
      M.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = 0 := by
    refine ⟨2, by decide, (t1.write 1).move .left, ?_, rfl⟩
    change M.multiStep (Machine.init []) (1 + 1) = _
    rw [Machine.multiStep_succ, step1]
    change (M 1 0).map _ = _
    rw [hsecond]
    rfl
  obtain ⟨r, ⟨a, d⟩, hthird⟩ := (used q 0).mp seen
  fin_cases a
  · exact zero M first ⟨q, hNew, hsecond, r, d, hthird⟩ live used form missing loop
  · cases d
    · exact oneLeft M first ⟨q, hNew, hsecond, r, hthird⟩ live used form missing loop
    · exact oneRight M first ⟨q, hNew, hsecond, r, hthird⟩ live used form missing loop
end OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1
