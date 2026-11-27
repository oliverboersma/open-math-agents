import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1

/-!
Split the write-1 / write-1-left / state-0 residual into the RepWL special0
machine (and its 2↔3 reindex encoding) versus the generic FAR case.

* H1 — residual nonhalting away from special0 (tv_b3)
* H2 — nonhalting of special0

Donors: @hyprspacecoyote R2.H2.R1 / R2.H2.R1.H1, @marcusbuffett R2.H3 (BB4Sweeps).
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1_H1_R1

open Turing Turing.BusyBeaver

/-- FAR residual: same residual hypotheses as the parent, excluding the two
special0 encodings `[6,3,3,8,15,10,16,1]` and its 2↔3 reindex
`[6,3,3,12,16,1,11,14]` (as in `BusyBeaver.BB_4.R2.H2.R1`). -/
def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M 1 0 = some (some 0, Stmt.write 1 Dir.left) →
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
  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
    let v := entries[2 * q.val + a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
        (if v % 2 = 0 then Dir.right else Dir.left))
  M ≠ tbl [6, 3, 3, 8, 15, 10, 16, 1] →
  M ≠ tbl [6, 3, 3, 12, 16, 1, 11, 14] →
  ¬ M.IsHalting

/-- Nonhalting of the RepWL special0 machine. -/
def H2 : Prop :=
  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
    let v := entries[2 * q.val + a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
        (if v % 2 = 0 then Dir.right else Dir.left))
  ¬ (tbl [6, 3, 3, 8, 15, 10, 16, 1]).IsHalting

theorem main : H1 → H2 →
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro hFar hSp0 M hFirst hSecond hRun hUsed hForm hMissing hLoop hHalts
  let swap23 : Equiv.Perm (Fin 4) := Equiv.swap (2 : Fin 4) (3 : Fin 4)
  have hswap0 : swap23 0 = 0 := by decide
  have hswap1 : swap23 1 = 1 := by decide
  have hswap2 : swap23 2 = 3 := by decide
  have hswap3 : swap23 3 = 2 := by decide
  have hswap_inv : ∀ q : Fin 4, swap23 (swap23 q) = q := by intro q; fin_cases q <;> decide
  let reindex23 (N : Machine (Fin 2) (Fin 4)) : Machine (Fin 2) (Fin 4) :=
    fun q a => (N (swap23 q) a).map fun (s, b) => (s.map swap23, b)
  let mapCfg23 (c : Cfg (Fin 2) (Fin 4)) : Cfg (Fin 2) (Fin 4) := ⟨c.q.map swap23, c.tape⟩
  have reindex23_step (N : Machine (Fin 2) (Fin 4)) (c : Cfg (Fin 2) (Fin 4)) :
      (reindex23 N).step (mapCfg23 c) = (N.step c).map mapCfg23 := by
    obtain ⟨q, t⟩ := c
    cases q with
    | none => rfl
    | some q =>
      simp only [Machine.step, mapCfg23, Option.map_some, reindex23, hswap_inv]
      cases N q t.head <;> rfl
  have reindex23_multi (N : Machine (Fin 2) (Fin 4)) (c : Cfg (Fin 2) (Fin 4)) (k : ℕ) :
      (reindex23 N).multiStep (mapCfg23 c) k = (N.multiStep c k).map mapCfg23 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
      cases N.multiStep c k with
      | none => rfl
      | some c' => exact reindex23_step N c'
  have mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
    simp [mapCfg23, Machine.init, hswap0]
  have reindex23_isHalting (N : Machine (Fin 2) (Fin 4)) (h : N.IsHalting) :
      (reindex23 N).IsHalting := by
    obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt N).mp h
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl
  let tbl (entries : List ℕ) : Machine (Fin 2) (Fin 4) := fun q a =>
    let v := entries[2 * q.val + a.val]?.getD 16
    if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
      Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩
        (if v % 2 = 0 then Dir.right else Dir.left))
  have hNeSp0 : M ≠ tbl [6, 3, 3, 8, 15, 10, 16, 1] := by
    intro heq; rw [heq] at hHalts; exact hSp0 hHalts
  have hNeSp0Swap : M ≠ tbl [6, 3, 3, 12, 16, 1, 11, 14] := by
    intro heq
    have hH := reindex23_isHalting M hHalts
    have hEq : reindex23 M = tbl [6, 3, 3, 8, 15, 10, 16, 1] := by
      subst heq; funext q a; fin_cases q <;> fin_cases a <;>
        simp [reindex23, tbl, hswap0, hswap1, hswap2, hswap3]
    rw [hEq] at hH; exact hSp0 hH
  exact hFar M hFirst hSecond hRun hUsed hForm hMissing hLoop hNeSp0 hNeSp0Swap hHalts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H1_R1_H1_R1_H2_R1_H1_R1
