import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1

/-!
Freeze the length-2 all-zero-write early-halt bound (return state ≥ 2) into
R2 residual shape, split by return state:

* H1 — `M 2 0` returns to state 2 writing 0 left
* H2 — `M 2 0` returns to state 3 writing 0 left

Donors: @henry10101001 R2.freeze_bound, @hananzlt H2.R1 sweep split.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →
  M 2 0 = some (some 2, Stmt.write 0 Dir.left) →
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

def H2 : Prop := ∀ (M : Machine (Fin 2) (Fin 4)),
  M 0 0 = some (some 1, Stmt.write 1 Dir.right) →
  M 1 0 = some (some 2, Stmt.write 0 Dir.right) →
  M 2 0 = some (some 3, Stmt.write 0 Dir.left) →
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

theorem run_add (M : Machine (Fin 2) (Fin 4)) (x : Cfg (Fin 2) (Fin 4)) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem no_repeat {M : Machine (Fin 2) (Fin 4)} (halts : M.IsHalting)
    {i p : ℕ} (hp : 0 < p) {α : Type} (cfg : α → Cfg (Fin 2) (Fin 4))
    (entered : ∃ v, M.multiStep (Machine.init []) i = some (cfg v))
    (cycle : ∀ v, ∃ w, M.multiStep (cfg v) p = some (cfg w)) : False := by
  have recur (m : ℕ) : ∃ v, M.multiStep (Machine.init []) (i + p * m) = some (cfg v) := by
    induction m with
    | zero => simpa using entered
    | succ m ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := cycle v
      refine ⟨w, ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (i + p * m) p, hv]
      exact hw
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  obtain ⟨v, hv⟩ := recur (k + 1)
  have hle : k + 1 ≤ i + p * (k + 1) := by
    have := Nat.mul_le_mul_right (k + 1) hp
    omega
  have hnone := Machine.multiStep_eq_none_mono hk hle
  rw [hv] at hnone
  contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem freeze_bound
    (residual2 : H1) (residual3 : H2)
    (M : Machine (Fin 2) (Fin 4)) (q : Fin 4) (hq : 2 ≤ q.val)
    (h0 : M 0 0 = some (some 1, Stmt.write 1 Dir.right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 Dir.right))
    (h2 : M 2 0 = some (some q, Stmt.write 0 Dir.left))
    (halts : M.IsHalting) :
    M.HaltsAfter (Machine.init []) 107 := by
  classical
  by_contra late
  let start : Cfg (Fin 2) (Fin 4) := Machine.init []
  have alive (i : ℕ) (hi : i ≤ 108) : M.multiStep start i ≠ none :=
    fun h => late (Machine.multiStep_eq_none_mono h hi)
  let seen (q : Fin 4) (a : Fin 2) : Prop := ∃ i < 107, ∃ t : Tape (Fin 2),
    M.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a
  let P : Machine (Fin 2) (Fin 4) := fun q a => if seen q a then M q a else none
  have used {q a} (h : seen q a) : ∃ r z, M q a = some (some r, z) := by
    obtain ⟨i, hi, t, ht, rfl⟩ := h
    have ha := alive (i + 1 + 1) (by omega)
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ht] at ha
    cases hc : M q t.head with
    | none => simp [Machine.step, hc] at ha
    | some entry =>
      obtain ⟨s, z⟩ := entry
      cases s with
      | none => simp [Machine.step, hc] at ha
      | some s => exact ⟨s, z, rfl⟩
  have agree (i : ℕ) (hi : i ≤ 107) : P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ, ih (by omega)]
      cases h : M.multiStep start i with
      | none => rfl
      | some c =>
        obtain ⟨q, t⟩ := c
        cases q with
        | none => rfl
        | some q =>
          have hv : seen q t.head := ⟨i, by omega, t, h, rfl⟩
          simp [Machine.step, P, hv]
  have restrictRun (i : ℕ) : P.multiStep start i = none ∨ P.multiStep start i = M.multiStep start i := by
    induction i with
    | zero => exact Or.inr rfl
    | succ i ih =>
      rw [Machine.multiStep_succ, Machine.multiStep_succ]
      rcases ih with hi | hi
      · simp [hi]
      · rw [hi]
        cases hc : M.multiStep start i with
        | none => exact Or.inl rfl
        | some c =>
          obtain ⟨q, t⟩ := c
          cases q with
          | none => exact Or.inl rfl
          | some q => by_cases h : seen q t.head <;> simp [Machine.step, P, h]
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  have haltP : P.IsHalting := by
    apply (Machine.isHalting_iff_exists_haltsAt P).mpr
    refine ⟨k, ?_⟩
    rcases restrictRun (k + 1) with h | h
    · exact h
    · exact h.trans hk
  -- Steps 0,1,2 visit (0,0), (1,0), (2,0) on the blank-tape prefix.
  have seen00 : seen 0 0 := ⟨0, by decide, Tape.mk₁ [], rfl, rfl⟩
  have seen10 : seen 1 0 := by
    refine ⟨1, by decide, ?_⟩
    have hs : M.step start =
        some ⟨some 1, (Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right⟩ := by
      have hhd : (Tape.mk₁ (Γ := Fin 2) []).head = 0 := rfl
      simp [Machine.step, Machine.init, start, hhd, h0]
    refine ⟨(Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right, ?_, ?_⟩
    · rwa [Machine.multiStep_one]
    · simp [Tape.write, Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk']
  have seen20 : seen 2 0 := by
    refine ⟨2, by decide, ?_⟩
    -- After `0→1RB`, `1→2RB` the head is again blank in state 2.
    have step1 : M.multiStep start 1 =
        some ⟨some 1, (Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right⟩ := by
      have hs : M.step start =
          some ⟨some 1, (Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right⟩ := by
        have hhd : (Tape.mk₁ (Γ := Fin 2) []).head = 0 := rfl
        simp [Machine.step, Machine.init, start, hhd, h0]
      rwa [Machine.multiStep_one]
    have hhd1 : ((Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right).head = (0 : Fin 2) := by
      decide
    have step2 : M.multiStep start (Nat.succ 1) =
        some ⟨some 2,
          (((Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right).write 0 |>.move Dir.right)⟩ := by
      rw [Machine.multiStep_succ, step1]
      simp [Machine.step, hhd1, h1]
    have step2' : M.multiStep start 2 =
        some ⟨some 2,
          (((Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right).write 0 |>.move Dir.right)⟩ :=
      step2
    refine ⟨(((Tape.mk₁ (Γ := Fin 2) []).write 1 |>.move Dir.right).write 0 |>.move Dir.right),
      step2', ?_⟩
    decide
  have h0P : P 0 0 = some (some 1, Stmt.write 1 Dir.right) := by simpa [P, seen00] using h0
  have h1P : P 1 0 = some (some 2, Stmt.write 0 Dir.right) := by simpa [P, seen10] using h1
  have h2P : P 2 0 = some (some q, Stmt.write 0 Dir.left) := by simpa [P, seen20] using h2
  have hRunP : ∃ q t, P.multiStep start 107 = some ⟨some q, t⟩ := by
    obtain ⟨q0, t, ht⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) 107 late
    exact ⟨q0, t, (agree 107 (by decide)).trans ht⟩
  have hUsedP : ∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
      P.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a) ↔
      ∃ q' z, P q a = some (some q', z) := by
    intro q a
    have eq : (∃ i < 107, ∃ t : Tape (Fin 2), P.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a) ↔
        seen q a := by
      constructor <;> rintro ⟨i, hi, t, ht, ha⟩ <;> refine ⟨i, hi, t, ?_, ha⟩
      · exact (agree i (by omega)).symm.trans ht
      · exact (agree i (by omega)).trans ht
    apply eq.trans
    by_cases h : seen q a
    · simpa [P, h] using used h
    · simp [P, h]
  have hFormP : ∀ q a, P q a = none ∨ ∃ q' z, P q a = some (some q', z) := by
    intro q a
    by_cases h : seen q a
    · right; simpa [P, h] using used h
    · left; simp [P, h]
  have hMissingP : ∃ q a, P q a = none := by
    by_contra! all
    apply Machine.not_isHalting_of_forall_isSome P _ haltP
    intro q a
    by_cases h : seen q a
    · simpa [P, h] using used h
    · exact (all q a (by simp [P, h])).elim
  have hLoopP : ∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
      (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank (Fin 2) =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
    (∃ tail, P.multiStep start i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', P.multiStep (cfg tail) p = some (cfg tail') := by
    intro i p q a side near fixed hp _ cfg enter loop
    exact no_repeat haltP hp cfg enter loop
  fin_cases q
  · exact (Nat.not_le.mpr (by decide : (0 : ℕ) < 2) hq).elim
  · exact (Nat.not_le.mpr (by decide : (1 : ℕ) < 2) hq).elim
  · exact residual2 P h0P h1P h2P hRunP hUsedP hFormP hMissingP hLoopP haltP
  · exact residual3 P h0P h1P h2P hRunP hUsedP hFormP hMissingP hLoopP haltP

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1.H1 := by
  intro h2 h3 M q hq h0 h1 h2' hHalts
  exact freeze_bound h2 h3 M q hq h0 h1 h2' hHalts

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H1_R1
