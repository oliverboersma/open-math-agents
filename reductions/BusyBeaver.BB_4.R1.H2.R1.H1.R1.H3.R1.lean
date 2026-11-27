import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

/-!
Split write-0 survivors into the henry10101001 R2 residual shape:

* H1 — total machines (every transition continues) never halt
* H2 — R2.H1 residual: used-transition / RepWL filter implies nonhalting

Main reuses the freeze_bound argument from BusyBeaver.BB_4.R2: an IsHalting
machine that survives 107 steps restricts to a partial table to which H2
applies, contradicting noEarly. Donors: @henry10101001 R2, Coq-BB5 NGram/RepWL,
@Halldon orient.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  ∀ (M : Machine (Fin 2) (Fin 4)),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
    (∀ q a, ∃ q' z, M q a = some (some q', z)) →
    ¬ M.IsHalting

def H2 : Prop :=
  ∀ M : Machine (Fin 2) (Fin 4),
    M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
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
theorem freeze_bound (residual : H2)
    (M : Machine (Fin 2) (Fin 4))
    (first : M 0 0 = some (some 1, Stmt.write 0 Dir.right)) (halts : M.IsHalting) :
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
  apply (residual P ?_ ?_ ?_ ?_ ?_ ?_) haltP
  · have h : seen 0 0 := ⟨0, by decide, Tape.mk₁ [], rfl, rfl⟩
    simpa [P, h] using first
  · obtain ⟨q, t, ht⟩ := Machine.exists_of_not_haltsAfter M (Machine.init []) 107 late
    exact ⟨q, t, (agree 107 (by decide)).trans ht⟩
  · intro q a
    have eq : (∃ i < 107, ∃ t : Tape (Fin 2), P.multiStep start i = some ⟨some q, t⟩ ∧ t.head = a) ↔
        seen q a := by
      constructor <;> rintro ⟨i, hi, t, ht, ha⟩ <;> refine ⟨i, hi, t, ?_, ha⟩
      · exact (agree i (by omega)).symm.trans ht
      · exact (agree i (by omega)).trans ht
    apply eq.trans
    by_cases h : seen q a
    · simpa [P, h] using used h
    · simp [P, h]
  · intro q a
    by_cases h : seen q a
    · right
      simpa [P, h] using used h
    · left
      simp [P, h]
  · by_contra! all
    apply Machine.not_isHalting_of_forall_isSome P _ haltP
    intro q a
    by_cases h : seen q a
    · simpa [P, h] using used h
    · exact (all q a (by simp [P, h])).elim
  · intro i p q a side near fixed hp _ cfg enter loop
    exact no_repeat haltP hp cfg enter loop

theorem main : H1 → H2 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H3 := by
  intro hTotal hResidual M hFirst noEarly _noCyc hHalts
  by_cases hTot : ∀ q a, ∃ q' z, M q a = some (some q', z)
  · exact hTotal M hFirst hTot hHalts
  · have early := freeze_bound hResidual M hFirst hHalts
    exact noEarly 107 (by decide) early

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1
