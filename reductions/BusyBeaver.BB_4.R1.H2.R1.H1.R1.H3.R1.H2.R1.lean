import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1

/-!
Split the write-0 residual by the blank transition out of state 1
(same case split as @hyprspacecoyote BusyBeaver.BB_4.R2.H2.R1, without RepWL specials).
State 3 is rewritten to 2 via the `2 ↔ 3` permutation.

Donors: @henry10101001 R2.H1, @hyprspacecoyote R2.H2.R1.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1

open Turing Turing.BusyBeaver

def H1 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M 0 0 = some (some 1, Stmt.write 0 Dir.right) →
  (∃ q' : Fin 4, (q' = 0 ∨ q' = 1) ∧ ∃ z, M 1 0 = some (some q', z)) →
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
  (∃ d : Dir, M 1 0 = some (some 2, Stmt.write 0 d)) →
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
  M 1 0 = some (some 2, Stmt.write 1 Dir.right) →
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
  M 1 0 = some (some 2, Stmt.write 1 Dir.left) →
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

theorem main : H1 → H2 → H3 → H4 → OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1.H2 := by
  intro h1 h2 h3 h4 M hFirst hRun hUsed hForm hMissing hLoop hHalts
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
  have hrun1 : ∃ t, M.multiStep (Machine.init []) 1 = some ⟨some 1, t⟩ ∧ t.head = 0 := by
    have hs : M.step (Machine.init []) =
        some ⟨some 1, (Tape.mk₁ (Γ := Fin 2) []).write 0 |>.move Dir.right⟩ := by
      have hhd : (Tape.mk₁ (Γ := Fin 2) []).head = 0 := rfl
      simp [Machine.step, Machine.init, hhd, hFirst]
    refine ⟨(Tape.mk₁ (Γ := Fin 2) []).write 0 |>.move Dir.right, ?_, ?_⟩
    · rwa [Machine.multiStep_one]
    · simp [Tape.write, Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk']
  have hM10 : ∃ q' z, M 1 0 = some (some q', z) := by
    rcases hForm 1 0 with hnone | hsome
    · obtain ⟨t, ht, hhd⟩ := hrun1
      have h2s : M.multiStep (Machine.init []) 2 = none := by
        rw [Machine.multiStep_succ, ht]
        simp [Machine.step, hhd, hnone]
      have h107 := Machine.multiStep_eq_none_mono h2s (by decide : 2 ≤ 107)
      obtain ⟨q0, t0, hr⟩ := hRun; rw [h107] at hr; contradiction
    · exact hsome
  obtain ⟨q', ⟨w0, d0⟩, hM10⟩ := hM10
  fin_cases q'
  · exact h1 M hFirst ⟨0, Or.inl rfl, _, hM10⟩ hRun hUsed hForm hMissing hLoop hHalts
  · exact h1 M hFirst ⟨1, Or.inr rfl, _, hM10⟩ hRun hUsed hForm hMissing hLoop hHalts
  · fin_cases w0
    · exact h2 M hFirst ⟨d0, hM10⟩ hRun hUsed hForm hMissing hLoop hHalts
    · cases d0 with
      | right => exact h3 M hFirst hM10 hRun hUsed hForm hMissing hLoop hHalts
      | left => exact h4 M hFirst hM10 hRun hUsed hForm hMissing hLoop hHalts
  · let M' := reindex23 M
    have hFirst' : M' 0 0 = some (some 1, Stmt.write 0 Dir.right) := by
      simp [M', reindex23, hswap0, hFirst, hswap1]
    have hM10' : M' 1 0 = some (some 2, Stmt.write w0 d0) := by
      simp [M', reindex23, hswap1, hM10, hswap3]
    have hRun' : ∃ q t, M'.multiStep (Machine.init []) 107 = some ⟨some q, t⟩ := by
      obtain ⟨q0, t0, hr⟩ := hRun
      refine ⟨swap23 q0, t0, ?_⟩; rw [← mapCfg23_init, reindex23_multi, hr]; rfl
    have hUsed' : ∀ q a, (∃ i < 107, ∃ t : Tape (Fin 2),
        M'.multiStep (Machine.init []) i = some ⟨some q, t⟩ ∧ t.head = a) ↔
        ∃ q' z, M' q a = some (some q', z) := by
      intro q a; constructor
      · rintro ⟨i, hi, t, ht, rfl⟩
        rw [← mapCfg23_init, reindex23_multi] at ht
        cases hMi : M.multiStep (Machine.init []) i with
        | none => simp [hMi] at ht
        | some c' =>
          simp only [hMi, Option.map_some, Option.some.injEq] at ht
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23] at ht
          | some q0 =>
            simp only [mapCfg23, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht
            rcases ht with ⟨hq0, rfl⟩
            have hq0' : q0 = swap23 q := by rw [← hq0, hswap_inv]
            subst hq0'
            obtain ⟨r, z, hrz⟩ := (hUsed (swap23 q) t0.head).mp ⟨i, hi, t0, hMi, rfl⟩
            exact ⟨swap23 r, z, by simp [M', reindex23, hrz]⟩
      · rintro ⟨r, z, hrz⟩
        simp only [M', reindex23] at hrz
        cases hMqa : M (swap23 q) a with
        | none => simp [hMqa] at hrz
        | some entry =>
          rcases entry with ⟨s, z0⟩
          cases s with
          | none => simp [hMqa] at hrz
          | some s =>
            obtain ⟨i, hi, t, ht, ha⟩ := (hUsed (swap23 q) a).mpr ⟨s, z0, hMqa⟩
            refine ⟨i, hi, t, ?_, ha⟩
            rw [← mapCfg23_init, reindex23_multi, ht]; simp [mapCfg23, hswap_inv]
    have hForm' : ∀ q a, M' q a = none ∨ ∃ q' z, M' q a = some (some q', z) := by
      intro q a
      rcases hForm (swap23 q) a with h | ⟨r, z, h⟩
      · left; simp [M', reindex23, h]
      · right; exact ⟨swap23 r, z, by simp [M', reindex23, h]⟩
    have hMissing' : ∃ q a, M' q a = none := by
      obtain ⟨qm, am, hm⟩ := hMissing
      exact ⟨swap23 qm, am, by simp [M', reindex23, hswap_inv, hm]⟩
    have hLoop' : ∀ (i p : ℕ) (q : Fin 4) (a : Fin 2) (side : Bool)
        (near : List (Fin 2)) (fixed : ListBlank (Fin 2)), 0 < p → i + p ≤ 107 →
      let cfg := fun tail : ListBlank (Fin 2) =>
        let free := near.foldr ListBlank.cons tail
        (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg (Fin 2) (Fin 4))
      (∃ tail, M'.multiStep (Machine.init []) i = some (cfg tail)) →
      ¬ ∀ tail, ∃ tail', M'.multiStep (cfg tail) p = some (cfg tail') := by
      intro i p q a side near fixed hp hle cfg hEnter hCycle
      let cfgM : ListBlank (Fin 2) → Cfg (Fin 2) (Fin 4) := fun tail =>
        let free := near.foldr ListBlank.cons tail
        ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
      have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
        intro tail; simp [mapCfg23, cfgM, cfg, hswap_inv]
      apply hLoop i p (swap23 q) a side near fixed hp hle
      · obtain ⟨tail, ht⟩ := hEnter
        rw [← mapCfg23_init, reindex23_multi] at ht
        cases hMi : M.multiStep (Machine.init []) i with
        | none => simp [hMi] at ht
        | some c' =>
          simp only [hMi, Option.map_some, Option.some.injEq] at ht
          refine ⟨tail, ?_⟩; congr 1
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23, cfg] at ht
          | some q0 =>
            simp only [mapCfg23, cfg, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht
            rcases ht with ⟨hq0, ht0⟩
            have : q0 = swap23 q := by rw [← hq0, hswap_inv]
            simp [this, ht0]
      · intro tail
        obtain ⟨tail', ht'⟩ := hCycle tail
        rw [← hmap tail, reindex23_multi] at ht'
        cases hMp : M.multiStep (cfgM tail) p with
        | none => simp [hMp] at ht'
        | some c' =>
          simp only [hMp, Option.map_some, Option.some.injEq] at ht'
          refine ⟨tail', ?_⟩; congr 1
          obtain ⟨q0, t0⟩ := c'
          cases q0 with
          | none => simp [mapCfg23, cfg] at ht'
          | some q0 =>
            simp only [mapCfg23, cfg, Option.map_some, Cfg.mk.injEq, Option.some.injEq] at ht'
            rcases ht' with ⟨hq0, ht0⟩
            have : q0 = swap23 q := by rw [← hq0, hswap_inv]
            simp [this, ht0]
    have hHalts' : M'.IsHalting := reindex23_isHalting M hHalts
    fin_cases w0
    · exact h2 M' hFirst' ⟨d0, hM10'⟩ hRun' hUsed' hForm' hMissing' hLoop' hHalts'
    · cases d0 with
      | right => exact h3 M' hFirst' hM10' hRun' hUsed' hForm' hMissing' hLoop' hHalts'
      | left => exact h4 M' hFirst' hM10' hRun' hUsed' hForm' hMissing' hLoop' hHalts'

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1
