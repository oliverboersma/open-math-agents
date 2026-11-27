import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1

/-!
Length-2 H2 residual H2 (M 2 0 = write-1-left into state 1): FAR certificates from
@hyprspacecoyote `BusyBeaver.BB_4.R2.H2.R1.H2` (`tv_b8`).
-/
-- Credit: @pageman (adaptation); certificates from @hyprspacecoyote
namespace OMA.BB4H2

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev State := Fin 4
abbrev Key := State × Symbol
abbrev Machine4 := Machine Symbol State

structure Move where
  state : State
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Table where
  t00 : Option Move
  t01 : Option Move
  t10 : Option Move
  t11 : Option Move
  t20 : Option Move
  t21 : Option Move
  t30 : Option Move
  t31 : Option Move
  deriving DecidableEq

def Table.empty : Table := ⟨none, none, none, none, none, none, none, none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val, a.val with
  | 0, 0 => tb.t00
  | 0, _ => tb.t01
  | 1, 0 => tb.t10
  | 1, _ => tb.t11
  | 2, 0 => tb.t20
  | 2, _ => tb.t21
  | _, 0 => tb.t30
  | _, _ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val, a.val with
  | 0, 0 => { tb with t00 := some m }
  | 0, _ => { tb with t01 := some m }
  | 1, 0 => { tb with t10 := some m }
  | 1, _ => { tb with t11 := some m }
  | 2, 0 => { tb with t20 := some m }
  | 2, _ => { tb with t21 := some m }
  | _, 0 => { tb with t30 := some m }
  | _, _ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip, tb.t01.map Move.flip,
   tb.t10.map Move.flip, tb.t11.map Move.flip,
   tb.t20.map Move.flip, tb.t21.map Move.flip,
   tb.t30.map Move.flip, tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q', a') ≠ (q, a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
  fin_cases q <;> fin_cases a <;> fin_cases q' <;> fin_cases a' <;>
    first | rfl | exact absurd rfl h

theorem Table.get_flip (tb : Table) (q : State) (a : Symbol) :
    tb.flip.get q a = (tb.get q a).map Move.flip := by
  fin_cases q <;> fin_cases a <;> rfl

structure Position where
  state : State
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def startPos : Position := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val, xs with
  | 0, [] => []
  | _, xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _, _ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq, Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1), ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state, c.ls.tail, symHead c.ls, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, symHead c.rs, c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state, c.rs, c.head, c.ls⟩

theorem flip_move (c : Position) (m : Move) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with | mk q a d => cases d <;> rfl

theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  fin_cases a
  · cases xs with
    | nil => exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
    | cons x xs => exact (ListBlank.cons_mk 0 (x :: xs)).symm
  · exact (ListBlank.cons_mk 1 xs).symm

def Position.view (c : Position) : Cfg Symbol State :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m, tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    rw [Table.get_set_self] at hh
    exact (Option.some.inj hh) ▸ h
  · rw [Table.get_set_ne tb m e] at hh
    exact hm q' a' m' hh

theorem step_move {M : Machine4} {tb : Table} (hm : Matches M tb) (c : Position) (m : Move)
    (h : tb.get c.state c.head = some m) :
    M.step c.view = some (c.move m).view := by
  have he := hm c.state c.head m h
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push, symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0, _ => []
  | k + 1, [] => 0 :: takePad k []
  | k + 1, x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad, List.foldr_cons, List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad, List.foldr_cons, List.drop_succ_cons]
      rw [ih xs, ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0, q, a, near, rs => some (q, a, near, rs)
  | k + 1, q, a, near, rs =>
    match tb.get q a with
    | none => none
    | some m =>
      if m.left then
        match near with
        | [] => none
        | a' :: near' => runGuardedLeft tb k m.state a' near' (push m.write rs)
      else
        runGuardedLeft tb k m.state (symHead rs) (m.write :: near) rs.tail

def checkGuardedLeft (tb : Table) (p : ℕ) (q : State) (a : Symbol)
    (near rs : List Symbol) : Bool :=
  match runGuardedLeft tb p q a near rs with
  | none => false
  | some (q', a', near', rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q', a', near', rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q', ⟨a', near'.foldr ListBlank.cons tail, ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | true =>
        simp only [hd, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, (x :: xs).foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
              some ⟨some m.state, ⟨x, xs.foldr ListBlank.cons tail, ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ =
            some ⟨some m.state, ⟨symHead rs, (m.write :: near).foldr ListBlank.cons tail, ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q', a', near', ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q', ⟨a', ListBlank.mk ls', near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht, Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip, hd, Bool.not_false, ↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, (x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state, ⟨x, ListBlank.mk (push m.write ls), xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, mk_push]
          rw [hstep, Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip, hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        have hstep : M.step ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state, ⟨symHead ls, ListBlank.mk ls.tail, (m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step, hM, Move.command, hd, Tape.write, Tape.move, symHead_eq_headI]
        rw [hstep, Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, near.foldr ListBlank.cons tail, ListBlank.mk rs⟩⟩ p =
      some ⟨some q, ⟨a, near.foldr ListBlank.cons tail', ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', rs'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hrs⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail', M.multiStep ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q, ⟨a, ListBlank.mk ls, near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q', a', near', ls'⟩
    simp only [hr, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hls⟩, htake⟩, _⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail, ?_⟩
    rw [runGuardedRight_sound hm p q' a' near ls' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

structure HistItem where
  step : ℕ
  pos : ℕ
  c : Position

def findRepAux (tb : Table) (cur : HistItem) (minp maxp : ℕ) : List HistItem → Bool
  | [] => false
  | hi :: rest =>
    let minp' := if Nat.ble minp hi.pos then minp else hi.pos
    let maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    let ok :=
      if Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val then
        let p := cur.step - hi.step
        let leftOk :=
          if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
            let dL := hi.pos - minp'
            let near := takePad dL hi.c.ls
            if listEq (takePad dL cur.c.ls) near then
              checkGuardedLeft tb p hi.c.state hi.c.head near hi.c.rs
            else false
          else false
        if leftOk then true
        else if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
          let dR := maxp' - hi.pos
          let near := takePad dR hi.c.rs
          if listEq (takePad dR cur.c.rs) near then
            checkGuardedLeft tb.flip p hi.c.state hi.c.head near hi.c.ls
          else false
        else false
      else false
    if ok then true else findRepAux tb cur minp' maxp' rest

def findRep (tb : Table) (cur : HistItem) (prev : List HistItem) : Bool :=
  findRepAux tb cur 1000 0 prev

def HistValid (M : Machine4) (hist : List HistItem) : Prop :=
  ∀ h ∈ hist, h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol), 0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q, if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩ : Cfg Symbol State)
    (∃ tail, M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail, ∃ tail', M.multiStep (cfg tail) p = some (cfg tail')

theorem findRepAux_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem}
    (hcur : cur.step ≤ 107) (hvalid : HistValid M prev)
    {minp maxp : ℕ} (h : findRepAux tb cur minp maxp prev = true) : False := by
  induction prev generalizing minp maxp with
  | nil => simp [findRepAux] at h
  | cons hi rest ih =>
    unfold findRepAux at h
    dsimp only at h
    set minp' := if Nat.ble minp hi.pos then minp else hi.pos
    set maxp' := if Nat.ble maxp hi.pos then hi.pos else maxp
    by_cases hcond : (Nat.ble (hi.step + 1) cur.step && Nat.beq hi.c.state.val cur.c.state.val && Nat.beq hi.c.head.val cur.c.head.val) = true
    · simp only [hcond, ↓reduceIte] at h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq_true_eq] at hcond
      have ⟨hstep_hi, hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
      have hp_pos : 0 < cur.step - hi.step := by omega
      have hp_le : hi.step + (cur.step - hi.step) ≤ 107 := by omega
      by_cases hleft : (if Nat.ble hi.pos cur.pos && listEq hi.c.rs cur.c.rs then
          if listEq (takePad (hi.pos - minp') cur.c.ls) (takePad (hi.pos - minp') hi.c.ls) then
            checkGuardedLeft tb (cur.step - hi.step) hi.c.state hi.c.head (takePad (hi.pos - minp') hi.c.ls) hi.c.rs
          else false else false) = true
      · split at hleft
        · split at hleft
          · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head true
              (takePad (hi.pos - minp') hi.c.ls) (ListBlank.mk hi.c.rs)
              hp_pos hp_le
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')), by
                simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)), by
                  simpa [Position.view, takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright, Bool.false_eq_true, ↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
      exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h

-- ============================================================
-- FAR (Finite Automata Reduction) certificate verifier
-- ============================================================

inductive CanStop (tb : Table) : Position → Prop
  | missing {c} : tb.get c.state c.head = none → CanStop tb c
  | move {c m} : tb.get c.state c.head = some m → CanStop tb (c.move m) → CanStop tb c

theorem canStop_flip {tb : Table} {c : Position} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip, h]
    · rwa [← flip_move]

theorem cannot_stop_run {M : Machine4} {tb : Table}
    (hm : Matches M tb) (c : Position) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get c.state c.head with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move hm c m h, Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  fin_cases a
  · cases xs with
    | nil => exact D.blank.symm
    | cons x xs => rfl
  · rfl

theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

structure Certificate where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate) := Option (State × Fin cert.dfa.size)

def nodeId (cert : Certificate) : Node cert → ℕ
  | none => 4 * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edgeRow (cert : Certificate) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (4 * cert.dfa.size)
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) &&&
      ((1 <<< (4 * cert.dfa.size + 1)) - 1)

def Certificate.edge (cert : Certificate) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  (cert.edgeRow p a).testBit (nodeId cert q)

theorem edge_none (cert : Certificate) (a : Symbol) (q : Node cert) :
    cert.edge none a q = q.isNone := by
  unfold Certificate.edge Certificate.edgeRow
  simp only [Nat.testBit_two_pow]
  rcases q with _ | ⟨q, l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId, hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := (val >>> 1) &&& 31
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := (val >>> 6) / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val.testBit 0, ⟨extra, (val >>> 6) % dfaBase⟩, payload >>> width, payload &&& (initialBase - 1)⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

-- A single inclusion check verifies every target in an automaton edge row.
theorem included_bit {x y : ℕ} (h : Nat.beq (x &&& y) x = true) (k : ℕ)
    (bit : x.testBit k = true) : y.testBit k = true := by
  have e := congrArg (fun n : ℕ => n.testBit k) (Nat.eq_of_beq_eq_true h)
  simpa [Nat.testBit_and, bit] using e

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        Nat.beq (row &&& cert.blankReach) row
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state, l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              Nat.beq (swRow &&& pRow) swRow
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state, cert.dfa.next m.write l)))

def checkMachine (tb : Table) (cert : Certificate) : Bool :=
  (List.finRange 4).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

theorem Reads.push {cert : Certificate} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, by simp [edge_none], .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0, 0)) (ListBlank.mk []) := by
  simp only [checkBlank, Bool.and_eq_true_iff, Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart, hsink⟩, hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp, if_true] at ht
      exact ih rfl (included_bit ht (nodeId cert q) he)
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    exact Reads.push (show cert.edge (some (c.state, cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd, Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, symHead_eq_headI, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push, symHead_eq_headI] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq, if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state, cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he', if_true] at h''
      exact Reads.push (included_bit h'' (nodeId cert t) hf) ht

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := unpack val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, startPos, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

-- ============================================================
-- Symmetry: swapping states 2 and 3
-- ============================================================

def swap23 : Equiv.Perm State := Equiv.swap (2 : State) (3 : State)

theorem swap23_0 : swap23 0 = 0 := by decide
theorem swap23_1 : swap23 1 = 1 := by decide
theorem swap23_2 : swap23 2 = 3 := by decide
theorem swap23_3 : swap23 3 = 2 := by decide
theorem swap23_inv (q : State) : swap23.symm q = swap23 q := by fin_cases q <;> decide

def reindex23 (M : Machine4) : Machine4 :=
  fun q a => (M (swap23 q) a).map fun (s, b) => (s.map swap23, b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23, c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q, t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step, mapCfg23, Option.map_some, reindex23]
    have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
    rw [hinv]
    cases M q t.head with
    | none => rfl
    | some entry => rfl

theorem reindex23_multi (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    (reindex23 M).multiStep (mapCfg23 c) k = (M.multiStep c k).map mapCfg23 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, Machine.multiStep_succ, ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23, Machine.init, swap23_0]


def sp0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩,
   some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩⟩

def sp1Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩,
   none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, some ⟨3, 1, true⟩⟩

def m0Table : Table :=
  ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩,
   some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, none⟩

def tblOfList (entries : List ℕ) : Machine4 := fun q a =>
  let v := entries[2*q.val+a.val]?.getD 16
  if v = 16 then none else some (some ⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩,
    Stmt.write ⟨v / 2 % 2, Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))

theorem eq_sp0_of_matches {M : Machine4} (hm : Matches M sp0Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,3,3,8,15,10,16,1] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 3 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 0 = none at hMmiss; rw [hm 2 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hm 2 0 _ rfl
  · exact hm 2 1 _ rfl
  · exact hMmiss
  · exact hm 3 1 _ rfl

theorem eq_sp1_of_matches {M : Machine4} (hm : Matches M sp1Table) (hMiss : ∃ q a, M q a = none) :
    M = tblOfList [6,4,11,6,16,13,2,15] := by
  obtain ⟨qm, am, hMmiss⟩ := hMiss
  have hqm : qm = 2 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl, rfl⟩
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 0 = none at hMmiss; rw [hm 3 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl, rfl⟩
  funext q a
  fin_cases q <;> fin_cases a
  · exact hm 0 0 _ rfl
  · exact hm 0 1 _ rfl
  · exact hm 1 0 _ rfl
  · exact hm 1 1 _ rfl
  · exact hMmiss
  · exact hm 2 1 _ rfl
  · exact hm 3 0 _ rfl
  · exact hm 3 1 _ rfl

def runPos (tb : Table) : ℕ → Position → Option Position
  | 0, c => some c
  | k + 1, c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front, step_move hm c m ht, Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Machine.multiStep_succ, ih]
    cases M.multiStep x m <;> simp

theorem m0_not_halting {M : Machine4} (hm : Matches M m0Table) (hHalts : M.IsHalting) : False := by
  have h85 : ∃ c85, runPos m0Table 85 startPos = some c85 ∧
      checkGuardedLeft m0Table.flip 29 c85.state c85.head [] c85.ls = true := by
    refine ⟨(runPos m0Table 85 startPos).getD startPos, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨c85, hrun, hcyc⟩ := h85
  have hM85 : M.multiStep (Machine.init []) 85 = some c85.view := runPos_sound hm 85 startPos hrun
  let cfg (tail : ListBlank Symbol) : Cfg Symbol State :=
    ⟨some c85.state, ⟨c85.head, ListBlank.mk c85.ls, tail⟩⟩
  have hEnter : ∃ tail, M.multiStep (Machine.init []) 85 = some (cfg tail) :=
    ⟨ListBlank.mk c85.rs, hM85⟩
  have hStep : ∀ tail, ∃ tail', M.multiStep (cfg tail) 29 = some (cfg tail') := by
    intro tail
    simpa [cfg] using checkGuardedRight_sound hm hcyc tail
  have hRec (m : ℕ) : ∃ tail, M.multiStep (Machine.init []) (85 + 29 * m) = some (cfg tail) := by
    induction m with
    | zero => simpa using hEnter
    | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht'⟩ := hStep t
      refine ⟨t', ?_⟩
      rw [Nat.mul_succ, ← Nat.add_assoc, run_add M _ (85 + 29 * m) 29, ht]
      exact ht'
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
  obtain ⟨t, ht⟩ := hRec (k + 1)
  have hnone := Machine.multiStep_eq_none_mono hk (by omega : k + 1 ≤ 85 + 29 * (k + 1))
  rw [ht] at hnone
  contradiction

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting ∧
  (M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1]) ∧
  (M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15])

theorem reindex23_invol (M : Machine4) : reindex23 (reindex23 M) = M := by
  funext q a
  have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
  simp only [reindex23, hinv]
  cases M q a with
  | none => rfl
  | some p =>
    rcases p with ⟨s, b⟩
    cases s with
    | none => rfl
    | some s =>
      have hs : swap23 (swap23 s) = s := by fin_cases s <;> decide
      simp [hs]

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts, ⟨hsp0, hsp0'⟩, ⟨hsp1, hsp1'⟩⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨hsp0', by rwa [reindex23_invol]⟩, ⟨hsp1', by rwa [reindex23_invol]⟩⟩
  · refine ⟨swap23 q0, t0, ?_⟩
    rw [← mapCfg23_init, reindex23_multi, hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q', z, h⟩
    · left; simp [reindex23, h]
    · right; exact ⟨swap23 q', z, by simp [reindex23, h]⟩
  · exact ⟨swap23 qm, am, by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23, this, hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q), if side then ⟨a, free, fixed⟩ else ⟨a, fixed, free⟩⟩
    have hmap : ∀ tail, mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23, cfgM, cfg, this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail, ht⟩ := hEnter
      rw [← mapCfg23_init, reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi, Option.map_some, Option.some.injEq] at ht
        refine ⟨tail, ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht
        rcases ht with ⟨hq', ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht']
    · intro tail
      obtain ⟨tail', ht'⟩ := hCycle tail
      rw [← hmap tail, reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp, Option.map_some, Option.some.injEq] at ht'
        refine ⟨tail', ?_⟩
        congr 1
        obtain ⟨q', t'⟩ := c'
        simp only [mapCfg23, cfg, Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq', ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some, Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this, ht'']
  · obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k, ?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init, reindex23_multi, hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m, tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get, h01.1, h01.2.1] at hget
    · fin_cases a <;> simp [Table.get, h01.2.2.1, h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23, hsq, hm q a m hget, Move.command, Option.map_some, hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist, h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle, hrun⟩ := hv h hh
  refine ⟨hle, ?_⟩
  rw [← mapCfg23_init, reindex23_multi, hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23, Position.view, hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q, a) := by
  ext ⟨q', a'⟩
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases e : (q', a') = (q, a)
  · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e, e]

def moves12 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩]

def moves16 : List Move :=
  [⟨0, 0, false⟩, ⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 1, true⟩,
   ⟨1, 0, false⟩, ⟨1, 0, true⟩, ⟨1, 1, false⟩, ⟨1, 1, true⟩,
   ⟨2, 0, false⟩, ⟨2, 0, true⟩, ⟨2, 1, false⟩, ⟨2, 1, true⟩,
   ⟨3, 0, false⟩, ⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 1, true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q, a, d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed, moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed, moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [], certs => some certs
  | m :: ms, certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | holesLeft + 1, used2, tb, rem, cur, prev, certs =>
    match stepLoop tb rem cur prev with
    | .rep => some certs
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some rest else none
        else if checkCertificate tb v then some rest else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some certs
      else
        checkMoves (fun m rest =>
          checkTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) certs

theorem checkMoves_each {f : Move → List ℕ → Option (List ℕ)} {ms : List Move}
    {a b : List ℕ} (h : checkMoves f ms a = some b) {m : Move} (hm : m ∈ ms) :
    ∃ x y, f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a, mid, hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : ((Nat.beq (cur.step + 1) 6 || Nat.beq (cur.step + 1) 12 || Nat.beq (cur.step + 1) 24 ||
          Nat.beq (cur.step + 1) 48 || Nat.beq (cur.step + 1) 107) && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01

theorem usesOnly01_set {tb : Table} (h01 : UsesOnly01 tb) {q : State} {a : Symbol} {m : Move}
    (hq : q = 0 ∨ q = 1) (hm : m.state = 0 ∨ m.state = 1) :
    UsesOnly01 (tb.set q a m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q', a') = (q, a)
    · rcases Prod.mk.inj e with ⟨rfl, rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [checkTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    unfold checkTree at hCheck
    have hstep := stepLoop_sound hm hG hsum hv hu
    cases hsl : stepLoop tb rem cur prev with
    | rep => rw [hsl] at hstep; exact hstep
    | done =>
      simp only [hsl] at hCheck
      cases a with
      | nil => simp at hCheck
      | cons v rest =>
        simp only at hCheck
        by_cases hv0 : Nat.beq v 0 = true
        · simp only [hv0, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hsp
            simp only [Bool.or_eq_true, beq_iff_eq] at hsp
            rcases hsp with (rfl | rfl) | rfl
            · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
            · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
            · exact m0_not_halting hm hG.2.2.2.2.1
          · simp at hCheck
        · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hCheck
          split at hCheck
          · rename_i hcert
            have hns := certificate_sound hcert
            obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
            exact cannot_stop_run hm startPos hns (k + 1) hk
          · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z, M q a = some (some q', z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ, hcur'_run]
            simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0, t0, hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
        obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm, am) ∈ holes tb := by
          simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm, am) = (q, a) := by
          have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq, Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m, Move.command] using hMqa
        have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set, Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2, rfl⟩
          have ⟨h01, hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
          obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01, hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def limitedStep (stop : ℕ) (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0, _, _ => .done
  | rem + 1, cur, prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep, npos, nc⟩
      let nprev := cur :: prev
      if Nat.beq nstep stop &&
          findRep tb ncur nprev then
        .rep
      else
        limitedStep stop tb rem ncur nprev

theorem limitedStep_sound (stop : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match limitedStep stop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [limitedStep]
  | succ rem ih =>
    unfold limitedStep
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht, rfl, rfl, hsum, Nat.succ_pos _, hv, h01⟩
    | some m =>
      simp only [ht]
      have ⟨hcur_le, hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1, if m.left then cur.pos - 1 else cur.pos + 1, cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ, hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega, hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev, h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u, hprev01⟩ := h01 hu
        refine ⟨u, fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur, Position.move, hd] using hms
        · exact hprev01 h hh'
      by_cases hrep : (Nat.beq (cur.step + 1) stop && findRep tb ncur (cur :: prev)) = true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01


def stopAt (tag : ℕ) : ℕ :=
  match tag with
  | 1 => 6 | 2 => 12 | 3 => 24 | 4 => 48 | 5 => 107 | _ => 0

def advisedStep (tag : ℕ) (tb : Table) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : StepResult :=
  if Nat.beq tag 6 then .done else limitedStep (stopAt tag) tb rem cur prev

theorem advisedStep_sound (tag : ℕ) {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) :
    match advisedStep tag tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev', h.c.state = 0 ∨ h.c.state = 1) := by
  by_cases h : Nat.beq tag 6 = true
  · simp [advisedStep, h]
  · simpa only [advisedStep, if_neg h] using limitedStep_sound (stopAt tag) hm hG hsum hv h01

def guidedTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [] => none
  | holesLeft + 1, used2, tb, rem, cur, prev, code :: certs =>
    match advisedStep (code % 8) tb rem cur prev with
    | .rep => some ((code >>> 3) :: certs)
    | .done =>
      match certs with
      | [] => none
      | v :: rest =>
        if Nat.beq v 0 then
          if tb == sp0Table || tb == sp1Table || tb == m0Table then some ((code >>> 3) :: rest) else none
        else if checkCertificate tb v then some ((code >>> 3) :: rest) else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some ((code >>> 3) :: certs)
      else
        checkMoves (fun m rest =>
          guidedTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) ((code >>> 3) :: certs)

theorem guidedTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : guidedTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4, GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
      False := by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero => simp [guidedTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    cases a with
    | nil => simp [guidedTree] at hCheck
    | cons code a =>
      unfold guidedTree at hCheck
      have hstep := advisedStep_sound (code % 8) hm hG hsum hv hu
      cases hsl : advisedStep (code % 8) tb rem cur prev with
      | rep => rw [hsl] at hstep; exact hstep
      | done =>
        simp only [hsl] at hCheck
        cases a with
        | nil => simp at hCheck
        | cons v rest =>
          simp only at hCheck
          by_cases hv0 : Nat.beq v 0 = true
          · simp only [hv0, ↓reduceIte] at hCheck
            split at hCheck
            · rename_i hsp
              simp only [Bool.or_eq_true, beq_iff_eq] at hsp
              rcases hsp with (rfl | rfl) | rfl
              · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
              · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
              · exact m0_not_halting hm hG.2.2.2.2.1
            · simp at hCheck
          · simp only [hv0, Bool.false_eq_true, ↓reduceIte] at hCheck
            split at hCheck
            · rename_i hcert
              have hns := certificate_sound hcert
              obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
              exact cannot_stop_run hm startPos hns (k + 1) hk
            · simp at hCheck
      | missing q a rem' cur' prev' =>
        simp only [hsl] at hCheck hstep
        obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
        have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
        -- M must define (q, a) as some (some q', z) since cur'.step < 107 and M runs past 107
        have hM_def : ∃ q' z, M q a = some (some q', z) := by
          rcases hG.2.1 q a with hMnone | hMsome
          · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
              rw [Machine.multiStep_succ, hcur'_run]
              simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
            have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
            obtain ⟨q0, t0, hrun107⟩ := hG.1
            rw [h107] at hrun107
            contradiction
          · exact hMsome
        obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
        split at hCheck
        · -- holesLeft == 0: (holes tb).card ≤ 1 and (q, a) ∈ holes tb, so M has no none!
          rename_i h0
          have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
          have hmem : (q, a) ∈ holes tb := by simp [holes, hnone]
          have hcard1 : (holes tb).card = 1 :=
            le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hmem⟩)
          obtain ⟨qm, am, hMmiss⟩ := hG.2.2.1
          have hqm_mem : (qm, am) ∈ holes tb := by
            simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and]
            cases hget : tb.get qm am with
            | none => rfl
            | some m =>
              have := hm qm am m hget
              rw [hMmiss] at this
              simp [Move.command] at this
          have heq_key : (qm, am) = (q, a) := by
            have hsub : ({(q, a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
            have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
            rw [← hEq, Finset.mem_singleton] at hqm_mem
            exact hqm_mem
          rcases Prod.mk.inj heq_key with ⟨rfl, rfl⟩
          rw [hMmiss] at hMqa
          contradiction
        · -- Branch on movesAllowed used2
          let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
          have hm_cmd : M q a = m.command := by
            cases d <;> simpa [m, Move.command] using hMqa
          have hmem_hole : (q, a) ∈ holes tb := by simp [holes, hnone]
          have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
            rw [holes_set, Finset.card_erase_of_mem hmem_hole]
            omega
          by_cases hswap : used2 = false ∧ q' = 3
          · rcases hswap with ⟨hu2, rfl⟩
            have ⟨h01, hprev01⟩ := hu' hu2
            let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
            have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
            obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m2
            have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
            have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
            have hM2qa : (reindex23 M) q a = m2.command := by
              cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
            have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
              rw [holes_set, Finset.card_erase_of_mem hmem_hole]
              omega
            exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
              (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
              (histValid_reindex23 hv' hprev01) (by simp [m2])
          · have hmem_m : m ∈ movesAllowed used2 :=
              mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
            obtain ⟨x, y, hxy⟩ := checkMoves_each hCheck hmem_m
            refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
            intro hnext_u2
            simp only [Bool.or_eq_false_iff] at hnext_u2
            have ⟨h01, hprev01⟩ := hu' hnext_u2.1
            have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
            have hm01 : m.state = 0 ∨ m.state = 1 := by
              have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
              have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
              fin_cases q' <;> simp_all [m]
            exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4, GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev, h.c.state = 0 ∨ h.c.state = 1) →
    False

theorem branch_one {tb : Table} {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    {q : State} {a : Symbol} {rem' : ℕ} {cur' : HistItem} {prev' : List HistItem}
    (hsl : stepLoop tb rem cur prev = .missing q a rem' cur' prev')
    (hChildren : ∀ m ∈ movesAllowed used2,
      TreeValid (tb.set q a m) (used2 || Nat.beq m.state.val 2) rem' cur' prev') :
    TreeValid tb used2 rem cur prev := by
  intro M hG hm hsum hv hu
  have hstep := stepLoop_sound hm hG hsum hv hu
  simp only [hsl] at hstep
  obtain ⟨hnone, hq_eq, ha_eq, hsum', hrem_pos, hv', hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z, M q a = some (some q', z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ, hcur'_run]
        simp [Machine.step, Position.view, hq_eq, ha_eq, hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0, t0, hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q', ⟨w, d⟩, hMqa⟩ := hM_def
  let m : Move := ⟨q', w, match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m, Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2, rfl⟩
    have ⟨h01, hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2, w, match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23, hsq, hm_cmd, m, m2, Move.command, swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2, h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01, hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1, h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01, hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1, 1, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 1, false⟩⟩

private theorem mk_good_ne_sp1 (M : Machine4) (h : M 1 0 ≠ some (some 2, Stmt.write 1 Dir.left))
    (h2 : M 1 0 ≠ some (some 3, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h2 ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,4,11,6,16,13,2,15] 1 0 = some (some 2, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs3 : s = 3 := by revert hs; fin_cases s <;> decide
      subst hs3; subst hz; rfl

private theorem mk_good_ne_sp0 (M : Machine4) (h : M 1 0 ≠ some (some 0, Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
  refine ⟨fun heq => h (by rw [heq]; rfl), fun heq => h ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,3,3,8,15,10,16,1] 1 0 = some (some 0, Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23, swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s, z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h10
      rcases h10 with ⟨hs, hz⟩
      have hs0 : s = 0 := by revert hs; fin_cases s <;> decide
      subst hs0; subst hz; rfl

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 1 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 1, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in

private theorem tv_b8_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24920804c241049208209b49209a4820030924124986026d24820920804da4104000824900820824820136904000000120024800006020104004d241009a4820db6c301b6d86124920804d241040000009208041249040269208049300009248209248208249248200061a4920b20134104124924020186924824826180036db6f309269a08209a4920920924820134904124800824d24824924904da69049249209b49208269a41368201049a6c06124c24926904da0904924d209b4d200000009001a4136db6d86db6d86db6db0db6db09249241369a41241249860261a08249269b09b6920986d860369a0c049049049249061b69b09b6920924800924924824924820820924c24d000040209349208209a4836924000134826d24824924924d000008009268201041241249240000208249a68041049249249069a69a4920820824934934020824924d24824926924da0904924d249b4920924924924080030d249b6d00820124db1120104d349a6f34020904d26db4836da49a6d028a288, 1133048953444545, 2923371238321452602275315851411786646617933755202, 2923371260099524085215377513067761522251099288386]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24920804d241049208269349209a6820030924124986026da4820920804da41048008008208008248201369040200201000240000000200040049241009a4820db6c301b6d86134986026920824920804d24104004100820800134d040269208049261809b68209241049249241249a6c26db4834d349049249008369a69a60008001a69a69a08249248268209a6924820924820030900124800026924826924904c208049241001848208269a40309241041a6c061248209a6900c24904104d20184920000000900120000000124124836db6d80c36d800000048009209a4924030924124d349201849201248000269a08249041349249049208209a6920d24d241249241a68001a6924924824924820820924da4d000040069a49308209a4836924000104026d208249a49251000008009a68201041241249240000208269a68041049249249069a49249208208249369340000249a6924c20826924da0904104d309b49209249269240001869a69a68041049049249008269a69a69a01041249249241a6924924830c30db6db6d80007866db6c60c30db6f38db60001b6c371bcc3cda4d2598292490, 1161368023863744, 1161368023863744, 2928712984119627669801440515032256664395222889282, 1133048953444545, 106105095590336, 317217971900864, 
    317217971900864]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨1, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24e34964940000936da6d2710c0240069a49a6000924d20004164947930db6c36db6db6106186d2716cc04926da49a6000924c3db26304134d86da6dc4c34d409b4db690490402c0203041b6104d26c00024d30936d861049b6d86db7000036db0db8d881808361849858308418009c8f34000186c06124c000319849ac1009b6d86d34c00024db61b6db61808041869269e6c24b36924124986d26d0602493032d18c104d361b6db4930924c36d36da4104100034820104924c36d36e241b6d86db6dc6c36db6c36db6e3612104014603c906db81b6db71b0000c36136f24020006c3d830c00000dbdb36f06000181800060c000671b79e7986e3db3d9b09a49a00079c49c4a00000146980804000186dc7124c000340048211059349c59219041b6d26d06800004906c2c1041069b6db4930000d00d000241249b6d6680, 1161155221459392, 324403033980877405537562920820621316828870797855852538913597458270697488587353581220035361868144324, 1161155285356737, 1161155221459392, 1161164080026048, 371085815678611994235083854345649049513899341634, 
    1161370171150784, 1161368023863744, 1161368023863744, 1161368023732672, 1161368023863744, 2928712984114310737555736974291338717328503239490, 
    316943093993920, 316943093993920, 316943093993920, 583925464646046210032418948265169619527655341046170694675523275017317690177621596081293357927638532, 8369598326593329836429484193452297382501830087944009089720128567922461699263514684307006723843958276, 105839008944576, 
    176209900605888, 316943093993920, 316943093993920, 4217239466888111472080243969461200383654574453816508273986178501851004512023759369613101997419931140, 33283751484824633568462844139029446496669927355979208908471420316520490663848708748493503179927856644, 17127037657320480964811417562565105392572970818, 
    28545062755111125892160670739186208216717473602, 1461551814188457737005823497529518369191583889218, 145275260768449, 145275260768449, 1130849996116161, 2923728051645552963199333300356476754602122819394, 
    17127037667954345495909952439432220128023951170, 15121341268958217710875072373595407989066104045286341663380342275931580135751596557203035207858949121428643059895024514450649403163779305426711671458405530078426125824800343569627158820853426040850494511284886257573637303597827265071969004039538210767368249877512, 28545062765744990423259205616053322952168453954, 28545062765744990423259205616053322952168453954, 28545062765744990423259205616053322952168453954, 16609466995054676039264686756895757063880650068832622971274094502085954536302567317406283616532815556, 
    16610449074603487350192158912779425439564230646405489915487364804369025545991802916291647880297701060, 1461551814199091601536922032406385483927034869570, 145275260768449, 145275260768449, 145275260768449, 1130849995133121, 
    1130849995198657, 1130849995198657, 1130849995198657, 75318833451201, 145687577628865]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924da00049241269808209a4826936920124986d26d24826924934da00049a4924d36800124d24926d00026934d24da0004d249249b4000db6db6db6c001b6db6db6d80020924924da0004100820800920820c34d300000000200200248049349a69800009249069a68208269841269a08200001241361241269a00009a09b69208208269a69a48209249269368001249869a6c20824920924da69049241249b49209a6824d36a20020820000020824920934da69049241269b4d20924c369369a4136db0db6db6d86db61b6db6db0924824936824124124986da6d860249261b49b6920986186036da0800004d04d349061869b0db69a0924924820000820000900000924d34904000000000024000034d249249049a69b69208a28a0824924da09000049269b4820820924934924000124926d24824924924902820924136804020b049a6c24824924924da09049241249b492092492492408, 2923371258738394617511777935173078628837196051266]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24900c00004104920820924920a26030030c201a68048249248041b4da4c374048069a4800800000c38830d34020820926124000034da41840041069a49249209200000000040040209208208248000000001049200000000041b0c00000020804920180000c30924104124924124836c26db4844d049049249008369a49a60008001a69269a08200069a49248209248268208249248209240300001001a48000261a6826984d84c30806920180800820100db6b30e80186036006180000030da6e349001869a49249a0000c36906106000000924924826984c00c341800061249249209a6130030d061269840040008041348000208208249041049249049208209a6921134124124924030de71e71b0c26800226924924824924800004006db0180004000986830000006000186000186020c20034d24d351800008009a68201041249249240000208269a68041049249249069a49249200001000000000000248275a6c000000060008000001a09b69a0db4934d340000008208208041049249249008208209a69201041249249241a69249248000040060040000048209248200000060001040001b6824924834d24db4d04000180338dbc0001800661b7800006300c3cd80006181000040f38f38db610000600cdb6f00006001986de000018c030f36000186030000c3cdace2698490, 1161234880008640, 1161368023863744, 28545062745818983358373638187091580235313869634, 188397414118873100197553673337628427696516133698, 513258889805605223322046716863513927553819518280132834263281228172320860999911596055912701620997604789162605682976289732430875467064312609936858817387901635221197424638022, 3957316615499469982613701026949970134706107164370788607669008626706598596188174160956720691207835445835676495735436173408833829800461849296379635389416383700263823886555196999, 
    17127037652013426268709507324442742335620543298, 97053213336547940768836784797262728837371818818, 1161234880008640, 1161368023863744, 28545062745818983358373638187091580235313869634, 188397414118873100197553673337628427696516133698, 
    513258889805605223322046716863513927553819518280132834263281228172320860999911596055912701620997604789162605682976289732430875467064312609936858817387901635221197424638022, 469678024262996135954626474396049201884783220875215041054024621605583225016001527993514795343872487456337410769246176010095495290068320916796611552389373285131418640684049581264097599128241716526687154708043139109938991244113303636377729362677976272995976245997512, 17127037652013426268709507324442742335620543298, 97053213336547940768836784797262728837371818818, 457547438363072, 316943093993920, 
    1247177207726153154038098006463783627512013935540556657255957341792308789515530887164147822323305077106444814543144337664534432445601373800292744158009052914568042473597228498332232016099205100591132002347970619635020768845287971045613598277091314578401715288978575512370808464068486039296824623733615911617759429979852429486579668204240116108636468556611913406049787909100141194856168082024173730554763263307787636383861869959621288495660086336258626231393854654835659388212755817542960512741996828805180838604]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924da00049241269008209a6826936920124986d26da4826924934da00049a4924d36800134d24926d00026934d24da00049249249b4000db6db6db6c00186db6db6d80020924924da0004920800800920820c34d300000208200000208049269a49b6000924824924104124986da6db4834d001049249049040009001241a69049a68208269a08260069b69208041808269a4820924926b388001249869a6000026920924da8904924134db40009a6824db8924030c200000208269a0936e24904d341279b49209a6c36938a261a49869a6c20836db0db8e36d849261b49b4920824824838924124d34124db49201249869a60000249209041041049261a89a0820d24c24924924030da6db6da6804160c24004100036186db6820a26984924924824924820004826980800000924924904000180d86020800064d249249049a49ec9209229041a6db6d86800038e34d200041069b6db6930000e36db6c401a6db6da6820824924da09000049269a4000820924934924000124926d040249249249000069269808001048241241240001849a68208041001249249049269a4920820104000004000304b28024820804024000804100026f6c920d3c9459260001a69a6d868041209041049008261289a69201040249249241a692492480, 1161368023863744, 1161368023863744, 2928723417169099951829284426158403243005788042050, 2923059026610039557868417108394340061549095551811, 2929080229092276441799548997650765616789883728706, 2923192831676724883718908784880608966556541798211, 
    2923371260099524085215377515428944763685921895234, 1161368023863744, 1161368023732672, 316943093993920, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164444803317065078691857111352826925133177765848226189623022983500158293775044885648381048902, 581094329041473, 
    581094329041473]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 0, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a48000200000040001a09800009a4030836c001a6800927104036d80da71b0c049249800075e41049200069b89208240000001041a6a06027120802924920000804000026800024c20826900da4db4904db6036936d241249260301b4904124900d84db49040801b0c01ae4180030000b34000006c30030d04000d86026d20c000060200040000009a0804d300001b09b0c00000026920024800180004c36000034920924920006c301e9a06000db48249248001b0c07a68184006c300412061000001a09a00301341041249240060300061b6c04944904924900000c040008001041441249240318481391b0c049049249249000000248201b0800c30c36db6c219a69a0924920806820924924820c36c30147106186820826920830db6c00c351800269a0924920000100800100020826826924834d86c24db41869a09a4924920000000030d801001b0e00c39a0400cc301e7a061001b0c06c311840b6e041b4e30808920124924920d36004d24924100000000004100006a208209200001b610610412492490249248, 736462597071981342345179509825147940046232400706, 5711778406529883243337093467006430218266129218, 736462597071981342345179509825147940046232400706, 736460511821621273943699801782668006681644938050, 572863283729344, 1135263481074624, 
    736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239141658954523784002, 736462602516499213080194925239143910762927403842, 261549947706041557390176538361675074190761867923720792719370073773866664630419112222312143098359429, 
    1040117280306995750137338785863443481636722505730908627853379824183438394816862088810446707168495237, 581659376751552]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 0, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249061e0800000926d04d36d0c024930da4e218049b6d86d26d84824930004845920000000826860126d040369608049249a61a69b00009040001041241261869a6820826db61b79c6db09a49a00009b69209248009249a4820924824986026930824924c369369a41249a41249e6d86036da0804100c041041069b6180db68209b6800924924824924824926924da00049a68249b69241269b49a0806920924924986da6da4824104920806920000db6db6db6000124926d24804800800800c009041a6c061a4c200069b4d86a30820d341049240001b6d26da4c00034d24924904100000000900934db6c26d84004d04104d34d069209249a4936800124904926020824920924da69049241249b4920820da68361a48249249240a6db61b79b6db0936d86d26db4836db0dbcdb6c00900000020020db6c36db8db61e6d86de6db6c249b0dacdb4984da0034934da0db6c36db8f3c1b6d86d26db4830db0db6e30f04836d86db6db6c02924c24d860369b0836924c36936da4136da40a4920804c241049a49240309241241069a0834920800124926d24804130da4c201049249a6c26d24824000926926b34102924820136804024820826d24824924904da69049249209b49208041a6820d24824000c3693682412492408, 105624522262593, 7729078731994588773169520666295190370093120183095540765374834179524720111209079132734956845828998767437522522968701847930303834604344418333858866518157924867386161229723719, 285984802024043109485611792222636670138114388802, 297402827121999908547499817888410059126394073922, 145825436029633, 163417622074049, 
    163417622074049, 150223490929601, 163417622074049, 736462602516499213080194927600327152197750010690, 567900462138049, 73673864188352, 
    565220398350913, 73673864188352, 567419421606593, 580613561139777, 183402028136003777047981896505496524284749689666]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 1, false⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24a24820d24d800048061a0920820db68369341041a7000924924824d24d80004da4d049300249269200200060009241a7000824924802926920834930000026800020824836da0d24d041049349340001349341069001049249040b4c34da4d00006984124920820db0c349b01041a60009a492483cc36c3cc00000004b209a09a0d34c30d24d80004f30dbcf38000100004c00004100804920920920300120104124020026924924800800004826800134104924924006030d00024804904d049249000009a018080010413412492402186602c9a4804904d24924900800004820c008200268249248219b0007836de0920d34d36936000136c30d24d041000009a0830820f30db0f30000000126820824834d30c349341041340001341041041060049049049040b6db0e36db1804db6c36db6db6324800924924834c30d34d000008200008209a0d34c34d34104124904100004d34904100004134d241024b4d00024d341869a0824924920db6184830d341a6826824924800004d000040008209a09249201801b0134d04026826924924834d00024004004f38000f38db613cd8002ce26984902124000900100106900124934904000134100100020826824924806106d04d34d04124004904104134336000b389ac12408, 84682268545984, 150655113761728, 572863283729344, 163849253295040, 581659376751552, 163849253295040, 
    581659376751552, 145687443406913, 567419421606593, 581334286981683693713488187727256180800793599194341058564502924039835935637918586019986842972206354501, 16610449198353422912511803907944161699844673149109530320237866828533505728608717347251478182110375557, 80284222034880, 
    150655113761728, 572863283729344, 2923728051608344394892238318514072679255399035714, 2923728051608344334045009507559061407413645177666, 1135263481074624, 2923371258738394617670543744030837028375597495106, 
    149673307279553, 149673307279553, 149673307279553, 2923728073386415816985071169215036283046810710850, 581334286981653481327101393010222584013122101823161845146208742016191432707815032123854714693662756933, 16611462957795337051808645890665641476946317295896982266441921389089590297320328872317895957838507653]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none, none, none⟩ true 103 ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩ [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249061b4930000926d04d26d0c024930da4d21804924940004935920000006828860124d04026d608049249ac1a4a60000904000d019341263069268208249249a00049ec920926800920b248209a4824986026100c249a6c369368261272461b6db6300849001126dc88209200349343201a4904130004c341049b6984924924824924824926924d200049a6824a369241269b49a69869a09a4924d86d369800241349208069210411bc1873380009249a61248049040241241040208200201a4804100124924906904934d019241a49269b69a61809041a6da69860208269a08069208002248209a48209249a49348001241049268000269a0924da89049241369a4100820db6db61aa8249269241269a69268000249209659041049a61a49a0820d34c24924924020db6db61a4804134d04064900836db6d86920924924824926d86d2718c036e30db6db1804c061b4930000db6c38db6c60126d86d26d8c0249b0da4d31804b361b49a6300db8c36db6c60136e30db6db18000000049019200060069a8860120000000000802926d861869254308349b61b49b6930926c369b4c301b4dc70009041b48000001a0b20d848261b0186930124d261b49b69209a6d86d36d80020830d34d041069b61b49b6930924004924924125186d3698c0269a6d86036da0824900134d34900900000000900924c34124924024920804d241049a49240309241241269e0804920800924d26124c04136da4c21184924986026930c24006aac9209b41049241049249241249249049249009269a0806a30820d349249240041b68209a68249261809a6800934d860269a0c2492092400000400402480002092482690400400080492000002082018cdb8f30dc60049b6c20134c00036e3cc36f00036db6d86f30000db6936d260001b6d24d24800036e3cdb61800000349b6920000db8f36de6120006db6db6db01268000269a0824904105924904920c209a6920d24d241249241a0834d0412490680018692492482492480, 95677451867072, 105624522262593, 105624522262593, 6767645792041897653518787153367553147015770872372382878943165879631626595205726881331280043943432208849424484184025696442329691198012861479732255489068979078365622318092514278935259345579783682345789849900214021225027960657163111514706470609891749467102685084726368406007196333842635405799940711577909411289488901798352816626978723707331013796336829690409094042376626137800770634, 105624522262593, 105899408763201, 
    105899408763201, 105899408763201, 194641827349460318704797760236000879110040476903690560058967534044104936307085814270279922551796421, 105624522262593, 105624522197057, 708156914160321, 
    45694401221598507776227517383879725817021926211, 143007937483457, 3957829878074701413907686587827558920396154515476837234848369427345372996214466429093741388207507762206778840774106734955451788720619767685003242760517082224079341682853671494, 143007937483457, 145206960739009, 162799146783425, 
    163280183120577, 145206960739009, 162799146783425, 149605007250369, 149605007250369, 162799146783425, 
    35255775985729, 708775389450945, 708775389450945, 105624522262593, 316730763192641, 316730763454785, 
    182710353988394096945727813344201171691599049538, 563021375095361, 1461507213920909015201252374224352795098672608066, 581659376751552, 581659376358336, 16610449198353422912511803907944161699844673150382369653175782224809510879283186691525473357923298949, 
    1462220839128391462825535371062575972393936843586, 16611462957795337051808646749353314959229089455844027623461870969448430711160026637415104874884836997, 16611462957795337051808645890665641476946317297169821599379836785365595447994798216591891133651431045, 73669502112192, 565220398350913, 73669502112192, 
    567419421606593, 580613561139777]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b8_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 130, ⟨1, [1, 1], 1, []⟩⟩) (prev' := [⟨3, 129, ⟨0, [1], 0, [1]⟩⟩, ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_3_0
  · exact tv_b8_3_1
  · exact tv_b8_3_2
  · exact tv_b8_3_3
  · exact tv_b8_3_4
  · exact tv_b8_3_5
  · exact tv_b8_3_6
  · exact tv_b8_3_7
  · exact tv_b8_3_8
  · exact tv_b8_3_9
  · exact tv_b8_3_10
  · exact tv_b8_3_11
  · exact tv_b8_3_12
  · exact tv_b8_3_13
  · exact tv_b8_3_14
  · exact tv_b8_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x249249249249249e0000934d24926c04020820930f00004824120000920924904906024804926934924d340001a69a6da69a00009a69b69a68208208061a00009209249868208248209249249a6926c04024924824824c360040248009a6c208209241269b08201249b6db6da6c04024934d34d00806db6db69b01009248209869a6820824824d34d359c60001a49b6dc7006035134d36d80c069a6936db69b01009a6d34d341041a4db6da6c24826db4d24904900800000000920820c341041241a0d86da6c040200001249049008a4964924930000924924926984024d369a4db01009249b0c30db4d269800041249249209041049269a48049269a69a00009249b69248208249269a69b6100db6d34d440001249a69a6d840249a00061a69a49208209b69249248209249b6da6db6c04024924c30c36d349a61241249a69b4d34d008069248001869a69a4824800020930da0900800820004920000824c3682c020020000004000030db0db0d80c00800000100000c36c38c360001049e6d36c00020936da69800041269b4920000c36f36e360001869a6d34c0002093cda49849049a69a00009a09269868208268248269a61809300000041341041209a6986024c200061a69a69a08209869a69a68200061a79b49309209249041869a6c04024934000824f3c9a40208009a6d248208241269b4920124980186da6db4c00000d041049060061b69b6d309248208009a69a68248049349369a49b0180934db6da6c040269a6da49a01009269249241041b6db8db6c36c34e249249049000000209a0000926824104124134da0924904900524924da6926c06034d34d65900804d36db69b01009248000008268208248169c6dc5136d80c049349359640001269a69a49201009a69a69248248269808241009209a6800924824820d36d451460001a6924924820834d269e5904104926924924920d36924db6000124f36b649e6000164030000104d040208249249a4804100865934104920924924920096db6de6db0000d34924924104134924924924906db6de71b00009a79a59249208209e6d64926820820000180826820104124924d241049049249249005b79b79b70000269b71b79c6c000269248000268209a08248100001801b4120100824104924000006006105804020924904900000000800000800036c20db4c200041208249201041241249240001048209268041049249249000001a09a6da0920524800000020000000004d04104900000db0836d309248008068269a68248109249249a6da6c04024924d24927820824924d249b0920820824c3c000124d048200248249241249b09200a49249269a49b0100924920920930d80104902926db6da6d04034d34d249041049369b69b4920d24d349249241b4d34d34d041069a6806186da69248041041249249001869b69b4920124d34924924022924924924c208249249249b49209249a6d26c24824926c30c36d349a4020924924d248249249249b49200a49269b69b69b0920924930c30db4d26904902000824c36824020000820124800020930da0b00800000800920180c36db8c36020000020024806030db6e30e00c24126db4da0000824db69ac0209049a6d24806030db6db6f008261b69b4920000824f369241240a49241061a49b092092490002093cf26904902134d36de7236e00c06da6db4934f000089a7236d36040104106d878000261b4900004d069a6d34c30134014924924d36d360201b49b41241a61b00209205b6db6db7006026db6db6db0180944d67926d80c04924830d349a6820824826d351249049069a692492082163cdb99e6dc6124924924924846dad936db0c0592c924924934904db6db6db6db6100c000041361808209249269209248249249248024924009a69260040000041041041000261a49209208009649249248249869b49249248249860268209a48261a0924926920812424a24d24940000926934926d04024924d36db69a41009209b6db4d20800004d24100120900134906c04804926db69a6100924d34926104134da6da6c34834d64b65b04904d24924db49261041b69b6925000024d36934984100804d24186920820d34900d240001249268040000249a4a049009a69b6dc68000249a6db69a4100924924824d36d36a240061b6938c30c201869b69b4d30124934936c04024934d24984104d249249a0920924d36d36924124934926da49a4904924db6d36924030db6db71b6c208249240349040009249361240249249a0836db4d20900006da4d44c30820d36d368240001b6db7134c36db4d26980004d24db0900000c34126904000124926b248000201a4824904d24924920904134936d848000209049a41041049249a69200008249369241249249a4804d36db8a24000934db5154000124a26db6d00024d36d6590080cdb6f3ce300019b6de79e60001e79b79e7980c0ce46f3cf60000db6db796400033b24d33d980020000000000820000004004124124000000000020000d001049009a5b3d9a4000124924924820824936d349041089a6924920920924964924924904104100d35800d24100034d249049041349b6db6904034d4d134d041049269b6db49209251249241243379b6db71b0c36db6db6da61879e73479e61b61a6800000000004005136d35104104900000000920124d34924124026934d64d00804924924920820924d349249241a692492492486492490413492492490490692cb20006c30000980000db4db6800000000c00026000066d36da0806dbcb269a0000d35934120020924924824800034d24924900820924924920924924d24100034d64d00900824924920920104d34924924020924924924864924924900926934924c000249a4d249b4100924934db6da6904024826db6d34820000134904004824004d241b01201249b6da6984024934d249841049269b69b0d20d259249261241249269a69a49308208201349061a48200049249b09208269a71b6db0c209249a6da6d34824924920934db4da6900186da4e30c208249a6da6d34804924d249b0100924924936104124924926d24824924924da4904924920926934934920920924924820db6d348240001b6934d00020834db4da0900006db6db4100db6d349a4000134926824004134d249849000049249bc920104124926924124924924824104d249a6120104924926124124924926d24824924924da49049249249200924a4930db4d20804920c249208209a6c36d369a41a6984924924830c069a0806920d249b0db6d30804926c36db4c201a69869a6800004134db4c24904106da0826920000c36d36d260000009249248049400249a0000924c209268208200009800008201341049241040000268208208269a08249208209200009a0820920820806826824820924c36d368201248009a6820824934db4da69069261a4924920d861b6db6db6c349a6d36d36d26124934db4db8904104d36d30924100030db4da4904134d86da48000249369a6920820986d869a6d840049449249249069a69a4924920924924820834db6db0900006da69b4000820db6d36d260001b6db6d84034d34da49000061b0800800000d34924904000186c208208000451249249069a6a269a0820d36db6c240001b69a6d20820836db4db4980006db69b6920d34d36924124d00000000004800006da69a48200000001001200001b6924924834d34d249040000000041200208009a6824800004004004900824924924920db492492410248, 3957920449257079469080845689865187924151315275616082471199775114488424426119832772153024810198787987097091909662669079247976904835567370733544522429250291433554938222629347910, 581109621461952, 1161367822537152, 1130439822020801, 176063729111233, 1161368023863744, 
    1161368023863744, 316943093993920, 1161368024650176, 1161368024650176, 316943362953664, 290555083887040, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 572029792162240, 
    290554815451584, 299351445344704, 371089997073248001570191377446652703691430196034, 290555083887040, 290555083887040, 290555083887040, 
    290555083887040, 290555083887040, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 286156768940480, 286156768940480, 149817327096256, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584, 299350908473792, 299350908473792, 3957920449257051350869629794887795358285639961157105646737809262289535250311748876691063690664586009528830137948770434459539464824286377350413609929531049863695805937350603334, 567915481928640, 
    581109621461952, 581109621461952, 572313528439744, 581109621461952, 283816003375297, 572313528439744, 
    1135263213425600, 290838283293632, 290838283293632, 853797363520448, 572313796875200, 572313796875200, 
    290838283293632, 290838283293632, 535719680387928928508262249411646441580330649951083551532746788100983712849239947652506897387098225220, 145706909176768, 308430469338048, 1128653050153025, 
    1128653050153025, 1128653050153025, 1128653050220737, 1128653050220737, 1128653050626625, 88515535702081, 
    145423441334720, 3957316619184925684297189135165343748734463072032449210831422820855888213761873049045068183013169601313331595898196396784592148744153662830160795947834798519981373451856207430, 299634376315840, 308439596143552, 581109621461952, 308439596143552, 
    581109621461952, 308439596143552, 581109621461952, 299634376315840, 308439596143552, 1135263212901312, 
    1135263212901312, 2923371239690557509060862098716539164780434371138, 853797363520448, 853797363520448, 290847410099136, 572313528439744, 
    853797363520448, 572313796875200, 308439596143552, 308439596143552, 308439596143552, 308439596143552, 
    1128653050153025, 1128653050153025, 1128653050153025, 1128653050153025, 1128653117329601, 1128653050153025, 
    1128653050626625, 581109621461952, 572313528439744, 88515535702081, 145277412446656]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249249a4925120000db6db6db6186124924924834824804124100da0db6db61861b6124924924804820524924924924904904800836db6d86186d848249249249249249241841249249249069041041041b00009349241041a41b6db6db6c060249249249069008a4da4924924000dc6de6db6000134924924904824db4924d240001259b6d34d360001240041249241a01c61e61b6000104924924904820924924924904104924906806db6d86d80c048209a49249200040049340000008249248248240009048049008241b4906900000906104926906c2c03cc06c00000920820924920d000000040041308249249a482410c1049b4b00804c349241009a0d86db6000db6130d249248348361c61b0006d84d869240201341240041241249a0186d340301361001249249848200041341b4961987986000d86120924924934000c36f3cc36000000186000c20c061b61b61b01249249248209049049048661b6d80c06d84804924924934d24db0180926924d24104124924924904904100120130000926924104124124924924904900524924924904804804800824814964924924924920100924924924824824904924100920924924924824820494db4d649200009249249241041249249249249049259a5924d20020920104100924c201041249249241049249249249005249249249861248249368248200001001b41201009241049240000048069058040249249049049200041200241201041241249241041249249249000001219349209205a49249248000048649348248104928a48a4824924924800000104c26804820924924926904984924926d34824b06db6db6db6c24820824924834006f36c36c300209249249209063061bcdbc1b01c6c36c30c678249a6da6d86db6db6c000248120925149149049249a4904000004104d049041249249249209049249249248249049a6da6d04824904124824924824124924924920812412492924920924920c049200041000209a49249a4824124924924904820824924904da0924934d04924900024004920c24d20000db6db6db60001249249348049301249a0000924c04906800824104900100c200001341341a4104124824836800c34d04d86d869a00041000200001e61b61c6100c36d86d875800009209a0d20000db61b61c6020024836834820924824926830124904906800824924924920904924924924120924924830db6c36338c24134d04e24c00024924924924120924924900c07987986d80186db0db0e308241049001a0020000d249a6984104124906904800024924da6904926926da0926186d801b00300019b6db6d86186186c06c06c00036db6db6d869a69bcdb0920824924920100004924d24c20820924824824000124924934824924926d000061b6d80c00000db61b6d860001e6eb6f30c00066db6db6d86f36db6e308209249248040209049848048249249249209049249249241209249249a410248, 1161165959205312, 736459918326967617761221917034528982686693864258, 3957920449257079469080845689865187924151312875865046798225662926908875983757671340594824493370926789276042752215032645197139226040711466983107102833308149788955144438184665670, 123695392443150858820591777138244336291394395440714787205159704201763050601339851629069209094461428404674401000154992733047238007702126188065678048127864424256712487880090182, 1161230450561472, 176068032467392, 
    1129145300357568, 1129145300357568, 105630973102145, 1130861139726784, 72714878521792, 72714878521792, 
    2923059026705582403273461691369447352415294097219, 1128657622029249, 1128657353982529, 4089193962158339516515071346465170652150032928531769189723606633645627869991822488917762999952826154346271425790918405154719943833034353681826258450776718619856368769362286150, 265751028401102427289067248950908305789144733842075096001308275958421885846822083711059483610047148101, 1135254488355264, 
    1130860736811456, 3957316619184925684297189135165343748734463071869861173193011719549700737721214921254185555839939557909052319763977186599168686537411926603100512561354959370226015551421898310, 308439596143552, 581109621461952, 308439596143552, 581110158332864, 
    72650454012352, 3957287485226948974103744061753945314353862245461522523274866709018383083513226931727335379675683658574435213199391852306695061568797308891377646522680459389903268938471946310, 3957287367290623198430576803805780844030012398690889939847578035126115638576355549661947710495616287923144332728583030407153477089393724349722670032861095030946969343860586566, 33338494248124709924710172511000926192004885740562247571412966604817919374261643270895065480047793861, 72650454012352, 2923059048494287750744621887311993532425221769027, 
    2923059026716216267804560225656018656792056235843, 1128657353982529, 33218933990109348390486863965668843610206729737035290861388417537392854076580101938017597147063455813, 265751028401102427289067248950901754522153426979699358746261707112147361099140469125691584914453164101, 426692192506304, 145281707413952, 
    427173698605504]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x14a249349a4924d300009c49c69ac000138d24944c04036da69c6b00c04804124100da09869d60001a4138d24944c04034926930806d00526924d26d26d26b00004db49a6da4030104d041058000261a618000690ce39a41240280d249a4c201b4024d349249c69a69ac0001289a69a69810041041041e00009869a60001a41b6db6db6c060269a69a08071008a4da49249240009a49269b6000134d24934d04c36d24934930c049a4936da60001675e75b6d800059c6db6db60001640041249241a0000000800824104d24904d04c30c20934930d00926b251a8d80006db4926da4040126da49a6980c04d66f66db6d80004904104924906c0002002002090d26ceb0030000c30824d24c340209a4924920004004904000000824924824826000d240059800241b4906d30000906104926906c2c03cc06c30000b20820924920d800000340041208249249a482610c1041b5b06804c349241009a09869260009b6130d24904c040361a49c0806d849869360001a61661e7580036d840041241349a0000000820804100124904d84800020980b201800041341e4961987986000d86120924924934000c36f3cdb80000001860000200061b61e6db0124d24d000249000041b41e41a0d04924c201341241249a0806d84d00020d20b20d04c00826c24834000104105924c679b6d8003618d34ceb000d2b0804924924926968b2c0001251a4a2c981004904c059e00009289680003241b6db6db6c060241a49a080cd00924924934935936000124d24d24d84106904934000124124d24d041849041349249a49c6dc6c00024904130936800044834964b34d65137b00c05b20924134984104902924924d24934d36000124924d24d84106d24934000124124924d04184904124d34924934d24c06024936924f04104924924d309209bc9c6d2c124020934d04026824936904004906934924d301009249b6920124024d24964db4d24d80804d369269261241841b4d20c04904d24926926124104924d24924000934d24945024036db6db6e061849249a4936104134d26924d84104920824924924db08008009249241b6d86d81000c00020804934100924924924c20824924936934920924924934d8410492c104800d34924100824104824904124964924980024926924980004d349249271209249a4d248001249b6944935000034936924984104d34e24d36104020d04124930c24826f269249000049a6d26930820924da49261041a6b65b2d924826db6db6db0c311c6db71b6186238db6db8c30c24d36934984104b06320034d349049049041241001a0904124805004020820024f200049249a41069341041269041a4d0482080092c904100020804926104904c05964930830dd6c011d8c20924924820d24824924930930920924924904034d0412480092c900100824144824900006db0de6db09e8a08f3c926124124964904036834926900024904d249209219209249a4020134124984104800104c24936904184904924e24106134004100904134820826124f24904020984d2c924024126900004d049249208349209249241061241a49a5826c24824a36db6c30db8c249269041b4904830d801b79c1820824124f34d04900526934926d48d35800024d36db6d86104d34da4920c20d24db694c244020100c00004824100000000906d349a0820100924180900004014924d26924da4dac1841349269249069041341a41e00009040240000241249269249009008a49b75bd9e7000036db6de6f00006db6de6db80002679bd9b7b37000036db71b79b0db0c30187806000006db6de6f00000db79b79b0db01b6de6db8000026826924924800000104c06004c209249249208000361b0db6000985124906934c24800100006c060282e9ad8241800820824924836000000100186c209249249209863061dcde8020008139020000001008e26d861002049a4dc0c20000e371381840081249b4d24801036dc8d8610020492a926d30040f371c618610143cdb6d86184060f37b3db6c0001001a69048000000200309000040201041200001801008040109249349041801249a69a61840061249a4934804926da4b27104124da4e361841a406136d1e61861641041349241a01040008008241269249a4904824926da4b20100124934d24924d24b000049369a4d24040124104d05800024924d00004906904924c20124024924d24d24d24980004934d34d261041a4120000005904934d241061241049249269241041241400215349a493c104124926934b04100924924924824924d361041241349249a49a0d36934d84104904924924924824da4d361041241249b6d26d86db6db6c30c248249249a4930820924924d24d24824924924924924124b041208249241040009241249241049a4a24d248201249349a4c20824926924934904924d249249209249249a4924d24124186820d249041241240200300249041049b6d26924104126da49b4904134d36d24180d34da69389241258209041249208000361249a49000049201049200009b012c9240249249a0834920924924d24c24824924924924124104120824924004000924124d240001b6c379b6c24d20024f249849069a6d349c41a6d269b08209209249a4820124124924820d248249249249049049249249209209249249a4924124124820904d2c9241240145149249249240009249a4926104134d249b4d448249269249249049249269a69a4920c049349241009241841249348249009249a4924800124924924c208249269249069069a49e49609209249249261041a4924924c20824934d24924984106e36db6db0c309009248009241208009341a4904124924924900024924964980004d24924924920924924d24820124924924824924924b000049249249b0820924924d261041a4b2592d924826924936934920d34926d2c9241a4b041249a49a49049029249641041249243200009249268001041249b4d048000249349a08049249249a000092492410002092492402480002493498410082490490492092492692410412492490c800024934904904104924924920820924d24924124924924800024924921900824924900920104924d279240208241201248249a4b24900924d26da49800049249a4d26830134d255269a4920004904d04924900000026da0984900c49a4b2402808009a4c261340249269249200049249a4930820924924d241241a4927b25824824924d249841069249a49308209249249249261041b8db8db6c30c04020900824d040008249241241049249c4d36104124926934924904926d24124926924140134db49481041049269349249009249a4d24030124924924c208249249249249049249249249209249249a6d24824924124936d269241241349a490410492490c800028da6a20004104928134120000a26da6840134d2492a800026924904c008248249009200009249249240209240241248249249a49068209a4924834020924924024824924924924904924924924920924924924024920924920c04920006180020a269249a48241249b6da6d84820c34924904db0924904d04924900024204930c04d20000db6db6db6000124d3413a8049241249a4180924000820004134d249a6c04844d06034000900824924924db0186d308009a40009241041000241000008001049040000200041b6000104c00024100130980104804806004d20830906d809a4004120800104000036c04d871009248249268301a49041070000289a4924920984924134d34000924a38f3ac3034b0269b6db6e3633ac261349061b7800024900020800104d241a8dc0020d359ecd6c8241061a5030836104d34806d268041b8c301b0180c34926db49a0104d359ecd6c824030c301b0180c20034136037100c30006c060300009a612c1a4020004124904800000db69388000001248340340000269b4a30c049b6d34d20800186e36f30000068db79b61800079bcdb0c30001a46de6db633adb6f38c2000c336db0c000019d6db6d860003019bcc30c00036db6db6d86db6dbce30b20824924920100004d34d44c20820924824824000134d34d38824924926d000041c6e00800000d80006984000108ab8c30c00030db4c36104934db4d20820924924804000104184004020824924920804104134d440009249a69a6000108db6d008000069009a6100004c2adb0920000820d2c9a41249a49b68049249241008209249a4106924134d2480500402492692490490492492492492c100100124934904804904804160000a48200000000c269a69a08041009249a4820134124924820d248249269349069069a49e49609209249241069241a4924820d2482490492492c8001208009049a4100006036de6db0934d24904024904124904104020024924100004904d24920921140924924c201241248001ccdb7146824904100904060820826924f249040209a4d2c104024924100004d049249208349209249241061241a4b2592d824826924936930920d34926d201241a48019b6c37b06030c00924f24104902800124820124c04136904824900006d208349201049b0920924134927924824104124120820000904800904104124804004000024930804904924924a300009241009240209248241248000249041a490082490490492092492c924104104104820800024d04824904104920920100820924d241241249a4924800024120906b00820120904820104da4126124020804120124826da4b24900004924904a20000a0c800920000124845164c00028a40809804b45964930920db6dbcc301b6236dc6c00246c3ae36dc0e81006db6dc61811b0db75b6e06038c3d04124104024818c007836030030006dbcd80300db0d80f300001c9349341009206186de8180e301b733ac001bcc371b7180036d86db99e0c36180db79c6c601b6346c0033af3780c000036de6f06d80c699ecdb0db0c31a46dec038030348c001b6c471c8d86036d86db6e36188db6036db8dc0c07008db91e0c50180e38e36db62b81b6db6f3700c039249249a41a60dbcdb0c00d80c0c186d871c6db01813311c6de60001b61b6dc6de6c36c36de6db1806d8d236000de6db81b6330c6cdb7b08c0000d23cde0180db6db8db81b61b6de76b7806d8133cc30c30c361b00003679b1736c30c36d80c00000006dbcdc1730dbd9b8dec1b0c36dc0d87180008de0de6180c30e36db62301861b6f3700c038dbcdb6d86000dbcdb0db60000301e01c7000036decf3d980006000d80030decf38dba000346f361b6c00000db6036d80008e60db8db0000d88dbc1b61b6f379b6c3000d236f08db0000036d80db60001b9b36e3cc00036e36e06d86f36dc6db0124d24100024904924924c20124124900024924b20904820924d24824000106d059048241269a0804d06824926920804d049249208349209249249241241a49279258248249249041a4906924920834920904124904920804000824924924000180db79b6c24d249241009241049249a4100124124926924904904920036d26de41a0920004da49241201049a493c104104126934b24900924924c20124124924820d248249249249049049249249209209249249a6c2482492482002412c904124124900024924824900824920904920000924924924020924124124824924b24904820924c241a4020904824124824926924904904924d24924920924924924000134d2412680000092402490000492692492000080692c12412492592482480, 1161157436117440, 996326080267117150069539610926479629085644235203682507087665625454694564551298210164613094470797211258086398709214024634705375682658086289793468924027786654242637316675142, 1161157436117440, 51381112940244825504347310871443639153522129730, 1125908774125633, 2923059026695112096712381925630729796131540187970, 
    1130719137509825, 51381112940265594691781450181960012947242629954, 567434981938112, 571833028449216, 531567574968099413811186360965354996902178173148492645221429664407691605843714986949838851227552752708, 1125908774125633, 
    1161509891805632, 105630973102145, 2928713332559469371677272818607758208630368776770, 387105950083393, 2928713332559469371677272818607758208630368776770, 316737205905729, 
    1161509623370176, 1161509891805632, 2141060067972986641489983245086216561761654305052551839625955993797949030643018055440989186062078276, 387105949821249, 4167933910274413237245272489742857075257029778043729253603258568650971004515687507990434955024782807430269429343394198434573434716762439875127798874828720019277292754046022214, 316737205643585, 
    1161367889514944, 1161368023863744, 1161368023863744, 105630973102145, 105630973102145, 51381112942721560628132222377356575957917381442, 
    105630973102145, 97053213331397020659796016847637924631234221891, 7759266745884737787867324976944749980532741920554690601082224481221757494454849463974938166481354484065363615996632407204735934235223147936744552146706388694244984216351302, 387105949821249, 1161367889646016, 1134980013232576, 
    2928723417169022067376522458704195217439525450562, 1130581966852544, 1134980013232576, 1161367822537152, 1161368023863744, 1161368023863744, 
    1161368023863744, 316943362167232, 316943362167232, 188402292404221478345290564329279322293436166978, 316943362167232, 316943362167232, 
    316943362167232, 1161368829170112, 1161368829170112, 2923026272390554537988115669023515424749711799106, 917365294896064, 2928723416146182422699051016717009949421530528578, 
    2928723417169022067376406401382792044126027133762, 2928723417169022067376406401382792044126027133762, 1130723298251200, 1130723566686656, 1130723432468928, 1130723566686656, 
    2928723417169022067376986687989816354975032292162, 1130723566686656, 1134980550365632, 2924431224707956147530185292011445697189328728898, 862868602360768, 149818131878336, 
    862868602360768, 290555620233664, 3957920449257051350869629794887795358285641428609152284851801827183634099114761788754536029376551979929867989046204625157455101418220277231743762659643258421713506383448502854, 7759266745884737787867324976944749980533451723996385529686276555252898123882929452606839361515917891368976565329855248476193662653752842279314836769978955928191582389400134, 283958550335936, 283958550335936, 
    286157573460416, 572030596682176, 833693890331902870340313078954012348387065893699, 572030596682176, 183045235268561950217819267195888480153763853122, 1130723298251200, 
    1130723566686656, 1130723566686656, 1134979745059264, 1134979745059264, 1134979745059264, 1134980013494720, 
    1130723298251200, 1130723566686656, 1134979745059264, 1139519391273408, 1134979745059264, 1134979745059264, 
    1134980550365632, 2924431224707956147530185292011447948997732348738, 862868602360768, 290555620233664, 290555620233664, 290555620233664, 
    290555620233664, 79449387438528, 290555619971520, 299351712993728, 3966977959076728493407069132047389504248000812626318421807933950031306258814136838459081076906932684677732169926361810724927128792477930413800872626509811725597425125512180294, 7759266745884737787877145148768247869732949545514152165202631488330373717290523336887000994051046685369872177239443931333151165653160884755603345950179478423099531195314758, 
    7759266745884737787877145148768247869732949545514152165202631488330373717290523336887000994051046683609926858807850165537288420772519394380570558046730906856655854126494278, 7759266745884737787867324976944749980533451723996385529686276555252898123882928947421917201157735849060283300103708148030651350988333041303302301037356387888524202937938502, 7759266745884737787867324976944749980533451723996385529686276555252898123882929468903127172191806579777301993214060196965447082256317923873844261268722492882374825667981894, 123695392443150858820748899887420302518588659820412146180609987400199469246676930144168262627160486889433972128009307786023226470106702675168375871029787152488861566303728198, 290555619971520, 1161157436117440, 
    1161157436117440, 1161168509407680, 3225580504192166417836761545841063272198386497346, 105630973102145, 188397414113883790944883745947744104877559658306, 1161157436117440, 
    2923036725865007830418698853551010946560645151554, 1161157436117440, 1161168173863360, 51381112940410979637645725469671315784408775490, 51381112940410979637645725469671315784408775490, 51381112940410979637645725469671315784408775490, 
    2141060067972986641489956183007052683065088594824095171203612775271352712463195535062745330317578564, 567434981938112, 736462602474296063222861846574931243388519887682, 571833028449216, 580629121471424, 17127037647020871812872020370332351676010216258, 
    35193239371841, 3957920449257051350869629794887795358285594409659868359683118389921524965577106052655561157644413600042373184682157620347167973094132456214706819939431324339143042975515275846, 176343044600257, 51381112940431748825079864780187689578129275714, 51381025828145817064833218156288187045467142978, 567434981938112, 
    571833028449216, 583925460778860723712888219525864395468814475061014398120264503191941525646800522047019333708738629, 35193239371841, 989143293765245393976718131553508388763519527498344923943944473277145124123097435146742168914475360247004159232789782096028760780225773969987304005057043817195229737572927830442869366128337627008365389322852075485340273773509918802639558497716812610967437313246956553, 531566814649450785657876682453298301676521680971546044596409420600945706501360254130836312353876911172, 1161226155594176, 
    976769454382615135350586901657136576064305691034313659323156455086169285251163600088220770061581100593464583926644902819689318865075084429955017773474504395754676985331685389832113485621129393935197787354593647750867930255422654557102350047035303598114210312245997512, 15015491880075510186898946866980240133138633850871926095099288192389851994449201877649744225173010095748661848615924222253106358379004727278239349074585512555989448155036864613347347003760192815302734418907459927754276315680904893088682104077378449875927560245997512, 15015491880075510186898946478850717057961400063627056487701903850262718137229767377201858678490527568698155467293377528787116602074766020759779707580895906265718986459175409758539696654752052324795414035211558400365261253537309108032794607425451499045519361249356553, 176063737500096, 52402270903687832003459046407038011732079721442405875854673365904038467304407418606020294890420466254265969092892307978971229242760664537051494463844616110615148762111925205950594372565629598276254097394349124474961248803724041637758922584594812245611489757207178970228772039149725210400647588315099755907175917560899165175551934193103418447904450960211213916033562019802622923, 961754420725220818364191558845582782040999896248880979041833363901559953222349352541973983353274905382951906843801977850719338162759992833555970314810843774438102246189696668525848963685816347571544563227793544427890741355726547513858136061519974465949139464245997512, 
    1161368023863744, 1161368023863744, 316943093993920, 316943093993920, 5784197299287483405454868079360132401368576549115071685582968012492842342059076906000770205466505842293403811261188302802503782738688226918386777461711733991070754799572754042507689734775535297068161887752486061581012383255480926454329665366449327889869986700283921820453357666897964281765686936849293669370384799413566963125889261480988672766991112084865363051733336392812477810799576271855428323871085555249067171790474317767651141747075384638838638648554315524636917338484291559164372894055906226639178118400265289210115902974204872727299679206690448910291846713820557707606247123059342114923827733314810791617076953708865881472487563293608209037648373724238, 123695392443150858820591777138244336291396694676127880012348308470959859752155427914204236940043264620579573075714916022463214538981245759271343917953645874091684923434857030, 
    316943093993920, 316943093993920, 4158272566466870091383534110015526725823507602172611964368012567025801406072639159820661693913391619540947265344009786154778590961934249926081701457506221329963200667210216006, 989143293765243688632026922530777792841446026963649081106416406050239333336712610034378346344631689209793821883085572329629512672046169742176004247802535167204998903681737043459931891794273465489049661539110458492570131702576101957658684932381998383118680065246956553, 4152865708507573132457227681927858014687311080567740603537893371855269783361387067413492509978240068, 4266660209495474733312466059838050347583873651257638296144116332773531361072192919584455431986455620, 
    4156413866686451810832326196060372877436855084232437382805955175078775291917310401518936410690004036, 4221294472902549454359975158907930339014490239242131417826339713726369959595191814914500760060666948, 4250186618073418690953369688818056170020323984299326123047771839513984505325754825108082050070848580, 265751471920874772371720477642306534438301956038827328422050907019478904717026909581021913713225344068, 265864506102254802529986501678086551913671797550287714252388335183017412147301808937363528169209308228, 265755020079053651050095576156439049301051500042492025201318968822702410225582832915127357613937108036, 
    265815845647351030204276783781755361031961649759598955067185468150713146711403793204285226343657219140, 265848285950700778119048314482005326877301533262821068420416549835808012166259162198186791300861633604, 465064695206726218478724981095366355711890050145677011634251007576576037917499556398121780514698312260, 105630973102145, 105630973102145, 387105950017857, 
    1128932231897921, 567503165068224, 585095351112640, 571901211579328, 2923103629376994606508239527889940007942243760962, 1161228235968960, 
    1128657353982529, 1128657353982529, 1128657353982529, 1128657353982529, 1161226156511680, 2141060067972986641489959188413954655150199938713273817546691263398928877434847813312017917561327940, 
    989728515036096, 567503165068224, 580697304601536, 571901211579328, 580697304601536, 567503165068224, 
    576294828904896, 567503165068224, 571901211579328, 106109457273280, 106109457273280, 106109457273280, 
    106109390164416, 2928712461445908185002432439366369227910974290754, 176476054884800, 182710528180985336458924098297377327399980513858, 182710528266055928189158714163220979257922566722, 265783407324362814692514333977381485969820436219451306309220949869568685688740570863550041873157023236, 
    537795859818752109918893605057614489715581452022222894160747114316220870257584847473373096984006796356, 145689729307072, 1135254622716737, 2928723415815873190407680633916649592034840052547, 424836833743296, 283815877546432, 
    283815877546432, 283815877546432, 424836833743296, 143379439555520, 72709645013440, 4080951628232876772103526134556496487211884578405472854500835915091350203685798936860833433391894517810946657876987289089512764174869998482330808486091681925941146805765925446, 
    72709645013440, 172497874826160916349374052754890674445100240146253624283008677511187487057180548827984668552108177090104038725564842684561086220838323431766585100947228412751333704308857258922400509722509993352677104317357986441126903521921365029141177598712746854043110800407853552446636589970699055944573925332081479411194798870086588157676925855980405196264232322925052058089718989135303764410815178914986818900438954990467642711700685757326322518433821623702403035000671958873909724248872892070336609937456899236140927583126747012124197463882459179801642783344556401644816323246760546075248113122967903525303583150371971143980890701977497367893119026044451186388559, 143361857032640, 143361857032640, 424836833743296, 283815877546432, 
    424836833743296, 283815877546432, 284099479605696, 1128657622688577, 1128657622029249, 1128657353982529, 
    513317857966737387904301874424141937318015012636919573060243240994170094627232533620633204468386808825699707650318627423153498072518257556550430966860996788068673751340614, 265750998701118393905084722680686169349901786447086705643697080014675192465671738246124622795615166021, 1978673462481190782656049655726538460145055812677274566479324212850068932752436812788669926156118293508272331000515451604218169827074560787036764980571330352648230325958202950, 75192404545984, 286157573329344, 286157573460416, 
    75192136110528, 75192404545984, 4158242433965077256442002245306975966697131435609321918454730928296053174801285614975458634365205846937897431057637918943243794182951615716963834785323680186064720867543216710, 286156634722752, 286156768940480, 286156768940480, 
    286157037375936, 286156768940480, 286157574246848, 286157574246848, 567773613789632, 567773345354176, 
    567773613789632, 145419146367424, 286156768940480, 286156768940480, 24263297898931498902744564851690167847859815235, 159184516551616, 
    159184516551616, 1003746885637056, 106109457273280, 106109390164416, 106109457273280, 79735003026368, 
    97053561801634534149586123715437357475297246018, 97053561801634534149586123715437392659803552578, 33218902561492904735556846207601157986802786660681478854088017599573142546110727285950771895572126340, 290847678010304, 106109457273280, 106109457273280, 
    28545062765744990430701354142192811976108815170, 106109457273280, 28545062765744990425739920254204479834328939330, 176476053967296, 176476053967296, 176476053967296, 
    176476054360512, 176476054360512, 176476054884800, 145707311829952, 163299497874368, 163299497874368, 
    150105358341056, 150105358341056, 163299497874368, 158883868840384, 853797363520448, 176476054884800, 
    308439596143552, 990140429243328, 990140831896512, 990140429243328, 567916018799552, 736462602495231484018462085951625254305448112962, 
    585507265319872, 581109621461952, 581109621461952, 572314065310656, 581110158332864, 581109621461952, 
    73120752931264, 73120752931264, 22880651877387912666330838747468919551335348034, 265751028401102427289069007543257046162199885812139376981243710031840842287399647952427409949806817349, 265751028401102427289069007543257046162199885811585350959531095427585587026657425252395646694360084549, 145689729307072, 
    145689729307072, 145689729307072, 990141234549696, 4158242378682424545877174067376945974239547267698697873326787519808434219117271852378230984684694805248724064964951223756716735222699614876508191190749530547597824987792142918, 283958550204864, 620836638035296940978642054847794999380553518048013198747585751226279636110327378989643700503594678268771397552726055391547320708401952599987801909921321524012468218421024145316991048129478768752860690562434337322372143124990786164340443179675938878469124293590239469629224262420360546671614999504640200823731069188949766771348791608416769128123423514777540690050136107376771935979660756601638323965854003755105368825607040107243161696295725729151288489344831700971701356738874480711147348579877660459971398413, 
    283958550204864, 60383859598390094747867247699644404364181302628185540619072920869882325368978588480753566178575452074978404215883638370926341142928659582143334714929316548462999841558086, 72639716594112, 531501997402235371604536482063022968267842695623939605455300626026834323663529161405359765695133557828, 1126458529956417, 1126458529956417, 
    531501949882260587742184532681616481834152658249993574006296330440557833688825337994125483863769892869, 3957287485226948974103744061753945314353862245461522523274866709018383083513226931727335379675683658574435213199391852306695061568797308891377646522680459389903268938471946310, 3957287367290623198430576803805780844030012398690889939847578035126115638576355549661947710495616287923144332728583030407153477089393724349722670032861095030946969343860586566, 72639716594112, 72639716594112, 2923059048494292943061287462768476377696088688451, 
    531566909688434973216618815775582182581406202551230366326597174477014622771159714319274303681260154949, 531501997402235843673080803229557732773481215950084082353306802115131791852314626378355749407695217732, 283958550204864, 283958550204864, 2923059026716221460121225801112501502062923155267, 1128657622688577, 
    1128657353982529, 531567321529194402003021360818622978727958829399911710536193024411891792196006923315195789075376415812, 33218933990109348390486863965668843510242328626201386547243596379522067495145443701425615476041601093, 265751028401102427289067248950901754422189025868683620244406724336805344865485139577384502017804988485, 7774362595245726724594926067066136785475014222102819087314190605825081420594613677621604623221877607431375849865281641798329817420368239172602887953170065046403609331228230, 182777604888390466720997638170411646385955812162, 
    730842809590337560534670766474807141481364634434, 182777604888390466720997638170411646385955812162, 145277412446656, 568056813196224, 145277412446656, 567915481928640, 
    531502440922011507987687986801948015492080352536889840451155839060349930300756034296296476719949456452, 145277412446656, 286156768940480, 286156768940480, 567768668225519906783121689580456505943387169180555699859553756926539504832913868936959790494773317, 149675458957760, 
    299351712993728, 299351712993728, 535686733205322738969914417874735183905193936409054659384936919714325449949038613253422798417936163908, 158471551979968, 158471551979968, 158471551979968]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x249249b4d64d34924a30100db6924d3c000124a34db50060299c8b64f00c04d34900200820db6904000124124a34db4c060261a4930c049009249b4934da4924f00006924e26d36030137104d27800034da4100005106924924c30124024944db4e302009a6db6dbd1c00009a49b51a4de0001124e44db6c06024a20a26f000040040200001a1248009a4a000104db4d860068049269b5937986034d34d349b4000d349bc9a80001249b4d34d36c24d26b24b30804d359b4a34300964d341009a4820d04000924924124834c04136c24d20804934100d249b8e36b272000049a6da4934c20134e34d26d06026d45106028930c36200024935105246d642201809a6820134d040249c0000d34c30a38c001baf4b0209209a49200000061840400009248289b6806104c05927800030d30da4e2000cc30006c3cc30f249208049261869c0004dc4d20924828030a66124d840279b08049a6800027930c34d34d34000830d049bc0009a6124834d04006024d26b20804b04d34100a30800d3400013c904124834c041b6824140804b26204f400019e49309a09389c6e34c06027349658208060269249030c0a02c98610690580003412916c1e0200000000c3000003794100000684d259206181804d269261801a01249b4136b00026984924da4820124134db4d06006c34d00004f24106924c20126986136c00027924c249a6d64180da08029249249249249249a48249b60041b6c36c36c060241249a6806026db0c248248269248001b6c06036c30c24924924da0904c34c369368001b6c06036f30c349248201249841bcc001b6db6c24924904da69041240b6db6da6da4db6de0000db6dc6e36c06036db0c30f00006da4c30000db13493482080501b6db6d86036c069acb24924924924104164924924904900020036820000924924104124164924924904900db6db69a69369a6c208369b6db69b0920db6c30c360001a6936820c2684d2492492010069b6db69b09200924b8a269a6db0180d24924930d041349041049024b6db0c06db6180020a20820000db6c301b6d86130d34d24900804c34d34924124130d3d1249b0c04904100004934104004104124d241024824b6de6da4dc0000db6db6db6d86036db6db7230c06db6db7240180db6e36db6dc6c301b0c00db61b8d800061a4dc6c30986006db0db6c06db51e6db0000d349249241041c4924924924906da4da6db0100a68db6db6c30c27a24924920820a249249249a4820180000826c30104124924d24104904924924900da69b6926c208369b6db69b6920db6db6db6c301b6db6db6c36c36d36db6db6db8d86c30036d86e360209b6926da68269b0db69b69200b6db6db6e00c069adb2c920100db6db6db6030124924900134d349041049024924b6d20d34a00006a20824920820db4934d24124130c06db6036d84c301b6d86db6134930c04d34134d04204134d24d241024824b6db0c06db41049a0000a6c820db6c301b6d861241249a0820820c36db6db6db600092492492480012cd24db08049b6d86036db0c34db0c06db61849208209a69200048049241241a69248249248069a40009a6840d341049249241b6d208061a6835124904924900000824000980104144124924000006120820805104924924900820004800c009b8d80036db0c279b00059b6dc0986dd6c36db6c20db6c301b6d041a6800024da0836db0c06db4104930db6db6db6d84004834924d24124d36c301b6d041240b0c00db6034900024824920820c30036d80c26000924924924800124d24930c04d24c349a4924924000924924924830c04db6036d80024920826920986824924924802c30036d86d241860268209a4830c00db61b49040049b4924d24134924c30136d86d341240b0c00db61b6980035824820820c30036d86da6186934924924800124da4db0c0cd24c34a24d249241300059249a69209868349249248028a69a08269a49209a6924824924830d200049001008209a69a4920db6030db6d861a6824924924830c0cd24136904d34b24124924134104034924d241029a6820824924824c34804124124136d86db6db6d84c341b4924d24124d2408248, 291388038583232, 1134988334732224, 1136981266666432, 2928723418532825578142970300950325520779909854018, 16690536445057661165191683008790748473017419616310996966940628220266094376395934651526429639945380676, 163844958327744, 
    581659376751552, 16680407017832143021476894212483785717218805055230324939541377458892788670694896814148244508755256132, 581659376751552, 581659376358336, 581109621461952, 581109621461952, 
    581109353026496, 581109621461952, 581109621461952, 581109621461952, 308431006208960, 581109621461952, 
    79306706391233, 871656105448384, 580629121471424, 580697304601536, 581110158332864, 581110158332864, 
    871656105186240, 290564210168768, 537796105275778724399705667485149936879420477719816759711258088036232295289058162997409423248856556612, 145290297349056, 3958006977665095717692379947811380348004870243827256929399279026976485368581477086369117068984571274005200642565987185581755663836646016578422532699611733699329175149938205254, 168242601661376, 
    11774838384775837982664019748807941481197253186, 75883624928192, 75883624928192, 79457977373632, 871656105710528, 290564210168768, 
    943467958637504, 564786192405865450604643984021517682087009952491083134461009005536047634036238306109657902168254293060, 564786572565669386325938591192582769515773313020731984302508404521864708589214901668488033490824084036, 564790247443784169093990425359048927817677437929304108461026521568842124894822877744320922113233232964, 137871296185277590929123679983784973673306662083472355347340275999265855883041803027702238362547141, 564789740564044329282822216364877668663197681671195088099973548057866371582263865030427771488670426180, 
    290564210168768, 871656105710528, 290564210168768, 75883624928192, 75883624928192, 23014456880290496075264292297925528528967742274, 
    75883624928192, 75883624928192, 81450842198976, 79457977373632, 79457977373632, 23014456540008129154316157317313539622618315586, 
    78082581074880, 6740821879975988026521245911734531044613713152076273354585977065720416950637795508775963741998921209310499249565269567127029317550707705635146231944479863168224143113875313178697021437391925721569569675543098646888947832902392959916761714590352953218828581772369738397425053172617395687841223158811185634144509770316840436210988052398617161386680695914317377452372064994630347362502754515783023063659803101989981039031175809789388115285139339043819674148537805345856332049346423881768576760250607317181773735153396582613609025019905176585883221839150387627734556367978159985696697313760646857416146321469016846543161661330263120791912268680260333888379577892352488579802251080234325973572485409659578855299236678680442686685012288799666289289479522556410086250747000444641408186864196936922838399844806706448383023289827448656851103124896408664773821011139567150721048857367646868254469410797002650120191811893048827800572627238510452312354124387829210988039641734416328410331142722744788701649327689607026460103686207349591061478045310785122385024541524616194822631794721433692445488853791139475054328587560353002992736012265990729527306997401284327050311611510010540013264831409217177426272619795018559824709586307811267743404509594607341885982841708043615865478064964100666155821029817490585295523270499686792078004476829168077451800850583047802681141213663348276410643147614348460378111968673808690588010564803678978744461924528742249391298844452394166594830449970265846470326360571642903355705088628848903729975786059502519845443122763033833194458236036610547222268328118681528758757756505258956683722908019926564399026347166768014765123794508746287547339716235882308157772147059956431779838997258968, 535719680387928928508263128705328054701998740094722918614775471478134019314956006633243009712668386372, 146252369105856, 146252369105856, 564790247443784169093990425359048927817677437929304108461026521568842124894822877744320922113233232964, 
    564789740564044329282822216364877668663197681665740062384672941471641928238297891468518449913900934212, 581659376751552, 46028913678147772768432850737842545414761395010, 149825917031360, 146252370023360, 158420024955585, 
    149825917031360, 154086524588992, 149825917031360, 149825917031360, 171679381722048, 171816820675520, 
    158420024955585, 158420561842881, 145290297349056, 290563405386688, 580628593525313, 286027785704384, 
    286027785704384, 286027785704384, 294824012944320, 312416870077376, 286027785704384, 290564210693056]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x12522524914924924920100524924924824836db6de6f06d84924900100820524924924824810914924914924d24925820812424924d24d301009249369b4db0180924934d24d600209249349a48048249a09a6f00004004020000120db6c379b6000124924924804802524924924924000924924924924814d25924934300564924100924820524924824924810914924924934924924814934d040249208124249b0000d24d209b6d86036f30c20920924920000004104000020924924926824124d059258008209209a4da000cc30006c3cc30b24920804926104940004dc4d209249240209a4124e280259308025249249241009a09249249248248149241009208005249248249a4836d86d86f36d84f300019e49205109269e6db6db6c0602c9261b81ec1e0180000000c3000403d80603cc0003cdb6db6d80c04114924924924924824814924c208259248124024928a49249249249248249b40041b6db6c36c060240a49249040269b08248248249248001249040268308249249249209048248269368001a6986026f30c249248201249841bcc001b6db0c249249049269040920a4522914924924920100524924924824834904924100920524924924824810914924914924904924c208124249349a49349349301809249349a48248349049041008209249249a4824820914924924924100524924924924826924934924902926924936104114536db4db6db4d04104924924920524904924924810914924924934904904914904104d2492c812420920924920004130804000020924924826824124924da4c00820004806004d209861b6e36f38c2000cf36dbce30a49349a49249020824924926d00004124d84d209248249a69a41248001251388049249241008205249248248248269249049008029269241069241141049249249a05249049a49a4830db4d86d80000004f35984920510f36de6db6db6c06036db6180c36f3ce38030186f361b6c30c061b6d86db01149249249249049049148201049241248124049379e49269a59b01809acb6cf38004164da6da6c048349b6db49811049269801818209acb06000324164da6d66804024986da498cd00516924924926924936104134924934d849061b41041e00009269241061241b71b6db6c06024924924d849005a4924924986d24906c00824814db6db49300009e4da6d66db4c24934da4db4906db6db6dc6180934d349361041b6db6db71c7824934da4da49049369b49b43009c6db6de6de6c36db6db6db6d80800000824c20100104920924124da6d24c008040000040249005b69a6934c408249249a6db6d26d04824826d86026930824810000000004920904020806165824904104da4d06180c301861c0100104100904186030c06186004000024004900800804000020924104136924186030c061b7804d04184da49049300019b49209240001240068205e59a68619048249249a49a6d26c04824834c208679348248108a49249249249048048068008248244a48248249248001041248268368249249249209049249249b4120904c24806c008249861a69a6f36c269b69b69b41208209249249b40001bcdb6db8c249209249269040920a4db4d64920000936da69a6d0602cdb49b6db00009a4dbcdb49a40009269a0924d200000040041201219b80379cc00010006c980c048049259349263005249249249b4864934d24924904934924920000924924924824812534934d249349008200008248204200200201a48109249b6db69b6d20b24d24964d34c24b269249249369ac03c02693cc310209b49b69b4d20124964d34d0c014924924924d20924924924924124d24964e04c24924924924d20924924924924124924924924814924924926d20924924924d241a4924924d248124249b6db8db918602c934924d30d309249a0006db6d86de098618cdb91bcc049249249301005249249248248259349349341041125a6da6da6c24820000806004820424904924824810926db6db6db6db0b24d249251c58249269ac114964924924924904914912425924924d300209249a4926d0482d9a49a59b18209249a00041a4e35921924984926d64802926db6db6db71b0b24d24964de4c24b26b26124966db6db6db6d849249248208209a4d20100800004d049209208249b8824020000020100024820920da69000061b4d34000920824938826104104d26d26c208209a4d25984db0c36db8db6126820006a26db6100800000820800420020020324804900124924904104124926980100104920124124904924b24812534900124934904510924d36d36d360203249a6924c00834db4db4d80904924184c349a6da403cc00dbcdb8c3cdb0db6db6d84104104d2490c814924124924d20924824924924124104964f05804004004024904924124926120924824924924124904924924814924124926d20924824924d241124028a49249249249249248348249a6986026830c24824924924924924864824924830d86db6de6c240a49a6820924934824924920924d20820986924930824924124924d20c30c369349361249a69801a69b6d040920a69a0804924104db0004dc48309249240209a6134c000249a0c208209a4920100000004000000924824b26826104001965800c208209a4e2010cc30006c3cc609a4c30000db49209049200019b4d30534820836934c24904104d24900800804000b208200001200248108000009248205a6830824924834904104d249025109a68201248041a5124806134c24924904920807330c30236f208208249248040340208061358249209249209048208269388040000001000008269b41349b61a09c8c31800338c2c124800064d44c14920820d24d20924104124924134000804105824d20020d24130124104124924020020120024814d20c20d24d20d241041249241248208249248124209a0804920100104136180aa0924924124820000c00030d800208209249251001008201841009248249249a61208209a4e27100180034dbca30986104d36da0c20006236db6f009b6f39006230c00800800000920420020020024804100904d24100c041261b40001009041009240309049b69300100069a49241004209869a4924804100944d24102420020120024810828820124804024104986d04024924904920900030c30036000820824924a34004020806104024920924928904820826938a340370079873470261b83361b7030801001908f36c20000004000180000104964d34c10824124d24d20104024124924000104904905804004024004900024124124130104824d24924110c24126d24d20104c24d24924020904924924812400020926da49800049200041200008249b69ac020020020004800020920da68000048200041a00008248388200009049b6d36820024124da4d20000824db69ac0209069a69348000269a6da4980006db4db49b0000db79b79c61049241009248205249248249248241041249249a01241041349241249049249248141041349b4f205225109a68201249841a49249049208071b0c301b6db08208249249b4036020806135824920924920984c30c36db8e361b6c00d66db68269b41349b6da09ac164d04024920814924920924d20904104924900c04d04184d24904924124924120924104d26d2481491242c9a08049241059c0805954d20924924020b24124826824d308208209a4925900000005804d20924824926b24124801924f3c8208209a4da590c9249029200201215351a0100100100020324020124006804004004006900c261b6db6da092103c1b75b7b30184826db69a404020b25965983408292c924d36d360201359a6d65836824934db4d86908db6db6180db0b2c000820c3000003cc36d8c036c66db6db0c06d8409293593516580c8249249a49249248048249040008060048248249249a49249248048249240008249b69a400c036dbcdb6c240a4324820120904067830de79b780492490492c9019e6db19ecdb082082492496400402080600482492092492c904c2082693696432c9a409208, 2923371238361329594247099300027507375211110478658, 2923371238361329594247108971470957921129952457538, 1128184970025153, 1128185100044353, 1128185100044353, 572854693794240, 
    150642228859328, 150642228859328, 572854693794240, 572854693794240, 80268786536896, 84675826094528, 
    150642228859328, 150642228859328, 572854693794240, 572854693794240, 1461507213920867476667927770574795875940950881090, 1128253685371073, 
    3957286427485527111778661891709499483189072249239034106659464513565086842785957174549272351145102433321328824145000197370456749242460252136184388282231779062309113555922699847, 290547030036928, 265750998701117656297987067882619201884752896315138283728167663002607021335899336179126138237000839365, 265750998701117656297987067882619201884752896315138283728167663002607021335899336179126138237000839365, 572305474589120, 290547030036928, 
    7729078731600933628437679963602718320107268343769672063058034901047075776712909962211997906679499670124561334693542827355526936696442077018182677612846312680443715998697031, 1978643215484742977146512441229227506897933497775709479222125768714718651725354259878976391944148046632322414905211419051732884829148063524715795031670908784249484761207129671, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 531501965722251543103487040183268616042994127252718152040478862918073334657319012107592528450236412101, 531501965722251543103487040183268616042994127252718152040478862918073334657319012107592528450236412101, 
    572030597206464, 531501965722251631616338442218049409810977256899298335935140467231180271693021930836419023112548610245, 1128184898717761, 1128184898717761, 1128184898717761, 2923036725960399449600350732219156686957437027907, 
    1461551814199029293895700872037599829402830766915, 2923192831719176615439906799426593603772754178882, 1128184970025153, 1128184898717761, 1128184898717761, 1128184898717761, 
    1128185100044353, 3957287669502457950539484277213028230953335791663006307413244280538695218689143406849385456874773795973008670212946788459388727336620170861814593323102110446862555034442265158, 1128185100044353, 23014456880272322976838298515527418596657476418, 163857843229632, 581659376751552, 
    581659376751552, 581659376358336, 2923036725907292758956353292997458250970995635010, 1128253685371073, 80268920754624, 1128184970088641, 
    1128184902981825, 1128184970088641, 1128253618262209, 1128665935122625, 3957286427485527111805477507569384677388244432552460802929910892738581610295799659392147100012252587307884841247336294588617620932283950096630848778158173690590703555155294791, 1128665935054913, 
    1128185175747393, 531501997402235843673082028467828721302319981674545662624807775116897818018486351300632948416005644549, 3957286424721394476599031345126779234910548776319919847528248588369111148862390617583182402440625761290423802552966331415946039093288530486429036556204573919559899340701361735, 1128185175747393, 2923036725950097893335815177058518097142871008835, 3958041221582916183306709044732106390945557888734870057655767152005854081573793393005170549248339425444227842172914808065532931110556307740378649337560953492185452165044600390, 
    1128185175747393, 1128185175747393, 123665204423862013091590996083691866570813393571676937481763223356029308536766292539942174095644755554184668085651853310255209900726746569045312751713607100521005069786641991, 146243779563968, 3957316619184925684297189135165343748734485785569124676029570219791433971881285648085489929242555540140270568007551389034031562785650291705819342222639351911062452182223642182, 73671649661376, 
    284777882194368, 80268920754624, 731108332973989501280306833880117991409197298498, 581659376751552, 365421404790025805822199550855930028100849763139, 146243779563968, 
    75879329960384, 146243779170752, 146243779170752, 1128665935528513, 1128665935528513, 531501965722252339719151417920491634045928517979389793547524302420702802677503249413493619632695070917, 
    1128666136855105, 1130452710723777, 83850924396992, 531502440922011507987688872858590831898367316546058926431842159963971489140745710554143137811784385413, 3957286482768179819956743135535386095930346763735873292166478601369796790101300072893659518088668294203269792455656948398523568201146461039653250299469513779227541883091648071, 531502440922011507987689092682635243365879351388973446728986241502240607062889814055478228366189773701, 
    1130383991640257, 2923371238321452602255508810783220562219547767618, 1130521365190849, 3957316619184925684109479824141464766515475154415460408195524067574680411373838615097071421540446546556419967924395455375767303830098161133076735927996442305496657009588514374, 1461685619180644028015341255356650256100487332675, 1130384203197377, 
    3957921577023166580744291592952589360221301937869783870707864548507636940187743053420706668520819636249049469940980054381321318803450229045338191976116352328084308990296584774, 1130383926237377, 435690216100288, 2923594244580123466427191645298702887567025517378, 1130452711641281, 83851058614720, 
    149817327096256, 290545957081536, 1130452710723777, 1130383992164545, 1130452710723777, 79444287951296, 
    149817327096256, 572029792162240, 290546225516992, 581109621461952, 290546225516992, 531502440922011507987689092682658172800521288335407949524201226904195707996731690160918893586232963973, 
    83851058614720, 290545957081536, 290546225516992, 960962621521537293379978066036846006136302196138644212446272102213445698559557918723149746590774080304015590202577841806444910174522418996274607531318137521328568277444690775027369329616726359310423866470854413212749056931611157894831156996330473260828328456246191112, 1131002600911809, 3957316619184925684297189135162222000183942661781737445987016028809626878194468017940148121053556827036465052928649905879006777733221190910374632680133100823280561416835159622, 
    290546225516992, 725845724369856, 567434038743233, 290546493952448, 437687644328384, 437687644328384, 
    11596431782481520859574259147544646405630997314, 531567321528223829083112490188317425117992137813409569224668151583544074859035013571475722929299485572, 149817327096256, 290545957081536, 581109621461952, 567434458186433, 
    290546493952448, 3957318108591727374544439760292094690229662872781875419598534552520245461287320038283648558723622977079539291041913331808525126252171890820723540204155880299594483913071742534, 531566814648484225306161819782817088462783182624643094665866621105900425296436751915818071467744259268, 708171946545857, 145221993124545, 567434458186433, 
    145281573196224, 290546225516992, 308439596143552, 1134782245514049, 1134781976873025, 291370724102592, 
    291370724102592, 290409590952384, 290409590952384, 290821908206016, 290821908206016, 150641825681856, 
    80268719428032, 80268719428032, 80268719428032, 501459318739392, 149679888142784, 183402028175797540171831498863172627440336909122, 
    501459318739392, 149679888142784, 572304670069184, 123696335928358367652635124616695946051363998779537850013747640598074343773263737992291472565102115233315432418798233979760929815691837075503460758257730071818748899155212359, 79238933844416, 290547029905856, 
    290547030299072, 79238933844416, 360713910751680, 642197477659072, 23549676764528270582390966675477641309078958914, 290546493952448, 
    149679753925056, 431154864853440, 431154864853440, 431154864853440, 712630109999552, 149679753925056, 
    290547030823360, 290547030823360, 1134782048246721, 531566814648544414059518183662259215919050899495550234557650921552115942616320921278155726433611211012, 1134781976873025, 572030596682176, 
    2923728051603203940427556977510208006710498689859, 1134781976873025, 1134782178199617, 4081435634987222247512024594046900125474848936706162436628526082504868503941088806975060679041366288760420834503123726627074120688095910526160057316002217190043466023265335367, 123666144228958051663211418310059195504788281291097087845382036321316702784936525560539310870672647462666530061747363219741616483499365996085420223186286705324282921072162887, 1134781976873025, 
    1134782245514049, 1134782245514049, 1134782245308481, 2923371239680027491021495209926182999269499470403, 3957921577023192969013089327086391147594136752317493560909618299334505113702458222869322866132006092390609035715368302261186493940395482871502400173058083749945314094480351814, 150641825681856, 
    75879329960384, 290547030299072, 4104170048216583831055539633580301494153034954633525928953554275633829302337163544843342957248315201511027636875904436266354811011160947260863713661487618624906007727092743750, 943482991023040, 4168901663976203132419678884029226468673294134181894738520170234419460060397279125816501467368985965407734898482922711258062836013301167506063553080603290889667535073374581318, 88528420603969, 
    88528017955521, 88528420603969, 14272531393526804490215961078403815500966789955, 290547030299072, 75879329960384, 75879329960384, 
    23014456880272322976838298515527418596657476418, 75879329960384, 78078286107072, 535719680387928928508263128826081008085695625160495874868197782614452078087738557032028989593403696196, 146243779170752, 146243779170752, 
    88528420603969, 88528420603969, 581659376751552, 146243780088256, 158415729988289, 149817327096256, 
    158415729988289, 158416266875585, 145281707413952, 580628593525313, 286019195769280, 286019195769280]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x229b4d24d249b4d24d80806db49269a00009a4d36db60301a71269a6804020804000004106db4820000920b259461860401a71269860248025265949269a4b20100524f26924824814920800000820524f269248248109249a69371369a7820836db6db69b0920d36820c3c000136c2682780004b24d308209206db09a09e0000114d12512524c209a48208124269a6da4920100a34d36d34d0000c9a69acf300009269b6db6020124934924920820d36db49240301a71a4924824824980134d000041341208209209a6c049248248025249269a4920100524d269248248169a79a4926100514920000926820524d208249a4810d36db6db6db6c001b4d36f34924d24124dc6000134db6124114d125a71249249a48125a68000249a0812424920c04924104930000da6920924830124986338c001b6f30c30d00d040000000001a4820820c36030d34104020000924924820980da4221804d34d00004d24106b30024926920d36000020924124c008249248025249269a4100920524d26924824814920000920800524d208249a48169a00009a6da05109a49b6db6040126926db6d81006db6ec6e30300db6dc41041341e6e38c20806036db6d84180c04924000004d34104124114d125a6d24924824812524c208249a68124028a4d34934926d349360201a6d249a6820826934db4d84d069b49a49209208201000001041a6d2482082482c9651841010069b49a49209200a4924924db4da0930d80104902926d34db4d340002269a6b268040249a6db4d80804924926004d341041240929248301249041a68000269a0824920c04924104934180db6820c340341000001a6800026828830d80d34d04104826036906860134d34000134904134d801049249040920a69a49249a6926980c04de6db6db0000924a28934000134e37136c06024820920806d84c36db0000db0924a28934040164e3710c036c065a25169a69a49201005a69a69248248169869a41009205a69a69248248109a69ac9269a4b280301a492692cd869889208248200300481b8dc6c3182492892cd889811851671c0c60196912626a269b6c0601242012092482081242c926934d26d34d00005926da69a0820db4b34db61041a6936924824804026d00004d05926da08209209a4b341860201a69369248248028969a69a49b01005a69a6924824834d249349041025145100009a48269204200269249a4810e66da6b3cc34c34a38f2cb3cc30c24d34db4924020134d36d24904904d30c04820124134d301249049041e69a49a6c00016da71269a0820d34924d241041a69249a68208125124000289209a4812420930d249800061a0024820820826c349a61040208009a4824800004d34024900000836c36920000134d069a6124d00004d34124100000b249269200000309a69240200289249248069a68240009305a69a6924824834d249041049025100009a48269204200269248248100069a69a6da05109e69a0800020c16da7120820920d349241041241a69248209a68125124201249249a68124028a2f3c9a4d349b4d34000136dacd34d041041009b40001341269acd041049040a2492c34c34d36000000026820820830c30d34d041000009a0830c30c30134d009240000209a09a0830c04d341a4904934000134d04904100004d249249040920a4db4d64920000938db4da7186036da6a2690000ce36dbce600009a4db71b49a6000db8e3cdb6000136db0db6db0000004004120031a48009a5c000100064d81006c06db79c6db63005b6db6db6db6c649249249249069a69a49201005a69a69248248125108200009268204200208249a4810927236db6e37030db89aca28208366db79b6c40c299c6e651b1030b26db6c36e38e3c03c048dc9030c36e06f38f08180e311b71c6db01b69e6936d840169a6da4924920d349249249241a69a6934c040125a69249249248125a4824924924812424936da6db18069acdb6b200009a8e36938c2c1a6934924824834d26d34d000049a6da6b20820db49b4d340001a69369248248249a6da4d200069a6da4a200009269b6934800104000000d041041000208209200200040300200201008248248069c69b69a00005a6da69a48248279b6da6f300005925100008268269a04268269249a4810926db6db6db8180d369a8db8006336db6d37000026de69e6dc00009b69b0d80030e000061969a69a69248208125125124279a592492082092493492492483cdb6d36d8000cd24f36b24934104130025924926920924834924924802db6e38db6c50336db6db6dbcd8c924e24926920d34f34924c20334d3cd24934904924106030124d0410400cd049349040860000000040008000069b49a0000000000100020006026d000208060200040000009a69b48209a00309b6d06186026920d24830c0ce361b7a04300000c30dbc124180000c302401008000009208004200208249248049049249249061809a48209005a6826924924812516510db6030db6986136d80c36da6184c34c34104104066c000289b0c06200c34db6d84924184044d34d341241860669209848169a0da49249201341249249240200209248208125a68249249248125124029bc9369b6da4c001b71b9268c41824da6dbcdb898c9b71b71b71b6c26db71b6db6e309368301a4e061b103120c1b7824da0d8cd8080d9ccdc0f06f300a2926b269a6800034d34934d340001249a69ac800036d24d34d04104d369b6934800134da4da4d20004100000034104100900104d049040b6db6db6d80204db4d26936d80104924da4902f3ce3ce38006134f34db4d34104334924d24092d3c0001b6d061a68209a6926836d86d00c34d869a09a09249200001808001000208269a6924806c00c24db41809a09a4924920030336d86de6136f0c330c36f049001861b0c0ad840920a6980804d24106db00051c6830924020030a36134c06038da10208009a40201000001b4000000924020b36806104000d60c01030c00e3623018d040006c3cc60da6c40001244920906db00019c6db05b6c30c36dc6c249041049249008269a41009204201a69248248108000009268205a68208249a48125109a80201348041b70060061b6c24900900c20807330c30286f3082002090080406603180c1b6c24900920c20986d80c60205160c30030d88c06000000100c00038040105836030a49041800338c2c1b6c000269b4c16da10209a69209241041249240209a69040040124200249248248125a682082492481242498000ce30d0682cdb0000b208200041b0c36104800824920804126d00005904986da0820b201809b4104020020136924824804000004d301041200209a0820c34004030d24020900824824804026da0c05100826da00008201069b6830134100800800000a20420020824824804104904924901806da0006f305900009a48269204208269249a4812510000826c38c34104020930c30d80000100de6da01009a8000c300301b6c00136c20c069e0006db0830d369a7926830c30db69b6920100820f3cdb60001a69a7936c3cc49280038d800069a69e6db0000000da69a0810c210269a69201041241249240201a68209248125124209a69a4924812400030db8e36d80004120824920000c30c30e3c020104824824800036d0000018000682cf3c8200001b6d86d26120024924924920000824104934020824924924800036d34d349800009a48269209069a00009b68205a68208249a48261809a48069205a68269249a48161819a4826920512510db6000038e36266c2680c1b4c36d88180db8e05120c209a69a0104c04820024008c2080c33cc04030124904904100030124d04134d06d049349049241e6c00026db0816da10209a69a08200208209248125a60249249a481251242c980004da61079c00249a69a09a40040309241a680682492480000cd040261000019a48269a0184030d349241a6866924924830c0cda4227984d26902eb0db6000e4c136c3ad8c1b1180020120924920180db4104d34338246c30db6c34924184184d34d3412408292cdb8e3c0060301b71b6c00036036e36db0006d88ec6db0038d80b26000c30c36000000000006000067269300006c000061b61b61e00a2dbcdb6c301e6128b2680002c824d349340001641249a680002c836d24d04104904100000134c04100d00104d34904d309b6830144134d24da0c04d040b4934f269001b8d04924d841a6936dbcd04902d24c24c34104104000020b20b24830006db41b4984924004db4d34d24124092324000100984066c001e71b78069001049249040003341009840000691e11b6c06100d34d24904c003369069e613492409208, 2925868921802255685771937679857906968103890268994, 1152580520776640, 1152443081954240, 1152580520776640, 2925868921786304959963762179048734015284989473602, 84680121062336, 
    150650818794432, 572863283729344, 1461507213920909015201252374224352795098672608066, 1152580520776640, 1152580520776640, 3957344566408624784345365678984872470827010303658589706157957064515098036170948400959664994411983136573324529982682738664357480481258422747004465417815801665220590805419274822, 
    589906251092928, 308706152289216, 871656105710528, 590181128999872, 572314064786368, 871656105710528, 
    572314064786368, 3957287367290624894035598852919657905840989602995591593556738405612699739242969877639360287834749370953444352674865565682576917635079948419872013644484824319903506769320130630, 308706152289216, 871656105710528, 871656105710528, 3957317558990021763896597074513483777321156805176720882992698890273639867762698338601815187996751444526582138906454889672419560626776655943359523499653547335948458782808301126, 
    308156395951040, 3957317558990021763896597074513483777321179430161425238078812544392135882582407446978645841895571704072929181978747396174676347508258625721257188210344456221644473855293480518, 1461551814199216217138443208193747167968544162627, 1947836356962666798087585008708321753582925263927133504901248269258065708390309345729541270410230877118744912568497244740574643110826078906561090458325378314676283433731654, 242005340496953503816289947997725603120450446414892547764321895260739028962725682607624613143177243272387085781302026755707210944201541590228037788016161297843887185249862, 2923371238340020255980085679411370351615220462402, 
    1134988334732224, 1134988334732224, 1134988334732224, 2923728051608375487825928603948058202307488215874, 581659376751552, 581659376751552, 
    581659376358336, 291388038583232, 291388038583232, 183045944456907182473841231752050358003379024450, 581659376751552, 581659376751552, 
    1134988334601152, 1134988334732224, 2923371270988497529402960013223026568313658487362, 1134988334732224, 2923036725907251063541363390790229854397059380034, 1130383995442112, 
    1464361729701995150169355557621560483777385411394, 1130383995442112, 1130452715180992, 1130452715180992, 1130452715180992, 183045235268598296434478295389250784401737986882, 
    1130865031779264, 1464356851413983042583976959464031448051080049474, 1464361729701995221157789170402403589880159482690, 368588132237269726995017466629531656489097311042, 1647406955442624936084612697918115873424897290818, 1464718541627830096131189960859731034631995208514, 
    1464361729701995221157789170402406967592764912450, 265751028401102427289068128361143511427579329910789064411693961554287700711724053535319004760845316165, 3957316619184925684297189135165343748734485785395155898837489954396887043002399210077174747422302319922886088184848641372505347747117663314049435674663293668504723005105987142, 73684534563776, 293586860643264, 531566814648487765820298809195371598988215372228345423683554479747612176819634522130820462786109664452, 
    82480829436864, 291388038583232, 1464361710667450402646890684193348870041497580354, 291388038583232, 1464361710667450402646890684193348870041497580354, 915223285333079095203488025763885827198239748930, 
    581659376751552, 146252369499072, 75883624928192, 146252369105856, 146252369105856, 531501997402235371604541297741964151506216033423071027041039861554875986669997478608041426112092565573, 
    3957317558990023521284798067949570812687761370013384503968135726959824672745343890117166425608325245385290567939513423486656320471684837140223329817614814080689947262719057478, 93475744388032, 300184131605440, 300184131605440, 581659376751552, 2925868931330161959558214656832395976193400189762, 
    1143784427754432, 581659376751552, 1143784428540864, 581109621461952, 299359498408896, 581109621461952, 
    581109621461952, 299634376315840, 581109621461952, 14450937376403547803626801717637761630552011586, 11596441990991628041781030195345049886107185986, 11596441990991628041473961856580039065552892738, 
    93476281127872, 93475743798208, 33316191415957783945943730355043089267597827436787229185868035704206606439317792411871186872577717124, 93475743798208, 529357198247630652435972179683705368137487671965939716500371154162029508307158807682837256473127990018716711635022387167579181650223098617840740346397658339718089156802630, 33316191415957776569872780185478023120265899966238880527979568678114380788376610020017998392600195972, 
    870968776987584, 303551453598656, 308018286695360, 581659377275840, 2923728051608375487825853648195290107200036500290, 1134988334994368, 
    14450959835018995398094983067680271868666917442, 1464361729723262950219676752785136610560119485250, 2923371238340020255980085679411370351615220462402, 1134988334732224, 1464356851435250771645864541846761091018434622274, 871106081723328, 
    183045932206741973320056547070572934726204600898, 290563942257600, 581109621461952, 183050266170738958495526025907317649314286744130, 1464361729723262950219676752785141114176926724930, 1136981266666432, 
    308705884115904, 581109621461952, 1134988335518656, 581109621461952, 308431006208960, 581109621461952, 
    290563942257600, 589631105012672, 290563942257600, 581109353026496, 581109353026496, 299634376315840, 
    11797899736279318406999543906883905466488530902591787552497645389860340643701064497195603150573065280899614033252336619886047884646746865438775976682593057259189344604818689145129681857270771148168508473696519726437308990745274456868129863800742126683853286689186173175746039826515492559378220699981129154782282447665784700984941872732859285194444751261118748492248838197176014410, 581109621461952, 581109621461952, 1978643270868171356894984430438010847598071112725106017540665695019489111898869082169883015626927444335469981305372501209951903650234729459161778191849001242204306317332444743, 290563673822144, 708176241513153, 
    708176241513153, 10325882931583270338949127202615331791917288094683748077605096329660877454863205258284248939848279924302804204677533389841603302578666326241426198113977916323027822016972569079380029185213723783881346513601234228562062730341669224002929188436566387488251492748581206347555291376598973668795747222325009410798775211659222404426117832037252847506689682887914077253435760450258381898, 11596431782520463224662554754721215916802126658, 531567321528223829083112490067564469435114015244131300595969046254064609364476617587120772653334819716, 290563673822144, 589631105012672, 
    290563673822144, 589631105012672, 290563673822144, 290563673822144, 581109621461952, 567434458186433, 
    290563673822144, 531566814648484225306161819675481127678065916616732616079050542127603407040065284823729478318768417988, 708176241513153, 145221993124545, 567434458186433, 308705884115904, 
    149825917031360, 290563405386688, 290563405386688, 308431006208960, 862860012164032, 563517166982080, 
    563517972288448, 563517972288448, 580629121471424, 2923192852774438676444060724819748139344018355010, 580697304601536, 308705884115904, 
    308705884115904, 290838283293632, 290838283293632, 581109621461952, 581109621461952, 581109621461952, 
    871656105186240, 90796691297216, 581109353026496, 163432641860544, 581110158332864, 72722462806976, 
    82068512969664, 290839087682496, 72722462806976, 871655166448576, 1016928140268480, 290839088600000, 
    11440325949369034878106482813348436116993291074, 73135785776064, 145703016862656, 531566814648725572209675331654007383076271472313779253986979452823677698909761837643554197386809468420, 299359498408896, 862860012688320, 
    862860012426176, 290564210168768, 871381227803584, 7636324022167556784850685072268030410994111666068086994547516692885697546693455377114055238980715541875548143170422442172544507755306525234954977030503264656315962451531117126, 531566814648498979306709625293015196780908247145655144260271058517068808662899308698057115007281686020, 581659376751552, 
    581659376751552, 580834475119552, 149825917031360, 290563942257600, 290563405386688, 290563405386688, 
    145221577872320, 581385035453376, 581385035453376, 145221577872320, 4850287357029081907113194342608390875253802244502402169044582776359321290648215649155281463286073656860678814575199403924116861470989809551752014687179887422379301813807785629237883988801578879886887275475209916928176762027762898184757009248843031552258155152158563244456153199341682819936790169887138727933387568259037508620987398057058928844448428708707438349334562826829279550260138995591953864009853636824284527800644780315486602008215473371501110037775189563224688979855206736235612614130206918836651341, 426765274059712, 
    308706152289216, 308430469338048, 290563942257600, 871656105710528, 290564210168768]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a498400033cc34124d349600049209209249040248201a09a0c041048200009e4120936d04024d80820980000f20904c34d34180a209049ac8201441049279a0824920924800824824826db6db00071e0924d341049241249349249049040361a4000120924104124124136d868209248249049049049000300009a00209249a6924824820924900100dbcd04924924820924824924924920920806826830004124820826924824924920926920826000036824124924926c248249249a498cd040a4934136db0c0098c8269a0000120d04db6c30026124904130d34d349049024b4100004d26104d24004124924100030d34c27900820000820020104c34d34924130c30da4da7984d2490248, 1130383991181505, 1128185100044353, 365399103964897076967743171740240873249883321154, 4153049406159124849731669713328262698878112008606895405297787329162115395083023393932825672345943586230696892378070418147771901580291190239938555485070105537807488157761893958, 2076195733907563424423218752919705972513283005990311738559370344476956089397873526294484106327678660, 354123283435968, 
    283958550204864, 283958550204864, 638763511499107679325966391126393200634711396606467059220997789302805842380876417924522708548251717, 91366501655131037985663318136427239530093886274, 283958550204864, 3114332582089866865587314485581906852615126420036066980425154611558337586783094927486385258698720580, 
    2076195733907563424423218752919705977980083346507057434696909808961440783292019391603307764179328708]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24b269a69b0c04904d38db01009c09a69a6c301241ac980020830d800000000001800019b91b6c001b6000184986d87802524934d34d86034c679b4d00006984d34d36180d309248308009a6c26824824d44db0000180b36d3520cc0602cda69b0c06906dc6db0000db09b69a6c301a41a0c04004100c009b6d04db6c30000036f3cdb6c04d04d65934101b60924d34d341013609a6d36000924135934d040060249b4da0c049061361b4180020904000100124186186d860018008000040041041000000001009a4d34106924134934d0403cc26934d041a49009b6db6c00036c2cdb7336000db0b369a6c301a4135a36c04038c26da69b0c06908836c3cc00036c261800361b0c3018cc36f38f301bc126e28d001b8d04db4a26d36224166d34d86034c6cdb6d8003cd84db4d36180d20d0602092c9b8d04db4826d36e240001879e6de6c2cc24930e36db0c00d8c126db00001b0c36db6c300361a4d80020926da6900000036e36da08001849b6db4804924d24d36180101964d34000124124934d860248249208261a69b49209209acc36db6c30036186e36c06000030db6db0c00d86b26180c36f36dbc031800de7236c36dc0db6e48e00c061b79b8de01349c6db6d86006067934d00006986db6db6180db0926830904926d2682480c800004024101980036186de0124000100820000800920c008208001a4da59001200000001009240069369a41308001a4da590db20024b3cf20db6008db8e3c33c90492cdb48269009200008249208248009241248200000369849201240001049240208009a6d248261000349b5b609c7000db6dc6c36d801b6db6d84920424800020120820920000804920904000d26d248049000041249049200249b4920984000d26d26826db0036db6db0db6006db6db612480, 1128322409042113, 1128184970088641, 1128253685371073, 1128253618194497, 1128665935054913, 1128665935054913, 
    1128322408978625, 1128184898717761, 1128184898717761, 1128253618194497, 1128665935054913, 2923371238340061865343368227926343987563549766466, 
    1128665935054913, 1128184970025153, 1128185100044353, 133816258058848940926468124843190183060244707070977878120964413137345923864021859638157100446900484, 66441797783171491808080836178675739982439706226983392600694744699229628488636714238991870945684147396, 132879538548455479010670491505896146271138793778095168540268361923357752780640185758681932700500156676, 
    290555619840448, 290555619840448, 1128322476153025, 1128322409042113, 1128253685371073, 99891607233880560330628571490009752224789020271927948280532930767981830340586766790500337700535959700591620706731587415023122358876763790690549557391399923275061893196638955757850472610175927460922363362505436879898884141684461796698699331509206647701950518322226516002996202853265896253475926798801263512030416017404252734902822973784651862329790044249304449174201940398409297759137400934247959494502991622088102398165157462931378767927872732510290814351976338910658671719622921325085850307231805571392829998973771898161340013011052424548340506161340947804136833797584415997097072529070816738017902693145072242914697799902668653894188883221804152618649181809569817156685324319020611505049568063719825440158923109198390984633226971367854323487534578607100189715335162108334932054996527413961140200134573670325492896268298686867312748584210466257588137918018805886424325434982614645604707021991706860099860807166487056153703998259729256643436674809299984688054209379686336449396797452720484085861807093898223827893075591290047923256046235208496528180170526639981746649352615224740741023254721522732343108592715139929890269115325661181230403475468834474406296360258598043352804656624596599882059221928116026762921657264440775042132, 
    1128185037199553, 1128184970088641, 3957317558990021763896597074513483777321156805350689660184779155668186796641584776610130369817004664743966618729157637333945775665309284335129430047629605578506187959930150470, 3957317558990021763896597074513483777321179430508008949843914401840611926891679826522145216615943444482926970830029219585733195874021530996831939694250207091012304685431217734, 290555619840448, 290555619840448, 
    1461529513368780940808987017555877737785634853699, 2923371238321452602275896138018807016802232578882, 1128184898717761, 1128184898717761, 1128184898717761, 1128184898717761, 
    79449387438528, 589639962596288, 290555619971520, 589906250568640, 960962621259340297057677422063182476857708814791000968182031025767761290532114054662934279788436017963666500033200301788866773997472270197641447516704438617612315754716475510308692333129850293380266692545289165189736825254535594466821305412451460978583798281246991112, 1128185175747393, 
    1128185175747393, 3957340674509873768378188911914518212778801862219515202564758153999156833648264956248390091894313399019976387632674268808101369649183063890375506523245286460653860320207435334, 33222925915530249330393399661577410146221186406382724844132034808863213295614335035917564742207594756, 589639963120576, 589906251092928, 871389817738176, 
    589906251092928, 290555619971520, 3957287367290624894035598853668097132687774399588490607998728059317599850749494701903335639326607307409515041786847820486116239838392326199466720711843195112146987716955387974, 871389817213888, 362919376458176, 290555619971520, 
    362919376458176, 290555619971520, 362919376458176, 290555619971520, 589906250568640, 1128185175747393, 
    1128185175747393, 572314064786368, 11908007530436053810993964339550845021140997921401489821610122258966937756248230340407420845976550139534016306241194440686255282454902209499860554368512687680045642404686985887704831273274834615507099618147273670620964786414560262975582402050980507387419745571238920956232656817771926423556035064731113940124869762048360666906187822026842386038939962384230422701451460528357877451171588891843796123898478744228834471175296691452019882893694959339391779325088097168372482537624046143794535302669631373892573514744325406142226457082666863188835471466619981883580558960059056382014969911656343765695794231181420200500130664191471055499789044762554427190203702110082941182445747351059828373322568226456531725393211783153960840529795259415815418734824402354712457959514614696929377722723462178179443171913686244764879179915903000867826075583146563753425750182988320148220780878866151006211397163154764089822491314078137416299831631086034248673415500002509000926608624477641285858209226393575546250422765373621355237414972021443996227306219892155296063748934345782823445103778006691905572252636977851466397038878241731192297099822525760687511178742602531940851860469462347595611119863601959067989310549928508648233414606718972757, 572314064786368, 290555620233664, 290555620233664, 
    531566814648517978207501577992281223225957562689410909010909477636145889558758213277082330530778934468, 290555619971520, 3957317558990021763896597074513483777321156805350689660184779155668186796641584776610130369817004664743966618729157637333945775665309284335129430047629605578506187959930150470, 3957317558990021763896597074513483777321179430508008949843914401840611926891679826522145216615943444482926970830029219585733195874021530996831939694250207091012304685431217734]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24e488209302441241249a0804d049269a08249209449249260201249a69248248048000040000049208209a49209049a4020d241249a68249a4826a0000cda4982de8e38f360301029349049248201441249a6820828824d249249049021200001000040a4d26904934902a26006036f340b20a41249208049049a49208269a01401001040201249a692482482ca249a00049e0920024924db49808241249a69a0904824d26d241248009249a4800036f3cdb6c02da09a6d86036c04d679b00059b0a495c90411c8c268369a0004b20924d341049241a89b6820906024934d24904900800000820000924104134124020800006020824904d04904900c069a00048009d11b718004cc20904924820124104d04d841849049a092680002ac22800924936d260a4120934934902208c36f38f300a20a41208049240049a0024920820d060060309241249868249248200209a4924d808261a48269a09048249269241248009249248208209a4da5984930c30da4d25982d68006936a26124800924924802904820124906104d00184da49048008249249361a0800026820824120924924902820826936a660a2ca20ac220804d241079b00059b4960904824030b2616cd860452410200209a4da59000061c40049009048249b6b2610c000d24f4cc30c30da4e2590cda498288, 2923059026737561881309746369607612760256872985410, 1132583016536257, 1128184898717761, 1128184898717761, 1128665935054913, 1128185100044353, 
    1128185100044353, 1027663288900614986408985390262045554256270899010, 566266213962688, 73671716770240, 73687152268224, 144058043995072, 
    566266213962688, 566266213962688, 1130383991247041, 1128665935122625, 1132582949492929, 1130383991247041, 
    1136981268769601, 1136981268769601, 283958550204864, 283958550204864, 354123283435968, 283958550204864, 
    847200561402816, 1136981268769601, 1136981268769601, 72852317671872, 283958550204864, 73671649661376, 
    283816816153024, 283816816153024, 144040460947904]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x269a0804924104db0004db48309248240209a6134d04064da0c208209a4920100004104030000924824b28826104000d64c00c208209a4e2010cc30006c3cc609a4c30000e349209049200019b4d30935020836d040249041049a4d00800804000b209201041009240200001200040248040248049008000009348209241041349241a68000041248261040049349029209a68201248041a5000006134c24920904820806f30000db6c30820826924804064c00000104824920924a20a04820828938804000000100800026184134db60309b7000c00f36c2c124800064d34c24930820105120924104136924104800004d04824804104024104120000104160000100900124000000100004024904104924904d20001934d30984100124d24134800024924826904104da49049049049009209a41041369240209a0804920104000004030030924824020826104d04034d808208209a4925900004134004a80924824828a26104000d04f288208209a4e2790000c236f3ce809a0004137244900907104026d008008008000009201009241009440200200300040200000048049000049079b4c001009040009340001241b6d00000025934da00000069a49341001048249349040201869a4d248201001b4934902180904000954030020c0003cc36004120c04900826820124804100000100000024920900820804134100106060820828924a340301051000340249209209a8984100034136de08208289389b4000000137b38c26206234db7030831104987134024044100184020000104964d34c04024904024100804124d35120000000100124000124104d04804024100024000004904134100000924d36924104120924924900004127934d30004836d24d24000104924924824000d34d36924000020926da4980004130004130000824a389ac000000000000000026826da48000048200000300009a08389200001b6db6db6c20004d24db49a0000826db69a6000136db6d26c000269a6da4980006c34db49b00012679b99e61849241009248209340049249241249048041248249209049249041041249249a0000824904124124904924d248249001249249041041349b4b30922936c00924d24820a268201249841e6c00166db6c249209008209851361819370408208269249d4000186100c0002492092ca2098410003593d340c30c36db8de6308000dbcde70269a4164d04024920824d00124924904924120904100924c34134924104104d24900800030d241049049241259341309a4004934924104104d26d34c2492493003493692082c9a08049241059b0005934960924824020b261249040249b08208209a4925900004144004900924824926b26104000d24f3c8208209a4da590c9a49849561568001c682000410080112018000000012435612080014b4060000000049000077379b7a50800904954dc68200241369b71200009a6db69a61b410, 1128184898717761, 1128184898717761, 1128185100044353, 1461551814199050063162363173862378288981691597635, 2923192831719176615430003279112310561573561185090, 1128184970025153, 
    1128184898717761, 1128184898717761, 1128185100044353, 1128185100044353, 23014456880272322966934778201244376397464482626, 91279338312640, 
    163849253295040, 581659376751552, 581659376751552, 1128666136855105, 581659376358336, 1128253685371073, 
    1128253685371073, 1128666002231489, 1128184970088641, 1128185037199553, 1128185037199553, 1128253618262209, 
    1128253819588801, 163849253295040, 163849253295040, 581659376751552, 1128184970088641, 1128184902981825, 
    1128184902981825, 1128184970088641, 1128185112705985, 1128665935122625, 1128253618194497, 1128665935054913, 
    1128185175747393, 2923059026716252532891576003668296306131812296515, 1128665935258433, 1501503365767945621989761726681307534140041129036580497413667840410145483033766639513220421855818461523524395536512446956438524562423287501135917765839484504657167208983096030445300165355422273819046893991067039745440641454143792312762995591897752862447379456746988553, 11462626758536582302583909586791404600526373699, 2923371238321452602275315853772966510340150932290, 
    531501997402235371604538329849018963974333629708809442753374553223559320445409024892059013950907502661, 1128185175747393, 1128253953946561, 531501997402235371604538329849018963974333629708809442753374553223559301192965533925820837409181552709, 1128184978619329, 1128185175747393, 
    1128185108638529, 182866459800280701675939303819557821249100985154, 15015033664604734385304966506489959399580110773953330295600086866903864083866133108599072806387146212049676744485611025026121041177544918919333576183636804355915796642970539752525234420828523977933341196619934081471551228217639135762042987961378366151467009249877513, 146239484596672, 3957316619184925684297189135165343748734485785569124676029570219791433971881285648085489929242555540140270568007551389034031562785650291705819342222639351911062452182223642182, 73671649661376, 
    132877511029752925051748174825186803139028445692011376668635412537999079269691137052392711834656039172, 581659376751552, 365421404790046575088861852680708487679710593859, 146239484596672, 75870740025792, 146239484203456, 
    146239484203456, 1128665935528513, 1128666136855105, 163849253295040]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a6db6db69368401a4d44964920000926924924904026da69a4d20004db4d349a4000930d30da4da000482000412092086482c9240001209040048208049279a49208209249a4924824826db6db71e0000924d34924104124934924924904db6da4da0100936de69248208208261a48208209241041241241248209248248249049049249009b6db4da4da6906934d24924820824db49249249209b69a6934830136d24926d24824d36d36936826134c20924824826da49a4980104db49209209200a4938db6db6db080c9269adb20100db6db6db6c201249349024b81b0c06db41869a00269a4920100000000120124986824924830c30da6db51808261a69a4820d36c36936d26124800924924831030db6db7984d2490248, 1132582949492929, 286156768940480, 145419280585152, 286156768940480, 286156768940480, 286156768940480, 
    426761113309632, 286156768940480, 88528152185409, 88528152185409, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x229249249a692c926000124924924980804d34d34d400009a4d34926104126d34d24984100006184000000934000120124104905904000024920804984100924925934d3d9300009249200061c6dc79b09b6d86db6de6c04936f36f66e36d84d34d36920101968d34d34820124d34da48040649349209249269a4936980804924b248269a0024104d30924904804134c208261a4954c30924904924d34c30c30da4d24d849269a6006b2cdb618450, 1130521365121089, 1130383926167617, 1130383992164545, 1130452577419329, 290554681233856, 290554681233856, 
    735045141664704, 308438925054912, 589905311830976, 1130452710723777, 1130452710723777, 149817327096256, 
    290554815451584, 580834475119552, 11507228419573289408614916196888154110077174595, 290554815451584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249251249a49200049269a49208209249249269241249a69249248259bcda4d31802924120804d241049208249249201200000001201249a68249248029249349249248001249a69a68208249249249249029b4db69269b40a29048201349040a49209049249020a49249249208049249269a0821926d3c9441261249a692492482c9249a49e00009229a69a6db6d86020824924da49008241269a4920126c3c945926124800924924804d379b59c0000926a369a49a0000924d349241041a69b6926820824934d24924906db69a49b00009b71e71e7000020800000000820924104124124024800000024824904d04924900924924924820124924924da49049a49269a6c000228a28209249369240a49209249249020a59259349c00019669249b6d0602d9b6e3db300009a49a00041349c59219061249b6d668028a41208049241049200249249201200000001201249868249248200209a49a51008261a4924820924824926924124800924924831830da4d25982d24902904820124904124920904da49048008249249341a48000248208249209249249029b40069269b40a28a208, 1132582949492929, 1133063985830081, 1130452710723777, 1130383992164545, 1130452710723777, 286156768940480, 
    145419280585152, 286156768940480, 567648925520832, 286156768940480, 567915481928640, 1130865028501697, 
    286449363588032, 567915481928640, 426761113309632, 286156768940480, 426761113309632, 286156768940480, 
    1128185100044353, 1128185100044353, 145419280585152, 286156768940480, 286156768940480, 286156768940480, 
    162814179168961, 286156768940480, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24db4d64920000938d34da4d0c02cdb6e3cde00009a4db4d349240009269a0924d20000004064120121a480079ec000100104d84c0c804925934926300924d24d251c4c64d449a59b4904924924920000924924926104124934d24c34c24934d249a4902936db6db6db0c00830000824820920104920d240200000001b4c24804004824900924db6db6db6180b64db6f3890002696cdc6f64c36826924824938a26030000900030c20980006c34d30124964d24d0c024934934939130924926926924124934d34980024924924d84104924d359361809a4924926924134924924d84026d349a49a4905124d34d363009a49269269241b6c30db6db6c24804124024904924934934920100100100124024db4d34d30000938d34db490602cdb6e36e600009a4920004204d06d3030905da69a48108104db4930c04924924920100934924934104124924934804024934d249049059349349640001239b69249640001b6da6db6c04036de6da5130c000068060049a0104824904d24024d87920804024900124904900937164964c30024a34d37938130b36db6d34c00026924840108944e34c34b0413793d530124d24924904104924924924924164d24d24d800049249041209249249049248249249240259359349300009269249b490402d9b49adb300009249a00041349c59219061249b4964804946d45964800025a34d36d46300b46db8e4900002692480010d9649e4c44204136d47730136db6db6d86184db6db6db6db6166db6db7180004d249861b0db6db6d86db6c36db6db60208209a4d20100c00004d04d209208269b88240300000301308208209a4d275000061b4d34c208208269349b4104104d36d368208209a4d25984c30c36db6dd6126820006a28dc6100800000820800100004920924020000000324820000004824904104124926a20004824126904124104d24f248249001249a4902924920906d06980800824d24d24920120c36db6c34020306d26900000030db6db0d00804938c00924db6824184c349a6da6020100a369b680c1c0f66db6d84d24124926d20104104d24d0c804000124824904904134936920000000100924104104d048208001209049a41041041359600208248249269241041049249b4824104134d36f2092492003493492080, 1130383991247041, 3957316733435741279695094842938213246030297183398556868321880162344348709122765445991438030010671167740061116195955953666299513519953436211247240708567523686864530757270720070, 3957317617958184597672899128210835318733529284583726970371325177309938065765155744860584514291484461426826578489517421186915115795680661265044183667405405949615101025208716870, 1130383991640257, 1130383926237377, 1130383926302913, 
    2923371238321452602275315851411786646617933755202, 1461685619180664797282003557181428715679348163395, 1130384203197377, 4169565881362078942603269316840097260200449565506583527042533717540875511726429561578240290051919497943838912486411626048174488163270001776130453693895462706485232312776651334, 1130383926237377, 435694511067584, 
    1130452710658241, 1130452710723777, 1130452710723777, 1130452710723777, 1130452710854849, 290554815451584, 
    74921548976321, 581109621461952, 172104583484352, 308439596143552, 1130452710723777, 1130383992164545, 
    1130452710723777, 290554815451584, 149817327096256, 290554815451584, 572046972031936, 290554815451584, 
    308439596143552, 581109621461952, 290554815451584, 2923192831699196581207897358526031384789878125379, 1131002601567169, 1131002601173953, 
    290554815451584, 172104583484352, 172104583484352, 308439596143552, 2923371238321452602275354537185584326676494431042, 426761113309632, 
    426761113309632, 426761113309632, 290554815451584, 290554815451584, 1130384135891905, 1130384135961537, 
    1130384135961537, 1130384136289217, 2923192831676765773212650191598267659641990501187, 149817327096256, 290554815451584, 145221573677249, 
    435566064702400, 567434038743233, 290555083887040, 145281841631680, 145281841631680, 435557340549568, 
    593904731689920, 290554815451584, 589639694947264, 290554815451584, 581109621461952, 581109621461952, 
    567434458186433, 290555083887040, 3957316619645614456670703133741263909701702003214454025535025642061467173125526469753343276291302619358266188478510362446948737417543988739765949797373487029826035532330651206, 708171946545857, 145221993124545, 145221993124545, 
    567434458186433, 531566878008451469248290970559449168515760066662976755054472260129319668484030187147086003014590493572, 149817327096256, 290554815451584, 290554815451584, 11596431761252815292394006238909503455738532675, 
    308439596143552]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a49a4924924d269e0000934d24924c04020826930f00004824d2000092092492490402480cb2692cf36f3cf3018092492592410433ce68f3cc36c249649249049000300209a00009249241041241249649249049009249249249249a68208249249249209208209a4c360001249248208248249249249209200924b4d30d34d00004d34c34d34104130c34d34da49009a0020820000c30d34d36924124d00034d34d24904104c3492492410248, 79449387438528, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 290554815451584, 
    290554815451584, 290555620757952, 290555620757952, 88253542697025, 149675458957760]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x22924924928e36e3cdc0000934d259280001269249b4900c041001001b0000904d240001241badbb1b6c0a0249249b0804d009149209209249200041049209a0db0924824924826104d049a6c00024130100180000920006db6dbce30b09186dbcd86020824924926d80008f36db6e309248249249a6104920924920000924c24924c20836d04904d00000804126986920d341241340001200041449879b0936d84d36d800000049269a49208201049a41248205249248249040249249249249209a6924136030124904924924824904904d000049b6d86da6d24824db6d341b6c301041249a492482492412492492080, 1134850761429953, 1134782245514049, 818783921166709118066698725725881366947667094225228184714991456056091619568544099113791838402169530250058676024429793666892672165044120315040601205611771367809459306701456472100661027706902479237825725479564257465949941172216575374659335122883992556783555987955941050119922358925163278037033526047553410345842124307225280203244218861715068807574175702551345065348871105518155, 480481084203240450432080877190139154811989515053442435874789679711051441878947742999308991867259810455178929306174411043647158238990012390174971447523251346845261735809792534494360571389852383644920529181788705463993908147776879898660215625348204456461729793246959113, 1134781976873025, 149817327096256, 
    290554815451584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24922924d34d24d808049249269a08209349a4d261241249a6924824804000000004904924920820920d36d36d360201249a69248248069a49269b69a6a20000924924d341042289b6f26820824934d249049008069a00009a092492410413432a9c6c20804024934d24904900924d32d24db49360200a4da69349049021000000001240a4da69349049021269ac924924934904106924d24924124000d249a6800024924904104904924d2492412402c9249acb24a2ca200009249259341041a69e6b36c20824964d249049008048200009a09249241041242249b8830c04024964d249049008a4924924920804924924920820926d369349241269a69249a4822924920024924d24900004124924920d06c36934924100000924924802924926d248203269a6924800024934db4da49049a89a69a61009a49a69a6800022ca2800926d349240a00209349249020a4924800804104920820824920926d300300201269a6824824800024b26c36c021808249b0f340001869a6924800036da4da49800041249a492090482492cd241000009a4924800024b2cda49849029249240201343269ac800124824934da4c049049a89a6180920da4b2480002c822800d359379340a002092493490200192db369240a208, 2923728051605758559929314933870742417626711995202, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957406596879099790595470146, 2923728051603100103917957404383269810945449276226, 2923728051603100103917957404383269810945449276226, 
    290555619971520, 290555619971520, 290555620233664, 290555620233664, 2923728051604429326853024096770637962380425835330, 2923728051605758559929334276757643509464395952962, 
    2923728051603764710314869006777135611050905844546, 2923371258736026921429193020158236526728280876867, 2923728070659203411399535038590333965637616486211, 290555083887040, 79449387438528, 149817327096256, 
    290554815451584, 290554815451584, 149817327096256, 290554815451584, 290554815451584, 290554815451584, 
    290555620757952, 290839088600000, 290839088075712, 853797363520448]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2494292493492492018092492492c104124924934c24826e249b4b049049049241009a0924924100124124934934c040249a49a48049009249349a4924924b041049a4924924124104104d258000249249040049069249249241240269b49a6a24a2c9d000092692593c1041a6db6db6c208249b4da4984900804820000a20926924100134224db8c30c040249b4da4984900914924924924180926924926104124934924924826e24924b049029249641049249249a0100824920924124904924924824800024b249009249a69249841049249a4924124136db4d36db0c049a4904104d2492a8040209248249069248249249240209a0924920004100004030000924824826826104d04db4c00020004806004d2080033adb6f38c20006db6dbce30986d87b66f00020824924926d00004934db4d209248249a69a61040209a49b6804924924100a20926924100924124934824804026e24924804902830104926124824104924924a301008249209241249049a49a4820000024b24900004b45984930920db6dbd0301c6338db6dbcd86d871c6db01813311c7b3ac0004d03cc30dbd9b8dec1b8db0dbcdb6d86000decf38dba0001b6f399b6c30006f36dc6db01249a49040249049249249241241249040209248249049a482492492400012492592482480, 3957286475397161215507271467758464678282920511704727498450596225747433248283068596185371699013391854873011680474393894354066091711414048032258511877057077388486965974225180230, 1134782178199617, 531566814648506648577238044788322869782431627444936453682351466636153651288060060779961551739649315140, 1134782048246721, 1134781976873025, 1134782245308481, 
    1134782178199617, 1134782115355585, 2923371239680027450535923395121142647858904961603, 1134781981137857, 1134782048246721, 1134782383799233, 
    2923728051603224709694219430450706072007199769411, 290555619971520, 290555619971520, 590189718410176, 290555620233664, 2923719732379918226590664828984032122686451073859, 
    2923728051603224709694219279334986466289359520579, 290555619971520, 1134781976873025, 1134782178199617, 531566814648491542382975396215709529811340286128523574468508095834682218610479466127616345303077146948, 535719680387928928508263142553344117905758614438823067324213593147744725932992870710078442010956702788, 
    4217746345661154897263197952045289589276152563663330699591193316812080037710027886911626353305625668, 537796239962114842500772471133007928991003666964535805698589647601600549965970226302406424082178548804, 33284258116097804024988001097606118023719077030435534339193063922667440404733838537696065762399265860, 1134781976873025, 1134782245308481, 1134782245514049, 
    1134713457082433, 531566814648491542382975399221116431783425397472412753114851174322809799513357274961440313220991603012, 162887181013952, 154219534356928, 149817327096256, 290554815451584, 
    535719680387928928508262249518143837791014998772725706683028673939927403060909686024192205328790758468, 145689729307072, 145689729307072, 145689729307072]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a49269a49269a49201009249a69248248249269801008209249a69248248208a493cdb8f3cf30180d24934d00134d041049024b4d30c04da4104d34c30134904130d30d34d80000800000000820d34c34d34104130db0da4da1804d34d00004d24904d3400412492410248, 74852829499585, 299350908473792, 299350908473792, 299350908473792, 299350908473792]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a4d34964d349249301009b6924d361041249249a4c2482db2db64b04904d349001008209b6924100124124924924804026da4824984900924928e36e3d1c0000924924920926e00104930230db0020824c04836c00804924926da69e0000926925926104124da69a70208649649208269c0820920924926924924d84904924936d24926c208248249241009a6c30920920924920004904100180c309249249248241209209a4da0000000004800020986d04d26c04824920804926186f30006db6c309249241248201049208269869209209241349000009261041201340249049254208241061b49b4300936d801b6e36d849200009a49209248208241248205249248249248249249049249040249b4c04824904924124924920924904d26d06024db6006db8db612490402492082492492092492080, 23014457560917385301969830696113236373271491394, 4169565881362077212660851155996506481707611342567675281637298081387612534227428990428032550565521795185925276334619633973587839830351751452761531630999914558983472905455661638, 1038343154854761125642749648409976747267357263027445512656581079382127357147827602280673836171055428, 91701014069372659985672593267478796450272392002, 149817327096256, 154073505468864, 
    290554815451584, 294810993824192, 294810993824192, 294819717976512, 294819852194240, 294819717976512, 
    312429352326080, 294819852194240, 312429352326080, 290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x228a29a49249a4924d808069a49249a08209349a4d261241249e69248248008040000041069a4920820921146f3c9040201249e69248248049269a69a69a69a00009a69a69a68208269a08000009209a6a268208248209249a29269249360200a49269349049020201000001040a49269249049020a49b8da4d21802d36f369369a61249b69249248249a69a49200069a69a49a0820944a249269241249b69249248249ac9a4da1804924820804d241008200249249201000000009241248008249248029349269a49248001a49269249249029a69a69368600a29268201349040a49269049249020a4980006f269029a6184030b341a68008269248248269a08051008269a08248209048249260201248009248248009800040040049200209a4920934824020d2412480082492482498000cda49849029249269263341249249a48201341b6db6d8603cc249249249049020240001001000a49209049349021200003369240a208, 185542907881716514983538333309578664332188726082, 299351712993728, 981449509505353238871313570943092176245494822015250209404988843581513618466218028789892439123878579809184623934098679028081147322955664436856728207906921311678116421308458661666498766573933700848086566929369723974833493282212757000291371566481768977052729864249837512, 159433623736768, 89084140327872, 159433623736768, 
    145221573677249, 145221573677249, 299350908473792, 299351445344704, 162814179168961, 369516446224832, 
    299351712993728, 299351712993728, 439955252842944]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩ [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1452292496492492492010092492492c1041249249248248279a7b64b049049249001008209249241001241249249248040249a49a4804900924924924924924b041049a49a4924124124d04925800024924904004904924924924124024934d34d301809a6a36a2cdd00009249a4d24d60000924d349b48060249a09a6f000040040000001219d60079bc000104924984004802936d379259248249249249240009249249261041249249249248249a4b24b249049359349343009649241009248209241049269241249248041248249a4804b24900934924924924984104924924924924134934924d04024934d040249208249041249a49049449649309209249241249240249b0000d34d20b3ac001b6f38c209209a49200000041040000009249249268261049059258000209209a4da0006db0006c3cc30b24920804926104930004db4d209249240209a61249040249b0802934830827924824924924100a209249241009241249249248040249a4b2480490492410092080092410412c9241249248041a48261a0004b24904b400019e49309209369369a580682492b9bb9b4c0a02c98090490580082413416c960120000000c300001a693c83000684cf4cf06180c04d34d64900120124924924904024904924924924124124934904004824904104b249049a49a412492412480002592482493496490092080, 79449387438528, 75870740025792, 75870740025792, 362919376458176, 290555619971520, 290555619971520, 
    290555620233664, 290555620233664, 4153081087726013885702245672149462584160435651081710015101107350678394278549906459400339478532138779635872324045196186797966625519267032865624376304983622028480718923288770118, 88528420603969, 88528017955521, 88528420603969, 
    137871296185277590929123653149795973942921910054426473123275364300250292407580530529559731306050501, 14272531393547573756878262903182275079827620675, 290555619971520, 290555620233664, 308439863661504, 75870740025792, 
    75870740025792, 23014456880272322966934778201244376397464482626, 75870740025792, 75870740025792, 79449387438528, 23014456539989956041034883063490866391518559042, 
    535719680387928928508263128814341137462336024532963996468164481709518578945588176144112556277596595268, 146239484203456, 88528420603969, 88528420603969, 581659376751552, 581659376751552, 
    46028913678132195818436124369258700730615739202, 148440587833792, 146239485120960, 158415729988289, 149817327096256, 154082229621184, 
    149817327096256, 154082363838912, 149817327096256, 158416266875585, 158415729988289, 158416132657857, 
    158416266875585, 145277412446656, 290554815451584, 580628593525313, 286014900801984, 286014900801984, 
    286014900801984, 294819717976512, 294819852194240, 294819852194240, 286014900801984, 290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b8_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 0, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_15_0
  · exact tv_b8_15_1
  · exact tv_b8_15_2
  · exact tv_b8_15_3
  · exact tv_b8_15_4
  · exact tv_b8_15_5
  · exact tv_b8_15_6
  · exact tv_b8_15_7
  · exact tv_b8_15_8
  · exact tv_b8_15_9
  · exact tv_b8_15_10
  · exact tv_b8_15_11
  · exact tv_b8_15_12
  · exact tv_b8_15_13
  · exact tv_b8_15_14
  · exact tv_b8_15_15

private theorem tv_b8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [0, 1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b8_0
  · exact tv_b8_1
  · exact tv_b8_2
  · exact tv_b8_3
  · exact tv_b8_4
  · exact tv_b8_5
  · exact tv_b8_6
  · exact tv_b8_7
  · exact tv_b8_8
  · exact tv_b8_9
  · exact tv_b8_10
  · exact tv_b8_11
  · exact tv_b8_12
  · exact tv_b8_13
  · exact tv_b8_14
  · exact tv_b8_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in

theorem step_proof : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H2 := by
  intro M hFirst hSecond _hThird hRun _hUsed hForm hMissing hLoop hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hSecond])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hSecond]) (by simp [hSecond])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨2, 0, false⟩
  have hm_cmd : M 1 0 = m.command := hSecond
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  exact tv_b8 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H2.R1.H2.R1.H2
-- Credit: @pageman (adaptation); certificates from @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H2 :=
  OMA.BB4H2.step_proof
