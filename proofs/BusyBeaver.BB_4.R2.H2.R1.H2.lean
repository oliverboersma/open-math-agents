import OMAReductions.R_BusyBeaver_BB_4_R2_H2_R1

-- The transition enumeration and automaton certificates are from the original write-one proof.
-- This adaptation checks selected recurrence times and verifies automaton edge inclusions using bitsets.

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
private theorem tv_b9_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924104d04d30924800020134820824924920904924824924824124920924920904924824924924124d30820824920904920020824920924800020124824104104024024124904924920105935820920924104104920900904924104904920d34c30d209241209248209249248240209249049040249249249249049249249241209248249248241249249249249049249249241209b6c000301b6c24124904104924924804104920900904924924924120924924924824124904924934824924924924120924924924824134900004024904820824924924900004104d05160820824924924000100020134824924924900000820824920104924124924000020020124804104924924904924924920820924924924020924934924c24920924924904920924924d209249249a4104124924924804104924924904924124924920924124924924124924924820824924924900004934934920820824924924104024924924824924924902820924924924020924924934c24920924924904920924924d20924924924104124924904804124926926904924124924d209241249249a412492493481448, 17127037648222892492088832191254553169902965570, 283777154746433, 582844317977153]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24906186134d06db6186d86db0a26000180daa1b6c000301b6c061209a6934c06db0c30c36e300009209a4c201800269a8946986000a289248281b6c30c30db8c36d861861b7184db618c30d366134c30c30dac806db0c30c36db0924c20d209241b6c000301b6c44d00034c24906820d24124904180004d04d24906db6186d86db0930004d04924104a269861a4124820924008180d4c1b4c2c924236c26980004028a04d30020806f30184820826d4000402c9240300000269a49208000041249063000009a8a252283000269a4920900004d3592c9219241b682c9249bcc24900834824d069a010cc069a0d340001009240309ac924980020804904924100000920da6820000d34134924324000135924934126830c36db6db7180006db6db6de0c30c36e36db60001b0c30db9036db6db718592493490, 531566814649450785657876671288681220503688302853484592960740319957002482245795571941930208402616893572, 17127037646893660693337608468486652373311165250, 580097500210033313530898337995684528076011922767533640754824706822032104335926480804358259074734813445, 4217239466888111472080135976067652861039486865225918470277087897724297538690784805359646959838753029, 736459918326967617751318358941169962342263296834, 7183928146899061435596309662811766136741107616290310352614994639126500500258252057811767340437583125166951900436082250995933202699149936537169781316321064060200992343110709830, 
    565252131457089, 265755022059037528606049368800710091551263626200569041458574813089957083939382782372282748352089616645, 532345381924043839394587231136638827431788164464791843856115421029898438119305033327835291741453566084, 864534085750463775437472024363696010114125555654840099293960090748314830633476077024791732707501601029, 864534085750463775437472024712642697737387749635444326403721610387307173690719351504776013275949232389, 4217239420481885636211884274333769221249619918406470700198229186599272284172188406363180931167305860, 
    33283751484824631724446758486592626339414626909687001650335242193193514332911774179094313633661075588, 33283751113574826881504406806559618149486719339474108751154924911311664747493418279123291655557628036, 635621412981313, 265816731696893447730563627300450531955463919580844976519612206675101608510758985677817893879145578628, 582844787739201, 635621412981313, 
    72671459560001, 90263645604417, 91433404103817034175472404877668913798921065282, 90263645604417, 91701014067046502415986223887064516432297464642]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4934934930924820820924820824924920904924824924824124920924920904924824924924124d30820824920904920820824920924820920924124800020124834900024824904820924924904100044924924904920034934924104924904124124820924904134134c24920000804920820924924824000104104104024920924924904104924924120924824924824124920924924904124124924120936c000201248241248208209348249308348249049200008049209240001009240209249249040208349349241000049249249200009249249240001349249348200049249249200009249249241248208249249249000049249249608208249249240001208209248249249249048209249249240001249249258208209249249041009249249209249249240a0824924924900004934934920820824924924104024924924824924924902820924924924000104124d24820820924924904100104934d2092492492411450, 1128322476216512, 17127037646872890872075751183139343257636442690]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24920b2c9808049208261200209a4928926824124924924d04820920b2c980800820820800d209248249240201269209249008049a4824924020134d04924804060c60c30d80004000900820d208000200201348049361269a0000924c249868008200009b8e36d209860249a6f34824000165934da41200009269a6d20000134d351b60200249a6b348209248249260201249a49868008249249249209049249249241208249249248241249249249209049249249241209a6924924824124924924920904924924924120820820820034c24134d059e6f040249249269b4120b36924924900824924900c04d459371861809a69bcd3086492410c9061bc120001924d349041041049a6d04800024934da490c92493c9209208648209e090000c926924820820120924824000324924924864924964900006000000800001134d249040001b0260f24800004964924d06b2c9a692082092492402402082418480482492492492090492492492412092492492410, 1161224003915968, 1161224003915968, 176061585821888, 583925464646046210032311089356028699147815484221798688925240876006685493968757625095968313786298629, 864534077834335084935312622230326113563315144255024245805499798786670227865183464886039064456182427909, 1161226147205312, 
    1161226147205312, 176063729111232, 176063729111232, 531501965722252339719151417893749385982748779816580615547198072437728481677236116362894153952498470725, 531502947801800442927492773163467800021002412283954851203799009110700548564465259687142662424228129541, 1161226147205312, 
    1161226147205312, 176063729111232, 531501965722252339719151418108316485676987136331602392411780810924942144674025080804788654475924918085, 531502947801800442927492773378087309851561709642737460745710913759943762170011643001940428365979052805, 1161161866217537, 1126054660018368, 
    1128322409107648, 571823633729601, 25690556470361908551796657728989377012701857603, 2854593387065901417756765364343888381097805635, 2860081461121140688163781291040791909445928771, 1126054660018368, 
    1130452710723776, 1130452710723776, 1126054660018368, 79251551291457, 88047375878209, 183045910556442370483193694712342523505812252227, 
    183045911917571838166947548565840953232885098051, 1464361708073129500882287014911023686260772898627, 1464361718792024058891848614007323820361471559491]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924124130030924904924904824004924924d20924920004124d04d30934904924934804924124924100924924924904824924c30134d249a6124100924924d20000db6db6db61248249249348309248249249249048249248061b6db6db6c24124924924924904824924900c06db6db6d84824924926180db6db61b0000db6db6d861860061b6db6c00006db6db6d869a6924d3090]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249acd30d34930926820820b24c20824820800904924820924820300060c30f36c2092082492080cdb1830c3cdb09a4820924924166decdb6f67304db0830c2c92090492086182cd20924c20920924124800020124834d0002482490c820d24924904100044924924904930044924924104924b041241248209a69040341b6c249200008049208209249240240000040041040249209249249001049249201308248249248241269209a49249061341249241209b6c000301b6c24124820820b34824930824824904920000804920924000100924060924924b04020834924924100004924924920000924924924000134924934820004924924920000924924924124820824b2cb6c90000d96d964960820824924b2c000120820b64c24b2c96c904820924924d240001a4db4d258208209249249041009249269309249249a4120824924936900006d36d34d20820824924924104024d349b48269a4926984820924924da4000184124d34c20820924924904100104934d209a492492416490, 1161187433711681, 1128322409107648, 1161224003915968, 1161226147205312, 1161226147205312, 1161230450561472, 
    28545062745826614654542989170976931924500550466, 97053213332570484226080655576251206069664092994, 1154573452716865, 1136981266672449, 17127037648222892492088832191254553169902965570, 51381112941428673778384513130846816218415895362, 
    97053213332591253492742957401029665648524923714, 97064015256046791763327138764567979698629382978, 188397414114916412921459845941395364508742980418, 371085815679566731778893623022126762229179093826, 97053213332591253492742957401029665648524923714, 1136981266672449, 
    1128185173650241, 1154573452716865, 1136981266672449, 1136981266672449, 176063729111232, 97053213332591253492742957401031635980878091074, 
    565252131457089, 79267991980097, 97064015256088330296651742414129120997107831618, 565252668803649, 582844854848065, 91701014068043427215791180862678754279475385154, 
    90263645604417, 635621412981313, 72671459560001, 45850507034727868674423523919561280953562174274, 365555209772865926674932633810841226960567276354, 8304733930652940451719901982801144768872511916180091368422812893583755779612095459060107662362852101, 
    565252668803649, 90263645604417, 365555209772865926674932633810841226960567276354, 582844854848065, 91701014068043427215791180862674532138718597954, 365733616415018905501941846483771628716151542594, 
    91701014068043427215791180862674532138718597954, 90263645604417, 8304733930652940465918776659426651251968052435512311295033709834475181099316037308248446282189159173]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨1, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24e34134130c30936d04d24924824004924924d20924920004134d04d30904104d24924804d34124924100d34006920000124904d24924824d00da49a00040009269249a6124924100924924d3000012692c9a8124804124924820c059a4b26d009b8c00db6000024db61a49b41008041249249048249248061b6db6db6c24124d209a4900004934834936820104d049249040200049241269849249000249a4926b048201349369a40200001249a4900000db69a8800000026126934800026da69b0c04934924d3092492490, 1128184902914240, 1128253685371072, 1128322476216512, 1128253685371072]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249209249008049200241200209248249249241249049249008000675b6de8d8000c9269ac920924900864d4596690000c1a490c920924824924924124800924924804930020924000924c249a4900824924800124164904120000820924820000d04d04d04024824824920820924824924020124924924920904c30db6db79b6024824906c008248041249a6f248269b69b69b412002092492592400032c9a6b24824920924924904134d04db6c000249249269b41208309249a6904824987986db6000024900804d34d34104800030db6de600000d1b6f37040000f36c361b6000348eb6dc8c675b6de8d82892510000036820020000d2492490400000c006c26800004934d2490c92cb249a0820920c34024000304926120820824934da09000041269b492092492592408, 1161359425540288, 188407867590598995433876054074561682760154485570, 1161567737680064, 1161361579315392, 1161361579315392, 3957316694277195614994462503114144769307033463553815450570712339360431478875808051027300363013679535835988814037371459145822003524327253094666992703914056043273343831721852486, 
    1161368023863744, 1161368023863744, 316943093993920, 123695392443150858820591777138244336291396694676127880012348308470959859752155427914208293232690456290052550212304997480296464058885970099943991227515690800865161044104835654, 316943093993920, 316943093993920, 
    4158272566466870091383534110015526725823507602172611964368012567025801406072639159820665750206038811210420242480599867612611840481838974266754348767068266256736676787880194630, 8305224599154052166240680337390790880533226594906252264505150666555029609841015119145792510836663173, 1128184905009217, 1136981266672449, 1136981266672449, 1128184905009217, 
    1128184905009217, 1134782243211329, 3957286482768179819527693281777222988744025692529400894336606579745787399523653660005104903997793704485635937785086124867479542972185660668685346054004184135500190241041366598, 1128184905009217, 1136981266672449, 1128184905009217, 
    1128185039297473, 1128185173650241, 2923728051605758559929334276762255195482823340866, 2923728070659203411399534953587449043607842539331, 1134782243211329, 1134782243416897]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249208208008049208201200209a69249268241a68289a6904806024986036d80824920824920904004186036904db6c36db60301041841841a6904180800926920000100100924000020124124804940020920000924c20804800820004836824d208001208209248200009a6826d20000104d04d24120000926826920000d04d04d340200249a49a4820924820820020124820804800824924924920906924924934020180926180db61249209201b0020100104100da4020820820da4836db6db6db0d86db6db6db61b01041041049241249ac8269a4800004004024904124c060040000249309301b00208009248209008249860261861a08261809a69b6820900804d35134d000068208269208208248209009000069249b4000820824924820000134924d840249a49a69028209208240240001a49249208208249249209000049249249209249249240800209248248000069e49248200008249249240001a6d25926824934d24900004036904b00000d34924904000024b65b24800024d64924d04b289249205000209248248000069249248200008249249240001a4924926824924924900006030980800000d349249040001bc006c20800004904d24d069a69a692000082492092002082000480480002092492090082492490402092492492408, 3957316615500313528950177876272529048288155726323241007950100135606601638602707211682971658053146511087598194634684540582714916712758322068585638751562374493544121597921766982, 1161363724570816, 316938794832064, 105624529012801, 2928712374323320047938245962372078769276222703427, 105624529012801, 
    175997568162241, 105624529012801, 176347343753664, 316943093993920, 28545672530831212176498446389348751566034175811]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24920920820980804100800000d2092482692482c1b6db6db6d86c249209a49209849248269248241b6d249249048675e61b6de8d84d30920946d209248208209348029248248249240200249249048008249249249209049249249241209248249249a41249249249209049249249241209a6820820db4c240a09209a4980804120034100020824924924924124924924900820b20924b000000009209a09209209a09249a0804900004820806900020db09309208249249249240009249249248009a0020924000826924824d008200208008040209209208069b4120020134d641341200009a69209a00001341441340209a49a4d268208248249240201860249a6c3482492492492090482c92682c004124924924924824104024924c2482482012492412400002c826824824924924924904124807986c078000249a6986db6da4826900004904d04d048125269b69b69b4120b07986db7800024b24900c04d059071801809a69b0f30816e30c00c0ce30d44020120924134900004024900000000000020840c4c846a26826f00030c0c000b27b30008d86db09a09b6804026126824d20000804920820920820024124926924926904db6820924820136da69a4924904f3c000f319b612408, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 565252131457089, 72670922213441, 
    3957286427485527111778661891715742980289809403316088108006812304106211422999039621404241934815456337522369217595597205168907777035615685739308012509164487438563703315090062918, 483126158568166773286909501779970166293965445751328771508515819887039896711342775527383807904754446294375835299554364434992840876207573631055366108494586633598600090537543, 66438248635027102813124237241583724451367411898321183114968081856330380920148341789161228046255055749, 1128861830156480, 90263645604417, 1130852545335488, 
    1130850397851840, 531567321528223829083112477940278025149321491870621794526642264114536414428678258513495851721554981125, 290348657018945, 290348657018945, 571823633729601, 4156413866686451810832326196060372877436855084233147672601697993894557969979166837109979602874639428, 
    265755020079053651050095576156439049301051500042492735491114711641518192903644689350718400806121743428, 1130850397851840, 290348657018945, 290348657018945, 1135250596303296, 290348657018945, 
    290348657018945, 88064621873217, 7172636365189588363607176903218687066369439733807998790634610167874084306646520189772781952105100223448952502443576991264467864889081323692101356298190666226274334673064686150, 88064622348865, 8337158023001882817957897760808819414583201386663325808079021372038858755147760960532775459931296645]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920924920804820820804920924824924924124920924924904924824924824124924924904824d34106804960934800020124804924924104024004124904924920104924124924d20d24104105924124924924904824934930d00104920820824920d34164d04d24124800020124820924924824924820124924904800c249249249209049249249241209248249249241249249249209049249249241209a68208209248241249249049249040249049209001049249249241209249249248241249049249348249249249241209249249248241349041041359048249209249208048249249249241208249a0984920924924924924904824104d30804940800164924924800820820804d20124104824004104924924920104924124924924d20105924921924124924924904820824924904920134d64100d24000124924924820924824924820124924904800c249249249209049249249241209249248209a69a4124824124904924904024934920900104924924924120924924924824124924904134904835904826920924920804924134d300009a4924924824134904924d04024924900004d30924926db0006c36db0902924824924820124924904800c249249249209049249249241209249248009a0824134c24134904924904024924920900104924924924120924924924824124924904164d44866984814d30830c08d20934800020134820c6496590d920800134924934820004104924d00800134d2492482490000402490c92048, 105656740808769, 387108095404353, 387099505469761, 387108095404353, 387108095404353, 28545062745826614654542991458373197064484950850, 
    51381112941387784284643108696242918232703374146, 51381112941387784284643108696242918232703374146, 105624528554049, 387108095404353, 105624528554049, 387108095404353, 
    316739351030081, 72671391975489, 265751027411102706756237512144468974075086430320502062773562197266207687140642489186475377624210489476, 72671391975489, 582844787804737]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249b6c061861b6d86000924826920924d368269248241249841841a69049b0006906920924000100924124c00124124802924db0186186db6024820904800824930924924020924820820f24834da49249209069b09241a00209241041049241249ac9a69a48249000040249040a08248208009008061249849b08209249200240200008201840208248208009048209209248200201061341b0820820824920800804104d04da08209a09249240201841361b080c026b2c826b06900920024820000824820904c00820000980100d208000268248248209a08041200200001341241241200009a09209200001441341340209a4c24c24820924820924820020184124124824920924924900800000804920820920820024124924924926904924820924820124926924924904300820b209ac124124804124104030c20104924930e20806124d24828820184924930a20900004904d04d00000b209a0920836db0db6db6d84db6c36db6db60000200001b0c060041041a69009008241200201001041069a4124020820900824b2cb269acd209260209048008249249041269069a08269a6db09248201009a41069b0c00806b30d34c309209241a4800060324824d00064824d079b0067b06d80b269b0b24980c609279b6de7b06de092052cc0c9288000249b09341b0020806124104030820184924930e209a602010480080000590510690480002c828834800005104d06d808009309b0d20834906004024986926104904920d260001009241a480012412683cd8032c8268049349049241861041369a09249a413cda6b2c826b04906e30c04d869b0d34c309209241b8c0c1361aa834900004024d00006d86180030a371b6db6db8c26c008249a0c009a79b6d87986de0920924104104924124900004026906db0000c06db0c3c000b20820020d24824924824920924924920920020800184134da4924926900830920da6d20f3c820b209ac12408, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 72671123736641, 72671123736641, 
    72670922213441, 72670922213441, 72670922213441, 120767488680169918399165268622602027742280342653253821720913292993952173166060156901174717755653608896388921490676621337812874729538282998565782375796716427635844118130246, 72670922213441, 72670922213441, 
    33271586370207423225362517379271641444025622881879765386887142991792251164544817084110018278361776260, 72670922213441, 72671123736641, 33332411939486704944657046008029710304980157828119295232459058074042110255999289778370363618030895236, 265864505112980430064054871127573132045062604100017069507878055920428296329654291468208000923686781060, 1130865430237376, 
    1130852545335488, 33316286455908288431653864251073937295421064613913359060191156043765266418867650724910935830852333829, 580628585138753, 72670922213441, 143039666391105, 72670922213441, 
    33219377757379689231767999864837256539143287023814230887063087914783010345376625869521044950162358404, 72670922213441, 483126158568163769937114868838473761282906949724489379021146262218300713330482029180406315665268527036589376086788127675677396458423267940772876637767459893707276340376134, 538769060929150387167605773514736849148931784373987043094044224405439912097892485073146163423969820804, 531502440922005843165199561779563581526279536531015403399888381329382996547219661043230978952084603012, 143039867914305, 
    72671123736641, 33219377757379689231769648545196138159099370861916658952561525826930787176297493145768920413961994372, 265751470930873414351167473664739559899181817133814433227980523673316973249952494835606557719617880196, 45716876276521919775377038403397142598434424387, 72671392434241, 72671392434241, 
    72671392434241, 74869945468993, 74870146992193, 74870146992193, 74870415689793, 1135254891139520, 
    79267991980097, 79267991980097, 79267991980097, 79267991980097, 79267991980097, 15473245945369894448001434783851088872574696671724011500879922843173615245921454298091071963540449087871393778004981174911518632728687379280258251530001274588972188270112326, 
    79267991980097, 584559057550438947336412874517033992483262275301403858786902727587776963513328081739992108519145604, 88064085002305]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, []⟩⟩ [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920924920804820820824d2092482492492412492092492490492482492482412493492490492092482082012480492082083080cd20924104824004020820820334824904104120104935964d379a41249041209001049ac9269ecd20d34104d319b6126c041243348209249248249248201349058000000249209249209049241249241009248249249241249209249209049241249241209b6c30c301e6c24124924904924904024934900100104924924924120924924924824124904924924824924924924120924924924824134d04104036d848249209249208048249249249241208249a0984d20924924904924904024904920804920820124924124804920820824920820924d249041040000201048208349041241008249249049208001249249348200041249241208001349249248208041041208049209248249248201049049248000209a4924920904924124924100936924c201348249249240a4920924920804924134d200009a4924924824124904924904024924900004d30924926db01b6c36180902924824924820134d04d04c208269a4924920904934934934120800da6d341b78249248009a0824134c24124d04930900104924924924824124904924904020004104126904924124924d209249049249348249241249241209200208248269049240001009a4014934830da0da41b6c000301b6c34d00024826d04830924924924100044924924904920020824900934000820924020004900100904920524820820924824930804026904920000804d209240001009a4020924924124820834904124900004924924d2000092492492400010492493482000492492492000092492482412480, 4217239420481885405707907810651761728937077123331855913644263850413340052916094075713140544841582341, 580645764483649, 736462602474296063222552360384525036875883775811, 72671391975489, 72671391975489, 72671391975489, 
    735038153295407254265949365575100471625558102594, 265872615188757442269524184549658156030712485687293037900285592807355900378626447750940012429883326596, 72671391975489, 265751470930873414351167693488783971366646566571538298686022043057095441248342488877933403559581466756, 265751470930873414351167693488783971366646566571538298686022043057095457831013613220635459541319041156, 79268461742145, 
    79268461742145]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b9_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 128, ⟨1, [1], 1, []⟩⟩) (prev' := [⟨3, 127, ⟨0, [], 0, [1]⟩⟩, ⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_3_0
  · exact tv_b9_3_1
  · exact tv_b9_3_2
  · exact tv_b9_3_3
  · exact tv_b9_3_4
  · exact tv_b9_3_5
  · exact tv_b9_3_6
  · exact tv_b9_3_7
  · exact tv_b9_3_8
  · exact tv_b9_3_9
  · exact tv_b9_3_10
  · exact tv_b9_3_11
  · exact tv_b9_3_12
  · exact tv_b9_3_13
  · exact tv_b9_3_14
  · exact tv_b9_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249259249201209249a4924d20100db6db6db6186124924924834824934924906904804124100d20db61b61861b6124924924834820524924924924904904000836d86d86186d8481cdb6db79e0db0926db79e79e0180924924d249241841249349249069041361061800009341241041a4124904924906900494d24924924100db71e6db60001349249249048259a5924d240001259b79249260201669649249008041041249241201b61e61b60001049049249048205359b5934901804934964924900804924904104924904807187986d800048209a0924920804000d840000008248249248240009349041068201bc906db0000b061b6db6d86c2c1bcd86d80000b00336db6f06c208209a492090000000400413082482492482410c000934f00804c34924100920d861e6000db6130d249248348361b79c0007984004124924120186124000124124004124124920186124820126100104924904806184920804900004134164961986186000d86120524934104920804904924820904904104866186180c06184804924d34d24d20100924926924924104124924924904904100124120000926124104124124924924904900524924934924834824924904804904000824815935124920000934934934c308249249349041049249249208209249200009249249209204949269249241041249b4924934904d44d24d30000924924100d34924d20100924924924124804924924900524924934934c308249249040349249348248100001241241201001241049240000041041058040049249049000001200041209241041249249241041049249249000011259249209205249040048001048249248000649659348248104925249249249049041348000248124928249a4924820000004c268048209249249269048049a41b6c3002c104124926120b06db6db6db6c20124924924d20820824924824006f36036c300209209249209063001b6dbc1b01c6c37030c678248361b79b6c61824924986d861b6c00024812092564924934904904924924924924924820824812492504924924904000004104d049041249249249209049249249248249249040249249248241209249249208124124924a492092492080492c0241000209a4824924824124984924904820c30924900d30924904904924904024000d20c04d20800134924934804936124920000924c049040008240001341341a4186024924c34c269840241000200001e61b61b6100005905106900000920920d200001c61b61b6020034834c34820924824924820124904904000824920924920904924124924120820924924134824924830c36db6336c24134c04d24804024920124924120800004104034820004d64907104100924920d20924900c07187987186180db6db0db0820000104d00900000934da4984000184d24924800064d24926d0c92692cd209261801b61b01b0000db6db6d861860361b6d86c00066db6db6d8c92493cd30904304d04f048000349369261041009049241200019249249a4324924b34820820924920900004924d24c20820924924824000124924934824924926900006188d80c00000db61b6d86000006ee7b36c00036de6db6d88f36db6db08209a49248240209049040048249249249209049241249241209249249a410248, 1161223936807104, 736459918327297978899165597341552335018518385474, 583925464646046210035169311700543112495737370560400340818668355485842552277242833726014485576085765, 864534085750463775437474882934987212150735677456850815001953192888646404129005235325752764740876169477, 864534077834335084935315480452670627976663066141362847457393226266149384923491950094669110627972215045, 1161226147205312, 
    1161226147205312, 176063729111232, 531501965722252339719151417893762462925942139568124456122449636846320815837917288747685935509512048453, 531502947801800442927492800212142591656481473626200130652390132322243859993997061955603779569957858053, 1161226147205312, 1161226147205312, 
    176063729111232, 1161234884202944, 1161234884202944, 457547442557376, 1128260534735040, 960962612589359618611532028395910518637252014413543773330069459706170758439299782734078755443486714569017602045288140747048921804864955815265939563464113987987469071467814027691857435877016470295355846966495759488133384841213134858544021695187902629243518976496988553, 
    28545062745143825013019818964169652391813059394, 1130453113376960, 1130453113376960, 366090429703230115313587427253627290567827801923, 580697312989888, 72709569515712, 
    72709569515712, 283816003375296, 72710575165632, 72710575165632, 2923059026695296463256125385836157452557299517251, 1128665941819969, 
    33218934237609691583668613635874583311891039549343827778229614350553361667770860123133092347380394565, 1461551814178093912396959819068707169171268536131, 1128665941819969, 1126054660018368, 1126054660018368, 1143646997320384, 
    1130452710723776, 2923059026705660287785760901782706508930421393219, 580697312989888, 72708431876288, 72708431876288, 2923059048473388756027668556620251635663845263171, 
    531501997402235843687492455450506644845432665480153217580199048554386459247388094160394534954521091333, 72723462623424, 72723462623424, 72723462623424, 2923059026695317273087606894964276760030679729987, 1128665941819969, 
    531501997402235843673079032506535546116741675871973025046324523990657685167589542340237534294613187845, 531501949882260587742187637716362761982646324171242140837005543296288403205208274621864177852821496965, 2923036725949931819777555688761884860089402196547, 182711399378464490998058473316705092375557505603, 1461551814178114722228441328787122287003354335043, 1128665941819969, 
    284241213538881, 145275193659584, 426761117503936, 616365761228219484124532512486989478989026516792404629457449633611717112559284693155219963303393157, 145290695807168, 145290695807168, 
    145275193659584, 145277404057792, 145277404057792, 145277404057792, 145277404057792, 426761117503936, 
    426761117503936, 145290695807168, 149675450568896, 149675450568896, 290413073141952, 290413073141952, 
    149675450568896, 149675450568896, 149675450568896, 439955257037248]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x14924d349249a61861249a4924920100924d24924124124924924824824934924906904804124100120134824da0106124924924804820524924934924906904924924904924020824900934904904815934924924000124924934984034934924930804924924924020124924004924924d20920494924924924100934934924934824da6924d240001249669649249008041049249249209249049249248205359b59349008049249349249008049249041249249348248209a49249208040000040000008249a49249a40009349241360261b49369a0000926b00336db6f06c208249249269000361b4d84d308248249249a4106c00924d860040041241009201040341b0126100104924804824100126904c04000824000124124004124924920924c24924d24124904924924800000920804900004124d64930104824da0936120524900100920804904924830104924124826930934934904804924925924924124124926924924104124924924904904104124d200009009240040241249349249009005249249249049049240208249349349049048124949249249241041249a4924920904d34924d30000924924100924924d201049249249241248049249349009b6d34d24c20124db6b24926186124d24c30134d249a6124124924964924c30824924904024924934824810004124d24120100924004824000104134134c04024924900900004120004100104124924924124104924924924104104924924900004124d24930106d259b4936120100004130820104dc4904926904d24000dbcdb8f3c1a40001b4d36924104d84934926906124924104800d04824924800d04925924824904934934904820492564924924834824924924904904134830c349349249049048124928249249248200001248268340209249249269049849241b6c30c26104d24926d20920124924924d208209249249a4120920924926904000904124006c249849349249049049248001b6db6db6c24812092524924924934924934830c00924904904904812492504924924904000024904d06904124924924d20924924904024924934824120924924d20800104924900d8490092490493490490023cdb6e3cd84900006db6db6d849024124924a49249249208049281a4900c009a4824924824124984924904824104924924100924904924924904024004920004920800104924904804934924920000924d04934020824000d361341a81269b61a4900c30900024904d06980004920920d30820d24834c24830924824924820124904934020824920924926904924124924d208209049241348249249b6d86db6db6c24134c34934804024920124924d208000049040348300051a4906d04100d24920d20924926c301c6de61b6020006124906900000d34924986000184d24924800034d24926d84926926d30924904334904f048000249369261841009049241200019249249a4324924b34820824924920900004924924820820924924824000124924934824924924904820924924824020904924024824924924926904924124924d209249249241049349a49260061249069349349000041341301809b6db6db6c00026db6db6db00009b6134d24c201261b0db6db6180004824920026126930904904900926134d24020124904934904904924d36924924106124000d34124124124934904904906124830904d24006c36d86d86db6d849b6db79b6c30c24986c36db6db6c24824900124904904d849349249000049a6d26900104a24dbc3260001349a49a4804126d26934a05924936d30926926180c30db61b0000db6db6d86186006036186c00006db6db6d869a6924d3092048, 1161292857741504, 1128307777605824, 1130438081384640, 77290809659752224641570850565179192160923234364145788709667211484705319203405149708392542463486844026349131196025008409570121986007553342977906601907764302383224447972494919, 1161088708251840, 1161088708251840, 
    175926290157760, 531501965722252339719151420469812432020520579809320376335738600182426246611998906964769907020616164677, 531502947801800442927492776168874682799921604365435904672868736201476900440003457112568722406451433733, 1128329254211776, 1128253618196672, 2923036725960399412838459165826004253505012899394, 
    290546485563584, 1125917221064896, 1128253618196672, 1128253618196672, 2923059026717914074224623051664358617033226590018, 1128253618196672, 
    299634384704192, 286577671540928, 308705900893120, 531501997402235843691094054311519500343267002393897100404738314524961138709247525085326124978845086469, 531501997402235843673079034223910918672121260868006679184995680358192280525565684572186994334616613637, 531501949882260587742187613673107930069182383842798234143924738899107782116660007440795223046427593349, 
    2923036725950430201681676503727122060293390281283, 145290695807168, 145290695807168, 145139965104320, 145139965104320, 290555083887040]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149a4db69249a60001371b6db7980c049a4924920100d34d24924020136d24924804826db69a4900b04804124100100134820930000136d24924804804120824800300524926db4926980804924934d04d24001804d00824c0000412482093000c0149a69a6946000134d249349840269a69a4930804924924004924924d30000826920da61200209a4966b00494d34924924100db71b6db6186134934924934864da49249240001349669e6924900804104924924d30187036db0db61249049249248605379e7b36d800049269b4924920804924904124924934c001c0db6c36d858209a4924920804004d048000008249a49249a4000d34d241a6824924b00336db6f06020824924926980034134984d308248249249a4107800124f360040041241009200001ec1c61b6100104924804800006007987984000824000020130036db79b6d84004924924920000d24924d24100104924924800000920804900004924d6496000082c930db6100020824826300564900100920800804924800104d24135800060824c36d840008209309ac0049249a6d249a60201249249249260001269b4924980804104924d300008008240000241209009208009009249249249e6020124924925980804924924964000124da49acc00034924924900104100824000024026826c2cc00024924900100900e30db0f30000124924924904904124001806d869a4d800043249a493c00c024934db4926d80804924904104924d00000920926930000c341249360201029c69249348201a6924924820c351a6da59269049269249269a0924964c001249049a4020924924924c2410002592690492092492c9a00a49249a49a6000124926924930805924924960000924924100924924d300009a49b69a412080692c9669009a49a49340001a6db6d24c30c26926b2498610cde8dbd9bcde0f369a492c0001249360009a49349a4030db6d24da6c06120b249a690cde018d9bcde0124924944d34c30834da4924986184d34924926206124904024924934c06246db6db6d85824934d34d26900004924900026934d36900c38e349369c0900004924d3412010082400082c0001041341050040209208008000041200041000001249a69a61240009249269241000049249a6980004924d349600001b19b6db612080082400012400002d836c26820020800000100000920e30b208001249b61200000301b6e30c20004924da4980000c06e30c300009249369240001a49a6d24c00026b24db4d00000f66db6db00009249b692c000026326da6820000d8ae36e60124924104c00d040248041001808049209240068201248001041259358000069a4db6d843009a493c9ac02c930900000020806000c00c360000001b19b79cc186e07800186c24b00106824db6f00000926946a20c00124938da41005a69b6d2493cc00024db4924f300009a6da4d3cc00034dc4db79800069a6d24db0000da0000000004006d86f079800069a0c200301001d61bc1e6000014924924924924134db00601b61b61b6000120524924934804036db6db7980004db6db6db6030124924904d04134800c36db4926980804812492826924924820000104806004020924924926900038db6d86e60984d24136c30c26104d24926d20920124924924d20820924924a24000d86db61b6c20920924926904000104d040060008249a4d861801b6db6db0c300201269241a61a49248001b6db6db6c061a09a48369841a78269259ac0120a4924924d249259008069a6926b30100924d249240241240009200009009a09b0b3000092492492402403cdb6db6c0180292492492492492493400c024824826c00024135965b67600804926da4924d80804924b269a4f003049b6db6936024104d24934c00020020800000804b249b6936024024924924920830db69b69a61b41249249249a4826da4924da0804924db6db6db6db6120004924126980824924926940924824924b248024a69249249208069b79b4930c309a4b249249a4326924b20804924926900c361b49369b09243249249243029249249249248241249248201249349a4030db4d24da7024104d24924904020020824004004124d34924d200049b6926934124924d040249249348001a69a4da4984120104924d2083c06092d934020020920004900000b60e309a0800800900024000024836c2c820000db6e38c30800036c36c30c20004924da49000009269b69208001b6936d24180036f38dbcc00024926da4b0000c9cc9b69a08001b6db71cd802b24b249249240241249240049249349ac000024b26da88240149269249a4100924da69b6180134dacd2c904824936da4db0906db6db6db61809a4d24934c201249b71b6db6d860269b4924d208049b09241809a4100100926c26900924da4936c201249a4924820024936da4d869069a4926da0920924934d34d24986184900924c009a4120824936124980f30f36db0c301249b4926d04034924927980004d37b24b64d20924da49b68201b6db6db6db6c26db6db6de6db612c93482692493cd800049249249a0800924924db41061a6924924926824924904126dbcda6d04d04924b24106d248241200009249a68001041a0d20904800036926da08069249a4d20000924db6100020824926825800024936d04180824926da69209249249261041a4920904800024926986b04106024804d20820d249b4b2412692c93480002493d930900824924920960104924da4d26020924924b26824924964d004924a49249249208069281b6d20000a268249248241249a4934984024d24924924100924904924924904024004d00004d60800104d24904c04934124d00000d34c36920186124d04d240318249001b6da6006d84124d80000c00c309001801a6104d26031837030db6c06186d861b4d00000db7036db0186100001b06180180004120100120000000000020020104004c058201208000000009248249248201a49051340018269a0924926904924134924d30830104924134c249249b6d86db6db6c24134c04964c04034920980806304920124924d209240360069a4000004904004c20000000006d04100124920130c000249061a6164c00c00db6db60000208000003061b01b6db6db08340609e60240200069249269000009269a6800000184d24934c00034dac9b0c04924926d209a4904334904f048000289b6926304100904924120001a269249a6334924b34c20824924920900004d34d24060820924924824000134d24904c24924926980008f68db0c00186036db01bc000206dc80318061801871b6c08db6db6db0820924924824000104d240358208249249269041041349259309249249243049209249a4100924db69a6180134c06926d04834d071a51a0d04db61b6db6c301249209249a6100924c249369840369a6924d00000824124804d20830180180da0000130120924800000c24820100928da09340001249b69a4d86304100db09380001b8e38db6c30c34db6da4d86308db8f36db0c40d38db69261861a6db6d24c30c26e38db6db0c30000000104024036e36db6c30c04000000000800186186db0c30124804926904024906c36d80304920d849b4d20d240309269b4130c06036db6c04db6031b361861348061269a4c26980c24d349849201849b6d20c20904920134830004c0480412082698693c9800049261a69a6186100100000800c06db0dbd9b6c31b361b7b36db61b6c36db8db6c36d80c24d34a0cde018d9bcde0db61b6936da41b6c36db8dbcc20db0db6e36f300061b6db6db6100004924da69000009a0db0800000166d269a4c0000cda6820c04d249679309249b0004124000900000db0db6800000130120824000006da49a0d04d249a4d20000decdb61e0030c36db6c37800036db7186f00c36db0db6db0db6926d36000124906824004126a36e86b000041b49b0d20104a3c92cb34135924d34830c07b3cf31980000f60f30de0c301b6db79bc186036de6f3cc46decde6f00524824924904024906d26986004d20104924120924224924824020104924164826904924d20804924b26124924820120020900326b04000b249248240249b0924d00004926c2493c18c104030924f00006e66306c30c30d3cc2493c18c134e30d249861869b61b4930c309ed98c1b6c30c00000904d00900db61b6db0c3010002403c02c00c18c1b6c30c049201249341009248249bc00c124834924934824900924926900005924924121924924db6030db6db61209a6266f2602012490c924926904004864b248041cd00c368f48c64b24836c06db0db0c30d80db6db6d84134925904124924904800026926b20304104134924120000024924824124924934800037b36d86000c30db6db0de0000db6dbc18c030de6c36db6c3cda49b4d84104924924120104a2492c1ac12493492493482492692492c90592492492180, 531566814649450785657876670215531265998023650808656098826945824754779869371771716067602040785765417860, 1161567670636736, 1128857199972544, 1128857199972544, 1130437678731456, 1161430097465536, 
    1135316702859712, 17127037648015521176116404669265403318733116226, 51381112941387455961885237871902540390912234306, 1128719626801344, 188397414113878274108121883777773022278185915202, 97053213331553114679404995237407323419041600322, 
    583925458845267951738859733850487746260040379428863801484293751228410341833749704057949946693043076, 176061585821888, 1161224004833472, 531502440922011507987688852142983278718900467173717559023594830312502731032005542366005473334201172868, 531567321528223829083115114109994311430434659402829629512586854342111017432851596892781981882271417220, 2923719688834201757094344235052742252880218575682, 
    150223474135488, 572298500248000, 366089384351810970051097662132651854132647318338, 468850913332476241393342124340705371628842799938, 531567321529186848906369252525030507086885214195230403430841780945585946778573305689494888430438728580, 531567321529186848906369252525030507086885214195230403430841780945585966031016795535089221183763399556, 
    33284591003420927995887185010945852286861332589745020583697714117032676458703928906999172695735944068, 163417622057664, 726367575478976, 33283751484824633568464494523555089167676467013013135550816259059624248911321348761768563879599948676, 588272456809824007104837722063016091387720654829062855177761045759635904597979223552704604481207419780, 265751030381101160251914697361723969332882984433199769663192756611795652540431116653601450114081375108, 
    567487725834432, 536173393131732473221824658039167194930743214246879833382176340556122612563407802937922744565755035780, 536173393131732473221824658039167194930743214246879833382176340556122612563407802937922744565755035780, 531501997402235135570264311189313421640219336353171926609452026235394949189442263659222039013178438533, 531501997402235135570264311189313421640219336353171926609452026235394949189442263659222039013178438533, 145825419235520, 
    567900445348032, 145825419235520, 567900445348032, 75387955581120, 145825419235520, 567900445348032, 
    4089164710033246213007359302831900118619751789091336403577432068919550416531602826166131596331397418295608575317451779870038257680246550460464513413204197249443290193646794822, 572298500248000, 48615820536105127092036639525625565032912853826, 75387955581120, 145825419235520, 583925458845267951737703940248531844532762451988572544967618062614739171873337456959285311358387076, 
    97058440069710812891172945498690220517847216963, 583925464646046210034081354418241042661840817254311917046424852876302661184584746808078170562249604, 158469400301760, 3957316615499431320073279171356055356640806737271037387578621426781415056028509443995710752171430173653479517965134612880364053994539135199775553254813707141174889720749141574, 1161155217264832, 1161155217264832, 
    1161292656283840, 1161155217264832, 1130918647959744, 2928723415900934047177917684730361642551275950914, 1130918647959744, 2923036725866004101741512453434809085573065610050, 
    531501997402235843673079044649230570505784453332728509252041570760871091146180489924269695899129867525, 1128719626801344, 1130918647959744, 1135316702859712, 1130918647959744, 531501997402235135570264311186221226746162484336017757929155529576925215960945709054439538734792930181, 
    2923103628355648394305329106798367155052724884290, 2923192831676724883718833713134832355930517017410, 2923371238318877862545842925807762757686101283650, 2923192831676724883718833713134832355930517017410, 1161567670636736, 1128857199972544, 
    1130437678731456, 1135729424470464, 1128857199972544, 17127037648015845695908003135277566749652816706, 1128719626801344, 17127037648015524979065825272171215012684116803, 
    316805655040449, 316805655040449, 1161155217264832, 1161224003915968, 1247177207726153154038098006463783627512013935540556657255957341792308789515530887164147822323305077106444814543144337664534432445601373800292744158009052914568042473597228498332232016099205100591132002347970619635020768845287971045613598277091314578401715288978575512370808464068486039296824623733615911617759429979852429486579668204240116108636468556611913406049787909100141194856168082024173730554763263307787636383861869959621288495660086336258626231393854654835659388212755817542960512741996828805180838605, 457547438363073, 
    6708399811944600532696790260259951571040479240051968516421583058712088867290078696718685866546038411240628912750561834603132311364113411708535990469257654854352837583404424268659640372883950977796194427357578042569542498057993380188801544155629728195874827015738305897197467023565797731950776408653067675339721065592128268439817412731078011281434893083385607104129505732685569994, 2923093000658592447980588729320906541032651365186, 75387955581120, 2923184468907743145133108082163167622172900332354, 145825419235520, 567900445348032, 
    567900445348032, 567900445348032, 145825419235520, 567900445348032, 567900445348032, 567900445348032, 
    150223474135488, 572298500248000, 163417622057664, 4088711893740771381379342781570705588355041718546686461865956551833091056979001689259706078246673102461641861758876481651394960237778308818600589732665575540508959174895291975, 4088680758550766603663186788895256365551859281052934693262494430807046741427580569272915901763208230240158394410557170796722151746126804632888888999814504053372436762085772871, 5943689845820892525614169358606913244565983263799167975061115907447897931742273242825163341625885070030477437674817168824359940889667872272086270926918750495800260946856726087, 
    4156914883483758559037819094677424841245519974828175105429258045252729027828858792872370962157519825261188057460420608821342408373016711842984249957565284324867846252588399174, 75387955581120, 75387955581120, 531566814649450785657874923644777402671711512750950096166187421880228096476545768604771935376345656581, 531566893848442985190980866565838473362175657068085156194334670639486524708682131323076016230238514437, 531571883445859728093837140427385603055051674628485481986039667203719999726863377092585856122263694597, 
    2928712984110318495059646919007336485032694921027, 531570869686387601568153503727630526490278533116331828309879491542255935320824782891380597688808762629, 457536835170753, 316799212589505, 573090402627753161486516680442063703959110230998250254501814378422345183133386836856593180882663369989, 1161226147205312, 
    1161226147205312, 176063729111232, 105697136611520, 531501965722252339719151423904563279495021731943489772826169363790960182818720811989963073500086913861, 531502947801800442927492776168874836345243619789674959719065905041382141120522107549359433573069338373, 176209904800192, 
    531571883445859728093837140427385603055051674634307017238631939284793394299748016726684783022796296965, 5765546543805391563381780853924709238853624682097217448921726523468025461793079394510719890329506292334581915161575705468453578308586525034010986453615906510312346773100078665067648387915358846855909057087186876963248649396505118130469297926964670254424586939775289671364395982823310298858079850647811093277181090444126629903772184660246131597635875438683587919322208029585893199611206498981318469703717996563450588773344431184468919644609481036814239641229991500152062498059281126567201237218232663977172259898049225722777032659423913577198986090325697532848071351329209458223001837673945158940115854156118206461248249421624167973432496560291193165935280010318, 960962622081764875629626206472676079327277374874781596525940651435555211919219491956045054884581775322130128040816507807391756922398468586404677883594024464416976494615298378463982072990360767319256278704350223481788764373133723322703744936524768137806086665249159113, 531567321528223829083112489960438149198804376545405962509925864369240606676787603297008608290488446213, 498163040104781343237773855974131845671883293734900061591288853416102642426126664740991463430876311546798842261167452227987070440949729936822730459775297266512895993151046, 158470075584961, 
    1978643215499139501480111932655952016112534566834475805791071227488675193942005186071021224849202533326164437654398232696305278986913238729826204884776110039015596004181245510, 531501997402235135570264310958079900145370019588344652262386231054880777405460864413218623075942395141, 531570933046339975351025529152217806744001312836172523151030541854518295425420727207725108521830968581, 531566878008451469248290982353197500484908746764260403146110055113348118614123168029392104719075503365, 573029577058473879753042511740591927632196194220010271288749486527830739361082369979707865783388597509, 580065067795137711352198537675952974095634500654255594392466282774296572246853319550668779936338406661, 
    845848463271169320889720537581558360560352067589879993421898280056435586169264105873082000454702066949, 1161161668104640, 2928723415900943782137840300818112327337581220674, 1128657353970112, 1130448688787905, 1139244781810113, 
    1161093145956800, 1128657622405568, 1128657622405568, 1128657353970112, 1161093146743232, 83713619669441, 
    567906896187840, 2141060067972986641489962623164648584329336648643615261780286032027624403642692542209416202924647813, 290279937544640, 285881891033536, 290279937544640, 290279937544640, 
    290279937544640, 571754914255296, 84190499443136, 84190499443136, 290279669109184, 290279669109184, 
    1128184902914240, 1128184902914240, 265750998701117656297987067882619201884752896315138283728167663002607021333567544911934299148455787716, 531501965722251631616338442218049409810977256899298335935140467231180271690690139569227184024003558596, 1128184902914240, 1128322476085440, 
    1128184902914240, 3957286424721394476491768881696603703764903848770318166983563251748963750950720875776116900299057653898949913151443479566117111929768128111805849987853224339449133021034622534, 1128184902914240, 1128253618262208, 1128253685371072, 1128665935515840, 
    1128666136842432, 1128665935515840, 1128184902914240, 1128253618262208, 1132720388509888, 2928723415900954166771171451729943110773217694530, 
    531502440922011507987687974671307298852662048507390360985377533966238448980290142687871096523585766276, 531502440922011507987689092682674858058762562534550482365951843008846848909657822635018625080409473924, 1130452711641280, 531502440922011507987688852250109597757980193307108025327280121064557086841128188820814364705948976004, 286852968878784, 286715395707584, 
    1134781978973120, 324403033014317025013452792266667442372935340253882132342696783432637782545279639989094591330794692, 4217746346624174720573599191810104277284258825278847475284504038723048479123082296576017894662751108, 145290293153984, 163432654443200, 581109629850304, 
    581109361414848, 581109629850304, 581109629850304, 581109629850304, 588487381307595738173260972382405858427612365104210263548053294057725871279884605134159608817087365, 551485155253820933266062457466958802287893320397053648910289043412412566816064778898896028883501956, 
    88734717448896, 88734717448896, 158484847923904, 17609920615104, 531611926944997396214937028473237242885810934252985743261324043754692474276252932131217526814432621445, 2923036726630994937979604706935186254505541940803, 
    531603816869224160557794421692510497801572667029234137886465081566064330350184282770368033773436334981, 9042944782536846948981574166627399384240643254729415806876483399908960075083700666305630933329541281120252144279941072681909659073634594233748546498717607458168238828801226850598750945948754662264210069070974874528169444898931430249236626922479839826117199391725617344618981788527846260228495579665550673031316916090798298159837853403385648407187671823781718449620485187056231523094109388927738353668614156036286506608615737073627204495869010022507472153706766435673749692708103639517440759458073029766121958297840681360429813054107229533120379736878137601663210742718151789930403767338023307073435587343373539126231654575845691833392481617869083186773305472079, 571754914255296, 620927684415644561850433813933519344039768284032471916290634555454224506920342868206084506728067973, 88739012416192, 88326292902592, 
    88739012416192, 88326292902592, 158484847923904, 17609920615104, 581109629850304, 17609920615104, 
    1128184902914240, 3957286427485527111805477507569384677388197674250739130133679843330344177161886871364396286693745900158590414288783911075530269644634508248180068241927249497143947173663039046, 15458150559956068225851132506395768897505380072025275592247127570063413516556477574871253652817132357768580923120990472391055479711629950492811984558738419483953658559248454, 1128322341998784, 1128322476216512, 1128322476216512, 
    3957286427485527111805477507569384677388220299235443485219793535927361868708015771026928091028424586370231408205400553554704717834826420744770438476709824892964080813810343494, 1130383924072640, 1130452710658240, 531501997402235135570264311189313424789097994856964839028254928206704809287030184532281305013660382085, 1130383924072640, 1126054660018368, 
    1128184902914240, 1128184902914240, 1128184902914240, 1128253819588800, 1128253618262208, 1128803575926976, 
    1128665935515840, 1128666136842432, 1128665935515840, 1128184902914240, 1128184902914240, 513262575315785713109034988782640296760438075564874281050404844154274029506142137894678607691033726719169151741943392654207284151724912364701364137612662817382401486847558, 
    531502440922005843165168360517650923420049720453808618315725106908818067518490724000083675379693482885, 1130383924072640, 1130383924072640, 1130521363091648, 1130383924072640, 1130933680345280, 
    2923192831676765773212575119852364948226399277890, 3957317617958184597672899128210835318733529284583726970371325177309938065765155744860584514291484461426826578489517421186915115842779835124340859742328616267857262782869098055, 145290293153984, 567915477733568, 75402987966656, 2923184468907784034626849488880700214468782592834, 
    145840451621056, 567915477733568, 567915477733568, 567915477733568, 286852968878784, 1128184902914240, 
    1132720388444352, 145290293153984, 581109629850304, 1134781978973120, 1134713457087424, 531566814648491542382975402655867125712604534182343094559084769091438495039565119690337711506354922885, 
    854063668270016, 564753244728138667426549824804832936857197572353657915528302025269505665617763235087476412594248708997, 74921548976320, 75402987966656, 551485160692050550417311503508924955102822317381147886419659577387906864949760757409782676147399941, 88734717448896, 
    88734717448896, 158484847923904, 17609920615104, 581109629850304, 17609920615104, 531619530141276267700557274461832567872510859927455563127685597429878351681048325215500874061692957573, 
    1152443081954241, 2923192833038372936644108241599170256640816525891, 3957286427485527111805477507569384677388220299582027196984895393375837913017288150570427465748796558364407671689073224107731583576405032560314521241743654677499927470207360582, 531621304220114566579311466517790443780762697499375362972412861988920033155938131641706009295917052805, 1139249076646849, 2923036726630994938058832869449450592099085922883, 
    531501997402235843687492467472134252733671676030216951097768158067712381864492650594342072099700955397, 1130452715180993, 531566893848442985190980866672964793598485295766810494280377852524310527398721297406382222870032315269, 531566814648489654094462052604028532705188804688722680103002038427226833581283017925190032782667567813, 3957286427485527111966371202725574094032889140597186263575005487352976806448171469348412931511057964323469129069035747318896766787336906825039053124343215746957859156389787206, 531501997402235371604541297741964151506216033423071027041039861554875986665903073521979653874969263172, 
    2923036725950430204216955942522701377235549499971, 3957286427485527111966371202728695842583131401649477762975031414170829524684296566292761932369683376308712280406635099414929226811327379038331897721684112069552228584306767943, 531501997402235843673079044528163154004980686422036758563893633503983607784694098774185071439793051909, 531501949882260587742187613673108083614504399267037289190121907739013022797178657877585934213045497989, 2923036725950430204216977704220474343531477021251, 531599254951833737190261037788891176835599359486611574790707312678322450338710135540840952138345902981, 
    286723994031040, 145840451621056, 4965524312256, 145840451621056, 531567321528223829083112490067564469435114015244131300595969046254064609366826769380314814930282247045, 145277404057792, 
    145277404057792, 531567321528223829083112490067564469435114015244131300595969046254064609366826769380314814930282247045, 531619530141276267714738563214905156958426445603439588578291278991848682840088774444118010874955199365, 2923192854816444419584169903255145132273982059075, 564818125334475614618550950192590259501422762557165747307180348102220756654690576543213284270098772869, 620927684415644563707507341121597685815827987103676199989793951083527565801715557062422710882562949, 
    564790246948754212628487062889464454458873136558678826990690777214378100779477850453582005435399304069, 2108619717975313787150224753205593936726681773318370307879175223363819179513068222487405634422848708, 299076030566848]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149248949a49249201005249249248248249349249049048049241009205249249248248104a48a25149249049240208124124949249249241009249249249248249249249240000945651649249000041049249249205249049249248104b59b59349000048a4924924920c025149041249249248124209a49249208040040040000208249249248240009049241008200069a6826d30920006f36f3cdb0b00334da6f3cc20824924926900004124d84d208248249249a4100800924d36804824924100920926924924824824944924000934094004924924920520904924924804104920804100004d259649205104a48a4124920804d025148209049241248124049244949249249241041249249249049041048249200009249241041241a6d349a6c248249249249049005149125149049049240208124124949249249241041249a4924904904d34924930000494924100924924820100924924924186904924020824804924924900514924924924c20812514904024924920812410004824124120100924104924000004104104804024924904900c049200049204941049249249241041049249249000048249249208601648201248205b79b58601348149a4924820d24812514800934925924812410492724924924904904104800824812492824824924820000124826834820924924920904b04924006c0082c10492492cd208041249a6f34c201249249241208209249249a40001bcdb6db6c20920924926904092092524924924924924924820824812492504924924906000024104d041041249249249209249249040249249208241209249249208124124924a49249249208049241249008209a48249249a41249849249248249249049249249040241049208049208001249249248049349a49200009249049240208240009041241241269b4124900820900024104d04100004820920920820924824c24820924b24924820124904924020824920924926904924124924920820924924124824924924124824924800024920124924920800024904020820004104d041041009249208209b6000db6db6c249248200069249249800009249249040001849349248000349349249049249249204a2904324904f00800024934924104100904124120001924924924324924b2682082492492090000492492482082092492482400012492492482492492490282082492482402090492402482492492492090492412492492092492492408248, 1161363590353088, 1161372188938688, 457684747293120, 531501965722252339719154054923620842382943073863194746847215318581273412531203308930154874776620290245, 3957286895545320047684324152697190215460328994723811010032159418551240508765011011656093113401066740197270669707185544458374033086002083608781505870440065925052715137907707463, 183402028136003777047981820951956254012701938498, 
    2923059026708588703916805937637658523034563684163, 1128184905009217, 1128184905009217, 531501965722252339719151417920491632846355695692230599568003510796252425001259351840845563008562679621, 132875517170550389995170533287665926974926292182759724234016112881086454304316730003152848783060422469, 290547022434496, 
    1143784301793984, 532150803464395994019471120612925425581683005071228924699805323479776131689220120093646667019365939077, 299360311317184, 580835288289984, 366447260679601595232441744360331160705678013250, 1464361729683385958228367264307970878966786495298, 
    531501965722251867650610633661219106744185412828122805170181363005037459523381512813604447443378112260, 1128184905009217, 531502440922005843165252786462039503554732626320041788730406872687119042335871490349242237505337952004, 531502440922005843165252786462039503554732626320041788730406872687119042448678776989442391342697547524, 3957286427485527111778661891709499483189185650736353921291864555387401284297164156314711640975370513437841933193535298173972260951140545150745060827815217239379841723857320007, 3957286424721394476438137649976833315366653176154437649223098666730968447110778018860828294938687848067344550413720092278019129604307447871960093313879881416254084158365912647, 
    1128184905009217, 2923059026719907911147649695641101884030819315523, 2923059026719243297149786251924321154639581488963, 708382399926976, 708382399926976, 426898422239680, 
    145414847205568]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149228949a4924920100924924924824824934924906904804924100920924924924824826db4904d869004a48a25149249049240200224124949249249241009249249249248669b5934980802da49249240000949669649249008041049249249209249049249248069859049008004b59b59349008048a49249249208025149041249249348224209a4924920804004d04800c008249249249a4000934934104024900124904904024b003349a6f34c20824924926900034104984d008248249249a4100000904c04c04c249241009209249249248248661b79b0006182db6924000924094004924924920924904924924806184920804900004904d649009661e41008049004b61b79000041048a61249208049025148009049241240224049248949249249241041249249249049041049049200009269241041240a49249249049005149125149049049240200224124949249249241041249a4924924904944924930000894924100924924d201049249249240a4804924924900914924924924820c12514904024924934822410004904d241201009241049240001041241340040249249049008049200049008941049249249241041049249249000049249249608a0914924924820924012514800934925925822410492524924924904904124830824812492824924924820000124026834c20924924924904984924126c30c20104924920d20920124924924d208209249249a412092092492490012c9269b4d20112092564924924924924924830824812492504924924904000004904d069041249249249209249249040249249348241209249249208224124924a4924924920804924124900c009a48249249a41249849249248249249049249249040241049208049308001249249248049349049200009249049240200240009261341a41269a4124900c00900004984d06900004920920d20820924824c24c00037984d06d80924924924820124904924020024920924924904924124924920820924924134824924924124824904804024920124924920800024904034820006d24906904100924920d20900805904986904900006d87187184810006924926900000924924984000184d24924800034926926904924926d204a4904324904f048000249349261841009049241200019249249a4324924b34820824924920900004924924820820924924824000124924924824924924904820924924824020904924024024924924924904924124924920924924924104237986d84800064906da61041089089ec1200001259369a41ac9a4b3480448, 1161223936741568, 1161223936807104, 736459874770490077036656962443802855532167959362, 1128376031535937, 2924441672899911360232830692776385730388248536899, 17132569276842963758942894458877969427712709442, 
    2923059037416497019607617077339783922282026575683, 1161088708251840, 1161088708251840, 175926290157760, 531501965722252339719151444513067647797196131885407859134493585748542302296823136804969098045019258693, 531502947801800442927492800212129898576597156441523387471623721767592956124827686952767913430854527749, 
    1130453113376960, 1128329254211776, 581110166721216, 33218934237609691583666909999527528259666470571293729925408031746124785775645461420082708091324856901, 1130452643549376, 1125917221064896, 
    1128322341867712, 538249572559650780434327630488443664821067304944032966968481131831819520575861552226698631316437746564, 30916771933042085333677033581040167259693948064636813691768121346216332103619348066374811270878255721463881783066253609013140969715696206579767960912301408354198607275404871, 72708431876288, 531501997402235843687717581032614575861391224547131243810491947338227115546681171775854569142947646725, 3969483873812212976714719816551295906464006405796989642144884820698117717773515504152218902946852506597666881492936776927823583187995738983175183776715986691576178100842494534, 
    565373395538112, 531501997402235843673079058267166134448796812944094161983750665924308336210389914412386185359019707653, 531501949882260587742187637716363145845857935918885716942679724465223837801484237280994414070830687365, 531501965722252339719151444566630808713504228262014033289359296502016110568898290711894509389024032965, 145290695807168, 145290695807168, 
    145275193659584, 145139965104320, 145139965104320, 145290695807168, 567503160873152]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144acb2492d925960000924d6496480402486c82c80000493d9200019205209649040648049249249a4924930000926924d248208248249200009209249258208248205148ac8a59349349211608209209242001b71b6030c3081492d9018218201249249249a4924924124104924124820824826924924d26d34d60000934934d34c040269369a6800004d26d30000d20930934d040348029249249459251248018259349249201609a4da49a00001459250208040259249249201000a49a4d24d2010092c9a6d34d30100924938d34d20000924d24d248040249469a6800004130100020100904d241248040029249249241041249249349249044a4d24924900004d24d24924100534934924904020820820824920400020020124810936d24924844824936da5124835824944da5134800c249349349201208251a69a0000104004000804c24104934920120124924924904024924924904104924924924920924924924924124965964b04014924924924100924924924830124934924904014924d24924100924924924030020020820924812424806d20004d20820820c20d008661b7986366d8c826b26b2cd3092092092492080cc36f36f3cdb0824824924820306006986800004104104126900006c04db4d200001001009a40001241241368029249241049241249249348049044a4124900025900820820800900400020020024824f3d921804920510524924904024824924904124904924924900920924924920124124965904064814924924100920924924820134104134904004814d24d24100120924924820104104124020924812404934514924924930000924924d34104124924d248248249a49249049049048200009a0924924104124134926c20c040249a4924904900514912524924924800014924924920920924120800026814924924920920412494936924924000d349249241041249a4d24924834da49249049045a6924d24820814926180924924820100924924924000000000124834c04904924900524da49249000149269249249209125149860249249208149209249249204108068200009001009241049240001a0020004004024904904904420124c20924810000924936820104924d349240200041049a480410490492490000d8679b49309205a49a6800024c169269249209209124040249249a08109209249269208003609e7924814410512b22934b65964800824924924920120921b20b20000134f658008648149209249219201125129249249248040149249249209208208208000248149249249209204124a2922920924824906004482494524524124904920820490924924924826da09a418c1b6db6db6c30c24d26d66da0c600a49249249209348269061849049249249241201041200209209a6db6dbcc00024924924826da09a4006036db6db6c060240a4924924920936826906180db6db6db0db0904924924924126d04d20c00d208208008040008209249249240201041041019a6020820820b348209201241a0020826924924824020820820f34c249249249209041041041049a403cdbcdb6db6c00004004026904092124924924d24924b00004924d24924040104000187800024124900004909a69341060200924d248201340149249249241201261a00209205249249248209249a68208248125b6da69b6c04034d34d65a00806db69a69b0101924d24dbd9b8dbc1b6000924da68208248125049249a6000000024104d049041249269a08209249a68001209a69248200249209249208124124949a692493000052492492490402cdb6b2c9a0000b36da69a6900024d249249241008a09a69a49208000001241001205001049048048049259649241009249269241041249249248348249649e4a049044a2524924d248208208049241049204001249248248105249e6d44c30814924924924d208a48a4824924924a240061a4936830810924924924d201249249248040249249a49041049249249249209249249249241149148249a4da4d248124228a2920820824920900006924d34000820924924824000124924d04024924926900004924920900104920924124000124924b248041049848249044a25245105041249249048041248249049049249249249209249249249241149149124025249a4924800814924924924120b249249249040229349249249040228269a69248200000049048048149249249201201249249248040149249249209205129259249248208128001249248248149249249209204124a29229209249249269009269b69b69204824945245244908a48a4820824924824000124924930820824924920900004924924d209249249a40920949a6920004920524820800024800000820b2080cdb6b2000caa000402082482630002080002c800100820920980000124104120104020824828100004904d04800000820b20904c308200009204849218600009209249201049241248200200348249048048049044a0824934d241008069249341004001a492492482252492402092481052486000000481492080080012000002082082008010082092098000012410413000402682482a0841009a092098003010412416000002082482c000000986000810820124124120124820800024824924804124904920800800920924100100124164b64965900014106924d24c208209249249041041b5134941814106d24d24c300209249249041041249249208124000269a4826900006db4006db00009249249a6000134904036c369a6b26902000924920924000365004134800024924926900004d25930db0928924a2c0800209248209000000001000000009249248240001041040008469a69249800049249049201049241249240001249249248041049049249044a45225100008249208240001b60059b7800024924920900004904d30de0d289a4a26104020800824004124904924d0492080080092092412412492431491491240002cb2482490000d905804d20000924924b2400012412403686c92cb249024825249a4c00934814924924920d20b24924904024822800804104904824924924924120000020820824130d249040248121249249040248149249249209205129041249248248149249249209208201248209248124124a2922900100820920b069269b69b09204824945245200249249209204904928a4000b2492092402080000400080002492492c900824924904021b2cb249a409208, 1161359291191488, 1161359425540288, 1161359425540288, 1161359425540288, 105624528554049, 105624528554049, 
    2923059026737479007375425761442089216273257891651, 290547021648064, 1161363590353088, 1161363590353088, 1161368023863744, 1161368023863744, 
    105624528554049, 4217239420481885636210232966340289828250149733726928783093352156513225234754959843739967953001791620, 371085815683523277197194658833636730835751162690, 371085815683523277197194658833636730835751162690, 105624528554049, 105624528554049, 
    1161368023732672, 960962154094212046835217857624440951243359382280253876264893850380835515611741996856708671079025254350731094848425145796623168453896190240269858365617863227668398236089863249564802476723289549794058256179038036245182003101161605902052319295054911639247667209246991112, 6707465088723695756462041669331607964978116025472644350312872008527489413480729830512419985040705341679014593577293636015152851719097600080060587064390093537934797085498020123474091990892841928670870054808072299412796995442080958840777967305268552177695249957244036934608956092751207649814188340672475331458066490272673911114669261455367053602801241014268454621369879103925342282, 2923103628360840061931629001074405107699049110338, 1161365672890560, 3957286482768179819956743135535386095930348178230646954065738028966237612095302773053601914450469100015392539406461267834458960449239216820326939892006705969458722944478838342, 
    2923728051608344334045009583117213363704120234818, 2923728073386415816985071244773188239337285768002, 1161372188938688, 7759266745547319253286405420057648018066864838672616857503613119803756201174864708723931142728944457001551147887345846520452688574434985370577031972148370381021830207994439, 457684747293120, 457684747293120, 
    316943093993920, 316943093993920, 371085815683523277197194658833637856727068070722, 2923059026737479331895217359908101379704177592131, 2924441672939788230529992574441005578117548377923, 368231309409075616123813067285691943719626888002, 
    365733616418933912545684089864669696841167688514, 366090429703239870199702515210530500352336220994, 531501965722252339719153615275532006652570137262412858188274824630842858430845092499590867553765216453, 365733616418933912545684089864666319128562258754, 365733616418933912545684089864666319128562258754, 573029569385977991062543329206871533031607703794336986393630119107048318388191402639656131312520175748, 
    589639004577298987863247018000754467723838762161568901030871583389256377197630708834600064846559092868, 366090429703239870199702515210527122639730791234, 3957286895545320047684324152697190215460328993337475832443767591232826335975409918193526530398535854438722306993357705748399648561359926244415143858328033334515813041969974855, 580834751943360, 290546217128128, 532345381924043839394585579883518760766813799403198470323167934873088069873793464583804172138570858628, 
    299351445344704, 580834751943360, 589639443289024, 290555083887040, 290555083887040, 290554815451584, 
    290554815451584, 290554815451584, 290554815451584, 145427748885184, 154224118731712, 163020337582784, 
    736462602479280687221814511196224166611755504450, 580834751943360, 580834751943360, 580835287896768, 580835288289984, 580835288289984, 
    580835288289984, 535719680387928928508261480024970401444234395048665818726322902052461522331132749310634829804285150276, 145427748885184, 532475143136476034682091077451801690103529327796605807023763891870137536695965346756686447363676717188, 532345381924043839394585579882313327631432159996699317530722950499989527032300613490233454023581909124, 105639091177537, 
    105639091177537, 105639292504129, 17884798522048, 354321989374144, 283953446523072, 33218934237609691583666965009206201264992175936726138166541215081749984203085941297873794916599517445, 
    72848018313408, 72848018313408, 283954251043008, 283954251043008, 365421404795155814697691617168091148319335650114, 565716458684993, 
    565716458684993, 565716190249537, 145410548043968, 286148170617024, 286148170617024, 286148170617024, 
    290547022434496, 1143784301793984, 1143784301793984, 1143784436142784, 2925868931314211233750039684930286717407825302338, 1130590166454976, 
    1134988351509440, 1134988351509440, 2923728051608375487825929132853392514083903853378, 72852317671872, 79449387438528, 79449387438528, 
    105639091177537, 105639091177537, 105639292504129, 105639560939585, 79449387438528, 25690556512605786755728698461259928835195406147, 
    105639091177537, 538833442545653603971549898359340949138139035875343555794027661603074843226284019830748529924296163460, 538833442545653603971549898359340949138139035875343555794027661603074843226284019830748529924296163460, 537795352846196041671505917809303984629307067977304899710566740789200434624231069170398271956731576452, 105639091177537, 589699837819074158287220465640199794940294362884597382124424433202081580026956498315423974357863669892, 
    589699837819074158287220465640199794940294362884597382124424433202081580026956498315423974357863669892, 581395120223413659886868621239904078869638619700288133456737066691086311210532893032621910617346973828, 105639292504129, 583925458845267980549659432351538066009591859866842404431927786103222411337374398963862935378097285, 589699837819074158287220465640199794940294362890688827412714848679377385276826900561737105809799815300, 589699837819074158287220465640199794940294362890688827412714848679377385276826900561737105809799815300, 
    565716190249537, 145419280585152, 149817327096256, 149817327096256, 976699353505545380826580284877520846237313370823832512863114942533191954699736407355762870794418620034426176628734863109866748954243808121748479435376113563294841633282431643826228133490682269559413845162472587986846040920853157243152299899599800760337956904749554312, 290554815451584, 
    1461529556906314653900893307435014038844078101058, 1562283826109727050376938259828334937648753047743498104504564670668641427751756499369763072432789159437029274078261171316735873461737742528858929459841967522569582070147988437342773133955037450817556483580991416787870655791194956317728665244153384401945772072499877512, 536173836651502472713914947874397287372450340484861844360015307411017609996312711275585223616283034500, 708382399926976, 3967672427131056788308956829268865824658456987278220319423362771574025524348256775675854182128105910118180294204856902360070247850838893500186156380034177327811436263487012422, 708382399926976, 
    426898422239680, 11440630823719329552277192313789707955868799554, 91366501617913810513003605409236749197976277826, 365398058617465896121540455782912976648570688322, 365398058617465896121540458144096218083393295170, 538379777262849792601508406541496302455127224424086513133487390077685692352759756574456907328454411140, 
    708382399926976, 290555620757952, 580835288027840, 72845872926912, 283958550204864, 72845872926912, 
    283958550204864, 283958550204864, 565716458684993, 565716458684993, 565716190249537, 145414847205568, 
    286156768940480, 145414847205568, 145414847205568, 286156768940480, 286156768940480, 290555620757952, 
    290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924920024d2052492482483481400ca24b2c82c0800249acf2098002492592412092492492490480002492c920905834820100920484924c201009205249248248648159249208259208a00001241209203369a6106b24124924924804820804920825920f36de6000f66090492524004a2c9368260a400482492c82c000dc6de70018120924a480002490680481480082490480483cdb6d86d86d82412480024924820900820020100000000b24924b2402094c96490082892cb26b02900024924824900820820120020000924924b2402092492490082492c92690c48, 1161156223897792, 1161224003915968, 387314253637953, 1161155217264832, 1161224003915968, 1161224003915968, 
    531502440922011507987688852142983278718900467173717559023594830312502740658227287849118750411233444740, 531567321528223829083115114109994311430434659402829629512586854342111027059073342375895258959303689092, 28545062745806169907672288095148337286252335938, 316943362040129, 565701960536256, 2923059026696439057511347221835829103482590204738, 
    2923059026696272904011890994598822473709322769218, 1128376031535937, 531501997402235843673079140808834435517016212640303952677106616814697913329596705104777829797796040965, 1130586127741377, 11440761574726576962955716297148793922420478530, 73189470769344, 
    11440630906297679322585746361299540123427279426, 565701960536256, 11440391347511366981907468145575908158606414402, 75388491927744, 567900981694656, 90781673591488, 
    581095138005696, 75388491927744, 565701960536256, 1128376232845633, 1134979745063233, 1130586127741377, 
    1130577403584961, 1134979745063233, 1134979745063233, 1134979745063233, 531567321528223829083115114109994311430434659402829629512586854342111027059073342375895258959303689092]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492410080490492db31865920924824120020124936c26c348148209a8b3c9a00841a69acf26804104d359c1820800136d24c3482482483cc00002524920806024804934d20004920524934c001648179b4d60005950f38dbc000f3a067134c001658371b8d8003cd80000124000920336dbc000f0a02080410000480ce36e0003c280804d30005920f36db6000f68090924904020124124934c00064824920804904904924c30900d20726000a269bca200a03071b79c79808209a0d3000030c1c6de71e6012124b30c06034814924c309b0d204bcdb61c0c071819bcc30180dc0db6d86db61c6092306d861b61c600080010000483c1b61e6d86d879ecc361b0db0416520824100904800004d34037820820824120020000130c240348148ac9b2600004d608079e0104006020800000164c219e78041001a09b6104d379c5960820904024126020934c041e6824920804904904924c30934d207268a8f120001b1806c610000080301860000079b0d80180000d801b0006336e66db7000024d04c24900004d35804d6000093413cb2400013cd0406482493ce24b0c48, 1161156223897792, 1161155217264832, 1161224003915968, 28545062744809569627808834671626492982492926786, 8369598697843136523389518661119113140007740822697123552094059711080353481196289842363703274600051397, 387314253637953, 
    51381112941387784284643108696242918232703374146, 583925464646046181221072788967444589938410699174705280431431772368264548952785396015890797198327940, 2928713681009934868167378245082692871195071627843, 1161224003915968, 1161224003915968, 2923728051604014589599319376093750509309591032642, 
    2923059026695608611999088599620482295034789499714, 2923371238319376324946354721798110498107061965634, 1161292656283840, 1161567737680064, 2923059026695276303732182286557903658906076320578, 1161292656283840, 
    1161292656283840, 1161224003915968, 316943362171201, 316943362171201, 51381112941387784284643108696242918232703374146, 316943362171201, 
    316943362171201, 316943362171201, 316943362171201, 1161224003915968, 28545062744809569627963577766832975884150903618, 567900981694656, 
    567900981694656, 567900981694656, 265751002661115918839352464884297205992486017696398016322007986673533741532379954866959939174498867844, 565701960536256, 567900981694656, 567900981694656, 
    567900981694656, 572299036594624, 581095138005696, 316943093997889, 316943093997889, 316943362433345, 
    316943362433345, 316943093997889, 316943093997889, 51381112941387784284643108696242918265989370690, 176210034831809, 371085815678528917485961395983617312409258038082, 
    1461551814178073752873021556102465442945903366978, 22881000326863946706263625876954302288096139074, 73189470769344, 565701960536256, 22880673485650519144869469305643864074729035586, 75388491927744, 
    567900981694656, 75388491927744, 286700884988096, 567900981694656, 79786546827712, 75388491927744, 
    75388491927744, 567900981694656, 79786546827712, 291098939888064, 572299036594624, 90781673591488, 
    308691142710208, 581095138005696, 75388491927744, 105839008948545, 316943093997889, 316943093997889, 
    176210034831809, 176209900609985, 316943093997889, 316943093997889, 565701960536256, 1461596415859547418375374079757923800662105135938, 
    1461685619180623907788878704983854933018478121794, 1461507213219035662803746381458741883169268568898, 572299036594624, 581095138005696]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492492492080492c3359018009a68249249a4124906da6d34824924904d249249040243349218059208009249241648049249a69a4100925864b20300124906da6034834d00100001904d04db6c00da41049001208000059a690496400000406c800000904804920005920c60db9b00f38104124020164c00c37b6416cd80924924924820124924164000026920924924904924924934100820924924164824924b24124924186c00024900120000004924126981800d2480410498402092082096480413612082cd00804820005920d2400400480410006c004180984d04004c34864020800b0c90c80c1b600606d1848145041208209048000249269a0004104820800120000964dc68201269a896482c8000000300360000671bcdb8000006030c00d800019b6e36dc63679b6f46c20824924920900004925934000820924924824000124924d0402492492c900004907b008001040008000200001059a4060004100000000104d45b35930820924924824000124164804020824924924904104924924120924924b2400012498690480410002080080082410696d93010480010000413cd24f6480, 1161155217264832, 1161155217264832, 1161292656283840, 531570869687339291747103522372062087863782221039299958983065813140202029022974143058101607814171437637, 1128376031535937, 2924441672902569826365605326348028556482439071555, 
    1161297018294464, 2923728051608334598332112241477757516553427896131, 1161155217264832, 1161292656283840, 1161292656283840, 316936651546945, 
    28546369434083170030383638208424249678071088963, 176199297413569, 316936651546945, 1161155217264832, 176063729111232, 1161226147205312, 
    1161226147336384, 1161226147336384, 1161226147205312, 176063729111232, 176063729111232, 176063729111232, 
    1161361582203201, 1161164019012032, 316668216086976, 28545062744809569704561117111931756036344517442, 28545062744809569704561117111931756044666016578, 564785685032092663086164932221496120079313509055889068652369187786417989600934256705471729833634354309, 
    72845070704961, 75044093960513, 75044093960513, 72845070704961, 16674323718499770506960884831016262817580557523772610088331808527428408066922568319643293572740917445, 2928713681009934867830622286622481525316876517955, 
    33283751484824631724445106583429594046309940316236151688569296861329201035390032840713185699573978245, 371085815678528937844659062234706516444677412674, 28545062744809569704561117111931756036344517442, 66502625332464833965431435452388194465993875051663214039238517519425291935965909667125592072961108549, 2928713681012593648340898099677408363679557109571, 316936919720257, 
    290548641440065, 17127037647018925489179711767971564913915073346, 583925464646046181221072949971383367868688667520576895305075788083272698204492678550798822791200900, 12993372403592331447569820076407047088587792363790735895221254607475192483360961638664038303661430294765835743130046243474669761460028988889658400410425443504495305649850795974005259943698914780548995696255584002190697061416773070478227839742459287813720161084461075594162814715183666932040790090327116073000748629384652796539326380261015691033725154249728388964698047074378, 513258889805605223322660477602494454133339262160886516704480203820253419458253914350972125777543032348092572098006614054799296552189570929328094346777779444370562781016646, 271725524954383304586472866144771714163632046376573657583036496406028162127539411997382193187703672876525879464315482449751927617510684916093884513547499632742433914662471, 
    538833434641126470158863430298939283618180091511190056501349045271004643505026614508033876587184406660, 28545062744809569783944022721402576522956510018, 3957316615503016392003724570384529582008112019250197669433848659546781744179587640342077201018830065621498424756112562272985006312994284599312535465403735633667505586919484999, 583925460778860723712888582099190564098552566730646806261283819408350182722314073922884646105006788, 4019149215871292525518850200639441379516894856525500629412364423570006050456220607134656301284140826868897842612618204045867433938213009704774759564624119467794632051298184775, 28550550818823270679482760027071236080670872386, 
    2928712374325645891426958855038577426204333195843, 2928712374325645891426958855038577426202185712195, 149810884649281, 2928713681009934867830658554397078408471483793987, 11441676171150510360836522770451774291432194627, 265751028401102427289069447553604734446076100293965825731499510086996050333147038708817375916554763332, 
    290548373004609, 290548373004609, 290548373004609, 387305663899969, 316936919720257, 316936919720257, 
    316936919982401, 265751028401102427289069447553604734446076100299784519738224682815082608129062040237245122965466823748, 290548641440065, 290548641440065, 290548641440065]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924924d200205249249249048148a59249249241008a09a4924920800004924121920524924924864804924d249201005249249248048159249249200208a4934924920020f369a69260040a0000124920120336d86f060001249249248048104925248a4824924924924006db6db6c618120924a491490cdb6db6db6d8241492292082492492090000492592582082082492482400012492490482492492c900006db79b0f001861b6c060360001b6db6c36c061b6d86d86d84d349379a048, 1161157364748480, 2928712461435606628737923424034265940623999638082, 316934504063297, 1161157364748480, 150958497008678147900342096783323651760357579299909774066252647724688858636897927280121592335276146720256004758518665730480430523493812033499157857428449624940523000475206, 176063729111232, 
    565703567478976, 72709636624576, 72709636624576, 143628541366464, 565703567478976, 567902592831680, 
    581096744948416, 2923036725865007830418698815753344038784609555266, 2923059026695276952772074967337460339004057588546, 567902592831680]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492492492080492db259618209249a49249a41249349249348148a2964924924904024304d21805920400134924964804934d249200005249349658008179b4d65960000f36dbcf380001e79359658000269b4d25960020f36dbcf6c0000bcdb6f3db00000000120920120336dbcf08000020004804004810924924924820124934964c00824924924924904924d249241207248a4b12124b34d24804014924d24924d204bd9b6db6db6d879ecdb79ecdb089290d9b6d86db6d8006cdb79ecdb04144acb20824924920900004d259658208208249248240001349249048148a292c500006de9b30c00000e3c360f000001e6e36c60c00060d80060d86de7b679b0820924924824020934964c04824924924924904924d24924d207248a4b1208, 1161226147139776, 1161226147336384, 1130439822020800, 1161157364748480, 1161294803767488, 1161294803767488, 
    1161294803767488, 1161432242852032, 392492092204286347247775334314785778351253039484107476024848921916042872471761895008408897642338783177250631977705164784962687080597130537505440814542701937420706105306694, 266594411932911499093405665547400227067257444511945599032221132490444587792440241876037958465204011140, 316943093997889, 316943093997889, 
    583925458845267980549659326692702849383006794209622847824523274213197670086846116716138596619534468, 961842399437839889284103792053779316418144121300324526075100356846211720569171805484685472171950815361702176782153571889589634619172553700191414456730650183447088590370898019705028338699199254107209764162217680138693152308877217503327225176933144856281219112246956552, 996326080379589994946213082928518195668409667751262965255904231206526695156042236887161021068148811626033901023903585677787070237304415556163083385447615092688813301083718, 61862792071275594269988712526260074203609479863323162541840140773099912032995381132605153023083275956720124911445761095047248547016551656462960661151896966475982029045542470, 176210034831809, 316943093997889, 
    316943093997889, 1161157364748480, 583925458845267980550099404125362525459897754038882129028309917989725944007031715499269907185680516, 176063729111232, 176063729111232, 1161226148122816, 
    1161226148122816, 72851513155905, 283957745688897, 283957745688897, 283957745688897, 283957745688897, 
    22858786674345843384792710378420107701557141058, 565703567478976, 79448582922561, 141429516013760, 141429516013760, 563504542126272, 
    563504542126272, 563504542126272, 431975476236736, 572300643537344, 581096744948416, 28545062745808441546213477357089084672923669314, 
    316943362957633, 567489869123776, 143628541366464, 284503472869568, 565703567478976, 145827566719168, 
    145827566719168, 145827566719168, 286702494027968, 567902592831680, 145827566719168, 145827566719168, 
    145827566719168, 286702494027968, 567902592831680, 163419769541312, 163419769541312, 141429516013760, 
    141429516013760, 286702494027968, 563504542126272, 563504542126272, 150225617424832, 291100548927936, 
    572300643537344, 163419769541312, 163419769541312, 308692751750080, 581096744948416, 141429516013760, 
    141429516013760, 316943362171201, 316943362171201, 316943362171201, 316943362433345, 158471543591104, 
    1461551814199011120787061872931106287209282541378, 567902592831680, 567902592831680, 563504542126272, 572300643537344, 581096744948416]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144948a4d2492592002092492492480482482482c980004d3513000192052492492486480449c8a492d92592010192492492486482082d8200019219249649248648104925248a48249249240001c6db6c66c000120924a49149049249348308224149249249261269a6da0c20da0924924924824924b240041e6db6c30c66c241249249249049249348308348249a4925b30100924924d651259e00609249249248048249249ac9800041651600019009649249248648029249249248249249240060079c6c67800c241249249249049a4934800806db6d86d86d8482082082012002082492492493c8208249269a51a0824924a2493482092492492080c9249249249a432492492493c80412410412c900c66de7b079b0000800100b24104de79b6307b36136db6d86d86d84db6db6db61b6136db6d86d86d81836c30c00d80800180030036c06db6d86d86d87336db1806db19a048, 28545062744829689855352168854467645200748516162, 28545062745826610851591226265220590392357950274, 28545062745826610851591228552616855532342350658, 28545062744829689855042682664054679465883603778, 73204503154880, 22880673485670559509960759824413273329800058690, 
    75403524313280, 90796705977024, 75403524313280, 28545324082684409935282928968888252121416209218, 28545062744829689854738032195366916218884723522, 2951548337407964754257892613500836973732427731778, 
    28545062746158917850522948068270934386202907458, 62225092464079550898007962695475014093282875823374457071543714614612159253635330274584022356821348360470357339971089808366508403511961527144865183358686642773122496211496518, 392492092204286347247775334314785778351253060976359138357167161372283791033769235926792519972834204223440672704380887257064991976169224146698661341217963224008755099512390, 28545062744829689854738032195366916218884723522, 72851513155905, 25690556475346532550749095675819675939309111107, 
    2928712635661194888245720018964058282410597421890, 72851513155905, 22880913193662718179838306737398909347980908354, 44950111031974080807851161376330137523458882, 22880913204961156144155163308837347072615126850, 532021042251964506863589615773938111467296454239710301906347019814134577582466442432345853018337723076, 
    531501965722251543103487040183268616042994127252718152040478862918073334654987220840400689361691360452, 532021042251964034795052322106484461517489087093285626696686173220015170729070556335186858976345342660, 2923048573223310770596151351600733373213549041474, 2923050663926148531240394478502529663218298656578, 143220257333569, 532021485771740171149387539381965305198837681519231278569204069483784005157117256246948389968859644804, 
    145290293153984, 145290293153984, 567915477733568, 17609920615104, 158484445270720, 91388541106358686388607393017927498785911477058, 
    45694314204870956538933785402811760471852457538, 283957745688897, 22858786674365281608276180633181363978027146818, 567916013621440, 581110165934784, 565716989251776, 
    730778716555816963144499249916175276195891384898, 1464361729701974451891127397486994667343838253890, 1464361729701974451891127397486998045056443683650, 567915007971520, 567916014604480, 567915075080384, 
    581109361414848, 581109629850304, 581110166721216, 72654746882240, 72654746882240, 565434869883201, 
    145290293153984]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249269a4937b20000f36db73660001a49349a4c01030804900001920d86db0000330124934820804c06d86d80d801805249249249249049e6800c36db8d8618cc04814924924924d241049200300669acf3c0041069269bcd001004924a09a4924920800004900181920824924924924000da6de61b60261349049b1030804124924804c2480492492493482082492492c980006d87b09a00824824924924000336f661b0c019b4920800000340dbcf00000006125926c60c018379c6f061841b0d36dc8186101036f6720c20798d864b6db0c1800049069a5920000db0f60f300001059241640000049000041004049249241040018379b0f061801249249259209009349b6d861840619b7b3cdb6164024924d36b24104124924964800036c3d83cc04124124925920061935b3cd2400, 1038105554918292487075689487044752358051168062468994626080348651174768673781221780072616692206024196, 4152422219672461384471281883428742727594239129141489229946656763141875306557414490565645357596033924, 532021042251963798731965622455631172017132408844606764731113172841286066833153412599976451936578978692, 532021042251963798731965622455631172017132408844606764731113172841286066833153412599976451936578978692, 2076195269844596962911890946643072449210920604273551882234328870409941646325922433317933375553811972, 1143784226431809, 
    1143784427758401, 1152580520649537, 1143784427758401, 1143784226431809, 72709636624576, 2928723421255084513510478008657322381883329266499, 
    143215958167744, 143215958167744, 283953446523072, 283953446523072, 143215958167744, 72709636624576, 
    469219808792220334359155696537160104036701585881731916329728125240356865873663177705343839088608483834214211587960880050376222141844678957643658472947339802224262392054950095484158136462251662686618629053058313999637615425374652174358689670455112377565192249197512, 15841925580783211757048864925179640952022061671642955336157219821607217464906775209684223921540, 538379333743079793109418344046343546957850711818184836902051539438418993824563242578658939354399129732, 1134988133409601, 2929437042379178558083424490248302874416539288387, 1134988334736193, 
    1134988334605121, 1134988334736193, 1134988133409601, 72709636624576, 143078380802240, 2340892446912, 
    143078380802240, 143078380802240, 283815869157568, 143078380802240, 143078380802240, 6799168915614215471804887295687208686934898452301474030597235386912751795548774591887410705237135485267299173700765540271387547723460990871852363067732057982082514741785853613121115296284055626988828261395544930972374711594167558277196805099156616827668220067844045264171558522297318561320469766087807288324539709646019553375958353266082237336510810925896789000397560508531019851, 
    2928723418532825578142970300950325522429183574851, 72847213990080, 283953446523072, 283953446523072, 7729078731994588665907057222071600211627729283230562191323110168922294317599332674089163925605611040609286687945015031645508668233565061000429562908226815344824395549880902, 63363835137531266384298561702826565616481586735310249891959194630347365439883676408742207571844, 
    539547184653035249620496659277723119128842005643163713601757210351003105967433125718488465064554045444, 72709636624576, 283815869157568, 4152422173266235548606349011125249007817112903058336362078889168610293522085250425944891144699920516, 284503472869568, 265751028401102427289069447180654201188962128707988577221482074904170853788449525467275304035596680260, 
    265751028401102427289069447180654201188962128713807271228207247632257411584364526995703051084508740676, 564720860112381718081544946717173679720832930477390876408758754429640921868500632059720314176241455365, 4152422219673169487284364839639592968736852436294631928642832964774030998080889775867409532229242117, 33218934237609691583666965009207839081752205338093664187707751524313407659609610637652021960922157317, 1128391264969537, 1128391264838465, 
    1128391264969537, 1128391063642945, 283966872494913, 531550657856897444840950424683310771935430631770051315350461454957115042259804461707131979622391235268, 79306706391232, 79306706391232, 
    79306706391232, 79444283756736, 79306706391232, 551485157187413703439291501099138753684484580099216313914057453169983749305971265509013640051966660, 97049358902081, 551485156945714612344934677186017527250719757583596372709966876408475367869309958193061578078962372, 
    532053411279217730194372624496281262155540255786839330266022633567390299715615158055682417868717441732, 159034603737792, 158484445270720, 159034603737792, 17609920615104, 158484445270720]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492492492492c9808049649279c00009249a69241a4126d2696680402482490c00000496492000192092092c90006480449cb249ad925920001926b2496486082482d920001921925b248608648109249249249249a60201249249249069048248201001861241144ac89290498c03004082c416924926926da6da0000da4da69b6830826926da0000d20da4da68308348205249249a6928a348060269b4924920f20820928a0403683c924924920f208249249269008029a69a4926120134924d44c000149249249240000a49249a490000cb26b249261841249a493483080402410412c900004105b059204001000201648049659e7b2630c164d679ac9b7904db6db6db61881379b79b6d8c306db6db6db00019b6db6db6c30c379c79b8d882019e4d608379b1b30dbcf6133a0061041a61e780006c04d26d2009249249a4020124924964800824924924904904924924924120524b2cb64860824924924906184924924d20c209249269240000a4924924906184924925120020100904104b24368249a6c2694121a6d249248368249b6f36de6c060279ecdb79e0db09a6b349e6800036e66dccd80c069ac9279a002082080480000480826820d200c0098092002012082482490000090282082410002010410406016081410092400092008002480002090410410180592000082410082000010002010482482490c024b0c507b0c1860601e60379d798b987986de1b36de1800c31860c30300f3a0061e6c3006140006000c030d86f66db1806de19b0924924000124124924800964824924904104904924920820d20524b2c860b64824924904120984924920c24d208269200008240a4924904126804924920020120820820100a2c18618606036d81208, 97053213331760485995360497733358229019544261442, 97052864883447526451756370831644468116000346946, 97053213331594332495889801110107854432213406530, 97053213331594332495889801110107854432213406530, 97052864883447526451756370905431444410838553410, 97053213331428178996414268765132242069967868738, 
    1461546326125036362266824436556710703101244348226, 1464361729701995221157789699309467283913485390658, 1461680392443508891667821314267413995624847119170, 563517963112640, 581110165934784, 22881000326904756338017218215926513900619568962, 
    28545062744850459122014470679246104779609346882, 28545062744684305621924801675169763435500016450, 28545062745847380118253528089999049971218780994, 28545062744850459121550241393626656108726719298, 28545062745847380118253530377395315111203181378, 583925458845267980548574051125756360137550170605739096965369916127912911741064904761357853610229892, 
    583925458845267980548574051125756360136024834892563611088671640385556826406491718460571711812419716, 28545062746179687117185249893049393999423476546, 150958497008678147900342096783323651760357622541387304231125849217792175470732398426648442136697328356409850441346395074189226089016179157090345619994393281437130219105862, 28545062746179687117185249893049393965063738178, 28545062745847380118253528089999049971218780994, 28545062745847380118253530377395315111203181378, 
    28545062745847380118253530377395315111203181378, 28545062745847380118253528089999050005578519362, 28545062744850459121434184072221793966842975042, 736461225016249006906417373383265192943089107779, 28545062744850459121704984488833139044744434498, 583925458845267980548670224145544649568109150256337580442046286870812283086235886485083984033497220, 
    75403524313280, 259775869566404136366974259107113228376949475728725082403981668347578481261038048130802896106430724, 75403524313280, 75403524313280, 28545062746179687117185249893049393998349734722, 28545062745847380118253528089999050004504777538, 
    28545062745847380118253530377395315144489177922, 28545062745847380118253530377395315144489177922, 583925458845267980549659432351538066009591865322540954193979902099417714847513694446267643050868868, 28556126005163792673338591914482926427700204354, 17127037646872890872075751183139343257636442690, 97053213332591253492742957401029665648524923714, 
    28545062746179687117185249893049393965063738178, 97053213332591253492742957401029665648524923714, 392492092204286347247775334314785778351253082637841123676033252122212427502611796581984066109858369577111819098855247371639848957389483190259610111610454758116172066238022, 97053213332591253492742957401031635980878091074, 143091267801280, 143091267801280, 
    140892242448576, 140892242448576, 145290293153984, 145290293153984, 145290293153984, 145290293153984, 
    140892242448576, 140892242448576, 140892242448576, 141442400915648, 141442400915648, 145290293153984, 
    145290293153984, 97064363704193597807460568969244178612966396738, 97064363705522825803245484842148196814644319042, 97064363705522825803245484842148196780284580674, 996326397721721777536927936207315319147508386699035717736553189003877388964674305912827072629660319984015312857295312656514387480496318655961912150719304931535825692438086, 996326311342576922307557386244975971582157673075422473953373728386558963944644322779932899009943582483456123709169013488675351007494619835497327887028903507426191529389638, 
    51381112945385219354841983919417053482540090179, 97064363704193597807460568969244178612966396738, 1461546587461894157547022775595194401902905268034, 709065031291584, 581109361414848, 563517158592704, 
    581109361414848, 145840451621056, 97053213331760485995360497733358229019544261442, 97053213331428178996414268765132242069967868738, 97053213332757406992199184638036295421792359234, 469678024263016139997925101829823845339487915731428724891007891899013807755129384971844749710331231091905719115307644788498851759964453948842020427730968316483347339314746828636731025987738762098015154944262993317563079995738909377315314064730841010929672247924552, 
    97053213332757406992199184638036330606164448066, 97053213332591253492742957327242443062142571330, 97053213332591253492742957327242478246648877890, 97053213331594332495889801110107854432213406530, 97053213332923560491674716983011872633891328834, 97053213332923560491674716983011872599531590466, 
    996326080379589994946213082928518195668564958828724586391547871368461467107988850245599439701271454222112631305471631393510347474886534368434332217615188170280731904486982, 996326080379589994946213082928518195674065935503967398973470362518960575219961199092598099713271488029593870868527384770996876078087251605313137819061613043495158108302918, 97053213331594332495889801110107854466304709442, 97053213331594332495889801110107854432213406530, 97053213332591253492742957401029947124575376194, 97053213332591253492742957401031635980878091074, 
    97053213332591253492742957401033887789281710914, 140892242448576, 140892242448576, 97053213332591253492742957401038391406088950594, 143366296703680, 143366296703680, 
    158759457395392, 158759457395392, 97053191565153594519096022936599644786600710978, 145840451621056, 141442400915648, 163432654443200, 
    163432654443200, 143641426268352, 143641426268352, 145840451621056, 163432654443200, 141442400915648, 
    163432654443200, 141442400915648, 28556169561306758552845360706469347416963289922, 28556213117449724432971101879281699978498544450, 97064102368665030522505544970449689216657920834, 97064102368665030522505544970449689182298182466, 
    28556213117449724432971101879281699978498544450, 8814087640000, 17609920615104, 97064015256046791763327138764576705456193409858, 299360311579328, 299360311317184, 
    365466006455704443988878930754779672181787870019, 736462597040100518019010362522298420327224447810, 736462597040100518018391392502655730189774885698, 563517963899072, 567916013621440, 563517962981568, 
    563517963374784, 563517963374784, 565716989251776, 1461551835806980362641955603786665879041050941250, 1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309470661626090820418, 
    567915007971520, 563517024374976, 563517427028160, 567916014604480, 567915075080384, 581109361414848, 
    581109629850304, 563517963899072, 581110166721216, 72654746882240, 11440325928267459949207791059222699318261584706, 72654746882240, 
    565716988727488, 1461551814183099266523630162741219235888042690371, 145290293153984, 145290293153984, 567915477733568, 145290293153984]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a28a49a4925930100924926f34000126924924804c24924d2c9809048049241019209049260043261269249248040349241a080c9004a48a25249249ac90000492492492402410492496400002412498010c982924924124324012495924924924100b269a8b6600016492492496486c9279a49809028ac924d35120805968decf36d80004104924925920000820b60b201649049249648009000208009004a59a69a6d000049249a4d24c240a256490412492496480002082d82c8028248241243240209a4924920804004934000000824924924b2600093412498402490012492490402c800366238f56c2082492492c900004905b05930824824924b26100000904804805834924100920b389a8000b64164d2492480406c1a7a208069028ac1a4d00004904004925934920000820f30b20164d049249640000000208209000049059649019204a692698002c1000241079841009a49a4d241a40a250012082c82c80482482492482400012416412406280, 531501997402235843673077274021725842911483841064560594136337044486619117881436770573870099296873104068, 1152580520584001, 1143784427758401, 1143784427758401, 1143784428020545, 73204503154880, 
    531501997402235371604539981213064686716613139783140172416962443529101956399527478546968724585442460356, 531501997402235843688392962931064486575976894963942546720275843055127749389186602021773335356435184901, 1137187357795137, 1134988334605121, 531501997402235371604541320768351005639881617153583958151936387206894233175824525030588783358107730628, 1134988334736193, 
    1134988334736193, 1134988334605121, 565725603566528, 3969483873812212976714719816551295906464040476362190998717879358579827418855021610247324460582908488221892672143347382398468153799149236520720641847483934058092046016472644166, 565716988727488, 565716988727488, 
    1461551814199382371272979595887951723894296024898, 538509094957445109129173573122060466017291425475275499824027287071153143921452258981197854587650096196, 73204503154880, 565716988727488, 565716988727488, 1128391063642945, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 531501997402235843673079140701184017111672217376334797014934291090638954283417228028370802200447139077, 531501949882260587742187637716364374208434059312798157312257075184465763245633440775324378304998580613, 
    531501949882260587742187637716364374208434059312798157312257075184465763245633440775320103403789787525, 1128391265755969, 2923049270124277460077097004029400700235638982467, 531502440922011507987659837301142041274031040853228480179348581693000063040078245332738033068068324036, 1143784427758401, 1143784427627329, 
    1143784427758401, 1152580319454017, 1143784428544833, 145840451621056, 1134988133409601, 2923728051608375487825853648195290108849310221123, 
    1134988334736193, 1134988334605121, 1134988334736193, 1134988133409601, 286014892413120, 286014892413120, 
    145277404057792, 145277404057792, 1134988335522625, 567923824399296, 145840451621056, 567915477733568, 
    567915477733568, 2923718295032351130678381551552889706819079979843, 568056809001152, 145840451621056, 145840451621056, 567915477733568, 
    567915477733568, 88032875188416, 88032875188416, 97049358902081, 158471543591104, 88032875188416, 
    88032875188416, 532053411277163287962389350442714345972601651671339629107911590887843657463443683495253178715990271620, 158471543591104, 158471543591104, 158471543591104]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b9_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_11_0
  · exact tv_b9_11_1
  · exact tv_b9_11_2
  · exact tv_b9_11_3
  · exact tv_b9_11_4
  · exact tv_b9_11_5
  · exact tv_b9_11_6
  · exact tv_b9_11_7
  · exact tv_b9_11_8
  · exact tv_b9_11_9
  · exact tv_b9_11_10
  · exact tv_b9_11_11
  · exact tv_b9_11_12
  · exact tv_b9_11_13
  · exact tv_b9_11_14
  · exact tv_b9_11_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x124949148a49249249301005249249248248249048200009205249249248248104a24a4914924924924820812412494924924924100d24924d249241249249249248149249249249208a45241049249249205049249249248104b49249249249024a49149041249249248124249209a49208049000341000209a48249248241248001240008249209249208000000009a0d30920000306f3cdb0800008e36f36c20820824926900000184db4d208248249249a400090c924936804924820000920d249241241241249268208248149249209a09208a41049a49a69205049269269a48200001279b49205104b49249049049024a48000249669448148008249249248124048a47169249259341041a4934964d049041249289a0000924924104124124924964d04900512514914904904124820812414924924924924934920820920494da49249309209249249241040a492492492490451492010410492482010412492492412492492492490051251491480412492492c812414da49049009209241201049240a4904004004900000004164120461804964964810000104124d00104124924924000c351349040249049249249000009249649209205127149148008049249248124104924924928248249248201040249a6c34c24920924920904100924920d209248249248240000248268348249040249a6f34c2410c92492cd208209249249a400003cdb6db6c24924924926904092092492492524924924904024924124924920924904924924800004904d04d04924001924925934004124924924824924924924920812414924a24b26000124926926960804d25134d30000b34a66929834124926da4db0905934100104925930000024b68f2412080092493c9004971c6db7b40000dd6deda480001c71b79b8c0003d336e6cde6f461801b8dc6de6d899800679d9b40000c491e62061b81b0dc6de6d899805124a6924924920806d801859000009248249249a41269209a4920980000100181920800000038c36c24904334924b54c2082492492c980000209b59a409249a49249a420618d23cdb8c04d21124920000d382b6b2a0041348041258608471899bcde0c000213349041a134826b34d8401359c00001269a592000004136d348030804d25964820534834924904034d84d2c980104920924925920db61b6db79b6104824924904824964904104924964800000dbda4d184924924925920802524934934934c30c249249040349249348248124924929249249248201249209249269049a48249249a4000034c2683482492410cd2492cd208209249249a41a4926924926906186f36dbcdb01121379b5934900c04926934924920c04924904124924926824812492492504924924906000005905107184124124924920904904924924800004d04d04904924c219249259341041249249268241249249249208124249a49a69ec920924926924920804824b249249241209269a4926904824a249249a41249241049049209248000201248069200008049b0d240209209241a4c00030124834900034824906920820806d809b6c061b61b6c269209a4830c30836d861b6d860279b0325904d609209248208209248249249a49248201049249248208209249249269041249249249208249a49249a41209249249269041249249249209240a692082080cb209249249249208041249249208208249249249241849249249248209289249269048249249249a4184924924924824900126926a20000000134104124004924126c208200269b69349209249200009209a0920800824926c24820404000026820800004104124d001049249249a098492492490602492492482410010492593092004cdb71b61a09049b6da6d048249249029040349249348249249249a4004820820000000005934d34900124924924920b04924924924824924b04324924b268201209249249208249201049049209248000201248208208249209049248249249241249208249269049249a49249a41249029248041241248248208249248240208249249248249249249269049249249249209249a49249a412492492492690492492492492092408248, 1130852142682304, 531501965722252339719153175627443183717469800790498869384772571818727217051835929572359927622822367429, 531501965722252339719153175627443183717640638391329153326374694246369831076240967235743877729693913285, 565226563962945, 1130865027584192, 283815877546433, 
    1128665935057088, 72602404061249, 72602404061249, 72670922213441, 72670922213441, 1464367293988666786345460835585929877903938491202, 
    72670922213441, 283958014124353, 72671391975489, 735038153274139525203752297001957862872067445314, 1130852142682304, 531501965722311820355295343000136595802133113959347658967798375607001664248784974852633330773870350149, 
    1130865430237376, 145703012667584, 145703012667584, 1130849928024256, 1130849928089792, 1126454091976896, 
    531502060762203795718038741380637189880501640821354318282516477999359619219928091514111650547465240389, 1130849995133120, 1128650906865856, 1133048953508032, 1133048953442496, 1128650906865856, 
    1130849996116160, 2924433315402813672402381236860191311731202495298, 75318833451200, 163280183104192, 1130849995133120, 1130849995198656, 
    1128650906865856, 1133048953442496, 1133048953508032, 1133048953442496, 1128650906865856, 1130849996116160, 
    2924431924328498024125656976618932504475786598210, 172076016079808, 172076016079808, 1016500946211776, 589890434634688, 97231598205936491350660359263071773829072163650, 
    2924433315402813996922172835326203475162122195778, 163280183104192, 726230136525504, 75318833451200, 145687577628864, 163280183104192, 
    1133053248475328, 1133053248475328, 1128650906865856, 1133053248475328, 1133048953442496, 1128650906865856, 
    1130852142682304, 531502187482143476356267063671762043437506508641589031873029778217502413599328374029571050082732392261, 3957340443244109915238528109586043985448832434640056637062048526497910158579920958479931133882092332045517877726494765500070927310663473525087378663218913628084149928268396102, 182866808207136263864215978811709875421280479043, 17127021408847196083121750759367945704492274498, 17127021408847196083121750759374384444584530754, 
    28545046591708432741945982415123546494438774594, 75192136118721, 75050536411457, 75050536411457, 75050536411457, 52897547630930988433218872835188071378869869378, 
    163286768161728, 163286231290816, 172083129619392, 163286633944000, 172083129619392, 1101836620742996991608515348445947153932575888194, 
    736462602484587234854032627426544128258394329922, 581100779869120, 581101048304576, 581100779869120, 581101316740032, 18151363318720, 
    163286231290816, 1128665935057088, 1128665935057088, 1133063985893568, 1133063985828032, 1128665935057088, 
    1130865028501696, 2924431924328538913619398383337473903088199914306, 581109361414848, 581109361414848, 2924433315402854886415914242044744873774535447362, 163295215489728, 
    1135250193387968, 531570901367383692542797550355194181719091974575125145453313647529762199060569528693234983449486270021, 1130849928089792, 1126454091976896, 531502947801755124347351589697314092741901750441794140060569511136538357293569279732368981362694000453, 1126454091976896, 
    531570869686402707761686297389117202236281552858088780410431686737075786286515655623407784374933419909, 1135250193387968, 1135265163121600, 1135267373388736, 1135263481074624, 1135263481074624, 
    531572897206374181958308185599536835979177851826758051002610364797034040619495469550271982378714766917, 1135254891139520, 12131651677057194035006421367755935246161335106, 150105492558784, 150105492558784, 290839088600000, 
    2928723416496427864135960017514810097242029953858, 2928723416496428188655751615980822260672949654338, 2928723416496427864135943092488771888175600636738, 2928723416156146470774386659116411387517522156354, 2928723416496430135774501206776895241258467857218, 2928723416496430135774501206776895241258467857218, 
    2928723416496430135774501206776895241258467857218]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x124949128e4924924d201009249349248348349041241009209249249248248071b6f38d8c3004a24a4914924924924801822414924926db6db6f30180924904920920030920494924924924100d26924924924124924924924812e2592cdb610c0e5924924924924134924934da490410412492412002592c1b610c1249049249048604a24a4914904104924904800924924904902426920924920804d041b4d808309248249249a4124800124024024d0410080083092cd04136d00830800186e36f06c20820924920900000004004100924824924824124907924000c04924820100920d26924130020124924824824812e359341841200ed924d0c904d04104024006900124924124124124900120004800d04906104c00004126004901824124184930100030c30c603004a24e4800d059079058148009049059058609209049049024048a4914924926d341841249249249069041241061800009249261041240a4904924904900512514914904904124800022412494d249249241009249249241040a49249249249049249249241241149249249249241201041249241201049248048240849249249209009249a4f2cd3430c124924824c20d34000124134924924924812514914804104924904824924924904902414d208008001009249201049240a4904004004900004134164120924100100124000124104905810004134124d30104924824824000d34d04905004924924920900004124164960d241201849340a0924e36f36180030124d06234dba000134904db4d86904130004000104134934d84d869041349249248248125149148009041049058249249249049024104924924929a4824924820124984924924824920924924904100124920120800104826804c2492498492492482410c12492c120820824924824034104836020c249209249209041b71c79e7800c24924d64820c34c249b6dc79b7000c249241049a6000c24812092492492524904924904024924124924920900000904d00904924930924924904001824925824104104924904804900906c0410492412492412082492493c9041869049061b8f36e00304924900934c001049024149249a69a6000124926924930804d24d24d400009249a69241a81259b6db6db6186134100124924130000826800c26120800926930900494d349269e6000124924926924f301009249a4924834824900124000d209049a4924834806db6db7980c005124a6920924920806d861b51000009248249249241200041001801609a4d26124924920904304924b04c208209249209801bc1b0e00c009248249248241b6e08e38d87004d24d24920000d36db69a6186134934d24c20c36904d24db69041201849a4920db01b6db6188124836d26d2485cd86de6db63059a49a6da61061b6c36db6db6c56f06db718620000413682413003c1b61b6100030904104104c36d80036c30180534804924904034d86da6986184921924924920936f06f37206185966906924da4904d04104924904800de0b06c04004924d24924120db6db6db6c36002524924934934c30c24924904004924904824934904904904812492492924824924820124920924924904800104c26804c2493498492492482410c12492c1208208249248241b6d04836020c24920924920906124904934904904904d64820c360249b6dc79b7000c24934d049a6000c248121379c7934900804936934924900804924904104924904826906904904904812492492504904924904000000984d00d84124124924920900020984d00904930930924924904c21824925824104104924904800d60906c04004124124924120c60c66db783602690693490490492090c904000c04936f38f36e00004920930934c000049024249a49369ecd209249249249208041249249208008249249249241209269249269048249a4924924124d24104904930934800020124806920020c04930d240009a09241a4c00020124834900026824d04d24820980d06126924104830c20836d86db6d86c279b0035904d60db6000db0db61209248208209348249249249248201049249248200209249249249041249249249208249a49249a41209249249249041249249249209240961249069a00000000061040241849241a6c20026134924924920984924924924826124926db0800c25920db61001200041209a0120c341351a4100000924006c04c00031984d00d805841869b6904830000924930106104124924120924931830934db0904900104d60924d001241269b49208241001249241309261b4d34d30c3092492490cd241041059a4126924924926100824924924100184924924924800924924924906134d24924d20984924924924830924924924904920904004924904824924924986c36db6db6c240048208200040000209b4d30900124924924920924900924934da4904b04304924b04800d64946d04000124924924121860c371b783602492410490492092480002012482082092492490492000080492092482492492412492092492690492482492482412cdac106d849b0906db6db7b079e0d44126d34db612c824134124100100104920924d00c2c1040069b0c06db6db6db6c00d64906d04006b20c208369209b48000201348379861861b6d80924904134134c248208249249240009249048040249249249209049249249241209248249249a4124924924920904924924924120b348000201248241b4d60836c26d0cd240001009a40001059e6d84806d80006036d809441369bcd209b6d871b6d86c26db61b6db61b0b66de0c06c36d84804d271c6181807180db4924184da6120d049269049049a0820800900964800020024800904904100c06db6d81806de1960924930100000160c30e361b030c1861359b6c61824924824f2cd3430c100924924904904906136d80000b24324100020120920904904900924e36e3cf3c000124134924926020104924924904904d04104000124134924924904904135834820c34c349249249341849a6030c24824906904184904924924924930934c0410490410010083018000082000003012080c984000c041b6db6de60301249241061469800001bc9acdb8000126b38b34e00000904c04820c06006db6d86d86d84924924934d849a6030c24800900904000c04924924900930934c00004904db61e61b6db61260049240240001001049209249001861b6db6db0806db6db6db6c00934934d000069a0820824d20de6186186db61b48000201248479861861e6d8092048, 73152495438401, 73151959024193, 73151959024193, 1978643212691817293584598830314142670096991565944056100368981556509283233971924845458511316430820595150800140124405141017350669856124677947226265994150000456136890591139245638, 494988812095680, 565357824708800, 
    494988812095680, 565357824708800, 424832672993728, 6766417418605052960284403873956034662415087933019357751174634711686152421128370236106196291468030336505308234966939183908257870890931027439678518685677619440202482198603738838052627672866608332873961145481784810297173166059837168989476227257631005135330662053069449156680952147525984028402147584967759407221876835532886241747606075049629154265286055029279599810987736517530953674, 72723462623424, 283815869157568, 
    283815869157568, 284099483800000, 123718979702907296900957969448798360870873626377824732180702756357245573391931476057583603804368562247178344431293461258271847245916035223212941028365569765359824100495687239, 123696335928358367652530274622954401638006858379669000195693308397547635663752629995967882383079843615071841009559242269338327500472436390910267045248771308809942908675257927, 72709569515712, 72709569515712, 
    283816003375296, 283816003375296, 72709569515712, 72709569515712, 283816003375296, 72722456514752, 
    72722456514752, 30916536060390973334392789219594223022841207738600850232126556505379098512641350303830668660273786849414053436988633874966690185044751065135974000939922304672263792479350343, 11462626759741199768997410706151217483789374274, 22880651857531844697587021773696965025688720194, 583325890726465, 583325823615553, 
    581126800425537, 581126800556609, 33218934237609691583667734500700879018965607552233066395366582696375288605112551729931261612438221061, 565733168267841, 2923059026705660288023445389325497336011054679875, 1128650909180737, 
    3957286427485527111966371202728695842583142669952406685939838099898004695599445105319527457963131716141822238702492805846893721692427541764692548515988117870786196643564669511, 2923059026705577860035993460215541050950996248387, 1128683121689153, 284258191557185, 565733168267841, 73151959024193, 
    73151959024193, 531501989977239595604777958266590246907210077719849643890214810377548812184427244189515772895015103045, 4152422219673169487285134331132632905950254647948019775334663091798630518408532879790735456359575813, 33218934237609691583667294852612056084036108681140815859361421562739649606960324545744914209578838597, 565733705206337, 565733638029889, 
    565733637636673, 565733638029889, 16609467366305190829035992418570272698236317637043172693449831413545592983268775239038697172417271301, 565733168267841, 2923059026705577859996379378958407824557450757955, 531501997402235843673079470330230775363297137637080212268951097862716056184207520967903928316539333189, 
    3957286427485527111805477507569384677388265726829047115696438224679927975456096416098154316005244052901084413721307554398407779864317554165801511606627852324871209849263716423, 33218934237609691583667294852612056084036062503985178488398341509027027513844003745897684573278071365, 2923059026705577859996379378958407824557450757955, 2923036725960379004854718034736358096204124431939, 531501965722252339719151636859109374010600548494107721524533470277470747775416975526562626240251973445, 73152495438401, 
    565733638554177, 7729078731994588773182614234970272038156773279364636877127765354306237444966898631880952793711909300025111364430614370685453418847559131887464167366985641869963783907036743, 1128665941819969, 531501997402235843673079910192991513469939473119834447266783141572455297281457741655391169468778049797, 284241213538881, 636102448859713, 
    636102448859713, 73151958567489, 73152428329537, 735038153295407254265949365575100471625558102594, 497187835351232, 567488128487616, 
    123718979702907296900958070943087228744413053056313867216125688855668387715473532790494675144454534755398185782685484058522813594209219842385064605170155050380555978601889351, 2923059026705577859996379378958407824557450757955, 2923371237138357288720360879014225395163695458115, 2924441672907886758631154593491314208670820108099, 33283751483858781319564816128739982923191892298955571051706608214456923181590049020647299712353462853, 2923059026705577859996379378958407824557450757955, 
    2923371237138356964201841070510447821626714138179, 145290695807168, 145290695807168, 499386858606784, 123665259706514723817469992000255752789379054795555447883033573604416149213201801252418953549607882351843797570774597697513494866586641516862518115928553331373128189439082055, 2923103628366116104703131682126640424996346834755, 
    2923103628366115780184611873622863345004526480963, 123695396123260585422513779322611143084593994527087862221254488193128200263184393189661664637173404191632624902323701007150699378088389076853445673602007209320004327330272838, 33219377757385355898274478425002338802635197787403479079808904420471000268913389039912058232559692997, 145275260768448, 531572722965411489262211614652112653890571392491620957230296323881245098360362829836917212692246446980, 297076719096000, 
    3353732746238322116020963563231326792644422537703767127716223924568548674187655352448409931972919654682979793076639620688730788254539800655875416880388223061156687878901618535159196436137574039570003057144329447585937781226521899446074102293389346875297253129600341098053943917600082257602680728741056239568529101632044833558695453383764547387563864902970990218166018884512206922, 33284591003420927995833185577910432186357966179657882351230328016968388343125413291033906832283550596, 1978673408206294763624360309987527955848333673722109684660407881534622700805795696569756410911859360606610087113994058174332916847192387358386346388016711860401960784534435398, 567487725834432, 145275260768448, 85970486563008, 
    508182951628992, 1461730221331979515147245494149263794911024517954, 33219377757385355898274478210540057781608293080767662406949643557349979322502755864517258443790050885, 2923192831687192594116636288463105625874138969923, 2923103628706398147105550337086237952436294694467, 6707465088747716097056592077363274021238854897065343158400050047707950500998719341524183391675321409496970057441757540690410606557287573747251488139544963912943054548085100119424324576958427034334873087468478330392628807636078415649582009511260800722176198949763498798044028233627840689285499641145862012942604749525681358692076765303413013233714108408516982431418474807276705355, 
    83984068383168, 8867811776, 562958821233088, 145290293153984, 7760210236153524638637458676013234798871915889947221852230702807348688769294996818961209645278891984808733514840781673483817676960116877218878907074773182085486586776997447, 501585881862336, 
    290343014895808, 2923059026705577859996379378958407824557450757955, 2924798491466569079041199394015702161682577008195, 497187835351232, 123666144228958092852206876092622838452637789351450489524223266348525584249636199036894919146602627393721421364483025032773856364553683338998756008392548269280890598989987399, 145275260768448, 
    145275260768448, 137284085361621710030000556353067655888143129154, 2923371238329345572943645501136036027629723232067, 2923371238329345248425125692632258947637902878275, 2928723415986004313754537852933648344949050083139, 290343014895808, 
    2928723415986004638274329451399660508379969783619, 2928723415986004638274329451399660508379969783619, 2928723417176992922497614073669046084924042422083, 531566814649450785644819340084031413389891698486306563036071193762820012627908814953434791380210049605, 79306639282368, 79306639282368, 
    290413073141952, 290413073141952, 532085914943017766239685494703179805233974339035105119452838975410652577433462081124345554337184105156, 531505989080216822504544562464942551601149426482642411874062691844592676582071534830629002487422015365, 531505989080216822504544562498485038846551566490484496303279843630861214447849527803752787620874704773, 1135254622585665, 
    1135254622585665, 1135254622585665, 531570869686402707761686297389117202236281552858089451856254100837565319476054259703681400686759920516, 531505989080216822504544562478359546499310328663480385579843117465226435849453072740624816924349978501, 531503961561272569453176849296590621453225986718733634654095615403665281272623020617534350899214302341, 532345469047865660768624110356848139815344057959486246185688371381305733006967915710357180121876808388, 
    5935930579190631616001319176849573227493461240099143296957030727711848769872209422459084875121076879920788683256028132544038939947375169829519249865721576241152424416657766983, 1978644155390614684742611329787861667513156864556970981279354174245290187816680792520850956158298116726105322830068774919213305674519022709856887827905089649766594436141120071, 2967965761340618917561478231531542951065145903390299399483757169101446921799051799401484535601367600385520942480866527222288090301184135517707525679540852567881416857480034887, 4156945546928349518604630377272479820007834827201969210917077057649731366151702308859654025665069468022725525839808875202508765286701869103334117424287916138899986363157805638, 290343014895808, 1135248247907137, 
    2923728051613651530597663926481896831140891772739, 572298496066369, 531505989080216822504544122696100774582772228052084178111223744204805973024121924562642702943787700421, 72709569515712, 283815802048704, 72709569515712, 
    145139965104320, 1135263213437761, 79306840608960, 290413073141952, 290413073141952, 8867811776, 
    523099895412083056701961568785102995499190629434155857492554403435754243343562188804286622922725253, 72722456514752, 72722456514752, 82068515066816, 290839088600000]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x12524894524934924d20000924924934804024824926800004934920000d205249208040348028a45948a49248209200001359c4d67000814d349259200200a49269b6dc6f30000924d36936c04024924920826800004930dc4db00009248351348000025249249249241040a49a4924924904925134924920524924924934824b249249041049208208249205248000201248109249c6db6dccc300249249248289a00061b6c061b7006024114924924924804024924924904104924924924920924924924924124944924924814924924924d209249249241241040208209248124249b0d20d24d209b6c30c30f38c24906184026906820c36826d3092492082492490cdb0f36f3cdb0924826924824325824a24800824906104126904940004d84d209240001009a4124c001241368025249249241049240a49a4924904904920820800900524800020024824824904104904f34d21804920510514924924904024824924904124904924924920920924924924124124944924804014924924920d20924924924124124d04020124812402492922512924934924c30824924924920d209209209a0000124934c20c34814924920920d201129125249249248040149249249209209248208000248149249249209204229124a29249209248060044845224945249241249008204909249a4da4dbcc000249249248269a000c124c36d36c00024920d24d600600a4924924924920926806186db0db6db0db09049249249241201241000209209248208209b48249241041009a40000208048008249209249240209248209249241a6820820f34c249249249209061209261200209241041049a41bcc3cdb6db6c249000040269040920a4924924924d379b0000924924964c040249269bcc00004924d300019209249208040648029249a4934934db6c30c24924924920d209249a6db0000134934c30c34c24924d20920d201a4b2c964d24924c0c024924944d04105924925920921924924d24124000020800020824924904104908e48934d201019249241241240149249249a4924930000926d24924c20824824920000920929924820c248205249249249241049a60208248249269269308049249a49a4c20124944924804024924924920804924a249249a4124926924924904924b249249a4124d249248248040041041269008041049049208200000201248029249a49a4c201249269269308049249249241009249a49248201249249248208249249249269049249249249209249a49249241249249249269049249249209201001841049a41241249249a6c24824924924924924800024924924920920820020800020820800924920920824820920800904920824820024124104020120824824920804904920a2492402012482092490080490410080492092082492402402000002012482482690c0249049029249a48201241249269208049049249241009209249a48201241249248209248249249249069049249249209209248249240201249249249009049249249209209a08203009a4124084924516b469a69a0000924924d341041a69b6e27024824934d249049008069a00009a09249241041243289b6c21804024934d249049005145129a4924924c0001692492492092082002080002681c924924920920414924924924924930000924924d24c20820804920000920b24924c20c248204949b49349240009249249241041a49249249248249249a49249049b49249300005149201041049248201041249249240209049249248249249a4924900528924924900016924924924920526d24924c208129148041249249268109249249249204149b0800000b209249201049241a4820020004024904024804904804920000800510000104934800104124924924020834924d24824904d249249000000059649309205289a490402c8169269249209205271248211a681280402492492c810920924924920800000965924814410492525924924924924c060249a4934d8410492492492092092c9b69241241241249040268249a490418490492492492010092c9269241240125125269249248000249a41269808209a69049a6020800004904d04904924000124d359440000249a6924820820926924920812424926db4db69b0000937135924800024926920924920804d34d64920000934c45926904004924d24926d305249349249b4c36f679e79861849269249241040a49a49249249025249a49249041008208208249204200000201a48109249b6db6db6c30c24924924824924a24134904135040c249219349b5120124934924934814924d24924d209249249a4da61249249348040249a4924904104924924924920924924924d24124944924944c14924924924d20924924925124192424934924d30000924924934c040169c49a4da0020526d249348008269c4924d300008b6c209a68000000001241001204001008048048028a46695e75b6c000148a49140a49279e49a4d20000967124936800024924902924b24924924124924924986336db6f36c24824920824920900804924d04920924824924824020020820144020820824920900804104d86c209248209249240201041361308249208249269049248209249a4126900800820820900420000020324836c00036c36d808041049008201061249249240a48049249249025041849249249045105249041249b4814924d2492cd60824924824d24104124924904804184924924904924924924920924924924924124904924a24814924924926d209249249249241124029249bcdb6e36c000249249a49a49248201b6c36db6d860240a4924924924920924926906db0db6db6db0904924924924d20924924924830824924924920d205a69249a4c308129a6934924c30822db08209a00000008041040048149249209201201249249248040149249249209209249249248208125128000248268248149249249209204229124a2924484522494524490924a6cde6db6c000249249240a492492492490492492492618cd2492cd309209248209249a40209041241348249209a4926900800000804d208208209248241249269249249049248209249a41249269249269049a4092124d34964c0c025934935921960db6db6db61b6124924934c08025934935920d60934d24d34804024924924904104934934921160924924924124104c04986c000248248041049049349349300201001001001240149249249201209249249241201261a0020920526d349e6c0c0259249249249248000249249249209208241249040208209249249209208125249a49a4904104d249249259241249249061041249368041849a4924906db79b6db6db0924924924924014924924924184d24924da0920500004986d008040248041249000301061a4160100100100124000006105904821831165924d60800004134935804104924924901830d459251609041249249240000049659248249349349375a08149269249241209279e6de7980030924920000105924d20920426980304124904db4004c049309240001009a6134c009249a6c269a0806024906c04186c04dc0934106100134c2492082492690cdb6006c3ce60924820924824020c269a6b0c824db4100db4920904924d31804d30534904030134c249208040249049209241049240a48249249049008008208049204208000201248040249041249025109a6004104a241a5000020134c24900004028907330001806f209a68201809ac0000000048000241001259200309248209249a43370000301b6c249209a49209000301261a41609c8d8c040338c2c124944860144c14924100c04d20924820100924020924904004024824904124100804924920920100924924124020104924804010804924920d20100924924124124904020124812400000820820800804920004d200000248208200201208000348108049a0024da0420124800934820000124124120800104904904800000820b20900804920004d304820001a09a49a0084000926826800000125934d304601e74001b6c148a4100120924a2c000804d67144810020925924d200800009a69a4904000024a209a6000004134d24820004820020000800124800906c24900000826924980000184db69308000041349248049208208249205248000201248249241008049201041249249240a49049249249049241049249205249249249348041049249249025100000269a6a24106000926828980c00104d34d60800036c0cdb74249241001a89a4a260301b6db71b6c24164c00020924814920000804d20800124904824804104924924904924924924920924924924924124904924924814924924924d20d0492492492411242c9800041249059c4105904d20924000100b2412480012413682c9ac90c02498780798c006d8092492082492490c9248269249a4324824a24b3c824902482492924d24820934824924d24920d205a6d24820db4812800004904104824924924924120000020820824124d34c20d348121249249040248149249249209209249248209248125041249248248149249249269209124229124a2904184924926b04484522494520820924924920490924800024c3cc24c249240000269a49ac000036d36db5820000d24d64d600a4924924904186926926986db6db6db6db0904924924920c30924d34d20920b240041049241e79861e61b782490000402c9079e000798cdb0b2c8203009a4000020804800824920924924c2092482092492432492492492690186092792d1209a409208, 1126454091976896, 1126454091976896, 1126466976878784, 1126466976878784, 2923014425055755907847806052055471588967421317954, 72671123540033, 
    72671123540033, 72671123540033, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 
    72671391975489, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 72671391975489, 
    1130849928024256, 1130849995198656, 1130849928024256, 1130849928024256, 1135254622966208, 1130849928089792, 
    1130852142682304, 1130852142682304, 531502440922005843165253198632127688506600639859087277907474580060043143738987107959451995641204836100, 2923192831697908886674815302507333853680167293762, 1464372861018823477429589516038269041656136274754, 33265503442351452126331306229090706639815515675446440866307823883690874866739331128466346530498363524, 
    1464361710646224212118018748179132717475383284546, 72671123540033, 33330384048567549770084055013415606785296572831131718200920138323617454815002967695460191932104786052, 72671123540033, 72671391975489, 72670922213441, 
    72670922213441, 72671391975489, 735038153274139565768571504305298710766570017346, 531621557660220520752150513146082314592552195636180300757603903126366351170190753183270369250787148484, 1128665935122624, 1130849995198656, 
    1130849995198656, 1133053248475328, 368944944160415134053722878186638528975017694018, 1464361729701964067257796246570573589988004401986, 1130865027584192, 531501965722252339719153230583454286584335988149384332492510088116786345471161445230340801350831280325, 
    565802424683073, 2923059026737561759922283370275190891157781514051, 73151959024193, 284258392883777, 3957316703951659838780152004808261855563355920534123062488556975520652436931769909419166354472247557026800888754137522857367008482401090263383330461290433004428141346133343814, 565733638029889, 
    3957317558990021763896597074513483777321179429988810303505790990816728443878441296223981855856133517212096960514156571367497189761345281635317880936951304641027610877674610246, 73152160350785, 73152495897153, 565733705138753, 565733705138753, 565733638029889, 
    960962154094212046835216665290546064298897187864006737062931415346219582426575847177378552277775350718611374702060332024911311854850761807530670807452093857470299238569650069956159152232319387331672625520977069402033759381951899521924245446933154360138416129247956553, 531501965722252339719153615275532006652570137262412858188274824630842858430845092499590867553765216453, 636171168795201, 73152495897153, 565733638029889, 123685131982806624731636947599472465597942826067141657887102180393266284177070176290541891531268771030017101866445080346239354495650139899496735353024919256742857713934923846, 
    1130852142682304, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 531568842167428478357530850701453957224191833802426491581053465286168581263678350519796619569340010693, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 531566814648484225306163577301943804094645550766493160852035823832285988526039447826278823301534896325, 1130852142682304, 
    1130852142682304, 1130849928089792, 1130852142682304, 1130865430237376, 1130849928024256, 1130849928089792, 
    1130852142682304, 2923103628366162226919935339958930556694097312322, 1130865430237376, 531501965722311820355295343000136595802132923292382446597370670226588905044197315343764340696619520197, 3957286482768179822531042257984468785437016842876743920674496321736278958371152670106324390638863448733274299389309339628051197033253113697326353127571360814580065455040331334, 1130852142813376, 
    2923095265597320640477781096116489869316256176962, 567916014604480, 45761303733508096269845501989850430331355667266, 145689725112512, 145687510520000, 145687510520000, 
    145689725112512, 145703012667584, 145687510520000, 145687510520000, 145689725112512, 145703012667584, 
    45761303733508096269845501989850430331355667266, 145689725112512, 1126454091976896, 531502060762203795718038741380637189880495730145432734799242231124143991301039029133666257093067116357, 290830230229440, 290830230229440, 
    572304938504640, 290829961793984, 2923192831102331992016298457582829561617546482498, 2923192831719094030521271970261338519330933978947, 539742768951196325507865402138699056102340450197875606894334348058039577989282022289613866135697244292, 1130852142682304, 
    531502187482143476356267063671762043437525003337214631804565324891564217087465117607093732827135315781, 531615475103387761601200090448234652778561254456376758670749079523822883523948720678328845253779866308, 581101048304576, 581101048304576, 581101048304576, 308422433051584, 
    581101316740032, 123695471676221042797915710105195680535550393139390880134966757974598658591025081248587257590371839161876970607808558261434691650770261780094935425264463311198526973746839110, 581109629850304, 581109629850304, 581109629850304, 581109629850304, 
    581109629850304, 308415994794944, 308415994794944, 308422433051584, 1135250193387968, 79735007220672, 
    150105358341056, 572314065310656, 1135254488355264, 1135254488355264, 1135254622966208, 290830498140608, 
    1135250193387968, 1135250193387968, 366090429719190666996350316640387456917454213954, 853797648470976, 290821908206016, 290839087682496, 
    290839088075712, 572313796875200, 79267991980097, 79267991980097, 581101316740032, 308439880831936, 
    581095138005696, 581096744948416, 581109227197120, 581109629850304, 274745532017468689803848039066971249828197303107, 581109629850304, 
    581110166721216, 581110166721216, 73120750833856, 73120750833856, 572298496066369, 145689725112512, 
    145689725112512, 532476030175051125568810890530274528309189987059290668932858355235412568351519032297064797028923752580, 88614378162753, 88064085002305, 532086366377952492244812920228283923502860872459586221613286526508628006287186036952809394911066735492, 145687577628864, 
    4184799162934115812467006531811878932024478815227303108363799046136982306205777732963098949877755141, 563508577046976, 88064085002305, 88064554764353, 25690556512564897417967736693685251176602797891, 25690556512605786755728698461259928835195406147, 
    88064085002305, 538834329584228694858269711437813787343799695138028417703122124968349874881837705371126879589543198852, 538834329584228694858269711437813787343799695138028417703122124968349874881837705371126879589543198852, 88614378162753, 88064621873217, 871372386472896, 
    145702610014400, 581101316740032, 145687577628864, 145687577628864, 726230136525504]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12494924920024d20004820c308201249249248348148249200009204a0824124104120924924924904800020920b20904484824924100920924824924824824c34926180d20490004124120920904104020104124924924804824820820000920d64d640001240905244928a430492482482c0209208040248120a4892514820924904904824124100805902424924d249300041209249001a0820920b000200040061008009049059058029a492492400c9a4824826130c208040048241249249248209a4904d04806184100804104824904104124904924000100b2412082082012002092482492490082692092492490c92082082d9209a4924924824020b24984b04826e36b26926e2090c936f0402036482d824964101860820904904804020004104120100925820100924104104d24824024900004034904d36da0c06da09c6d860301b782048, 90744681482817, 563534346338881, 72639712399552, 72639712399552, 72646163239360, 72654746882240, 
    72639712399552, 563534614774337, 563534145012289, 563534346338881, 22858351026265797544420420379146467978082521922, 301850645580353, 
    2923059026716211724527477913244979128934212896579, 1144050715542081, 90744681482817, 90744681482817, 581126800360001, 90744614373953, 
    531571883445859728093838005984573371015275453222989363297997857564691512789431255911021779426363115269, 1135254622585665, 1135254622585665, 1135248180134721, 22858351028509527383532186048578453891757119298, 1128650909180737, 
    531566909688434973202219461557252614587781686025470124591971624095238120289787173063293825373713985797, 11451955460767297944068514140156230740863881794, 11440630863596169112004453033220901494786626114, 2923036726045449637149771857905542595956585857603]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14db68201809a61241249208049049249249240200a09209249008049241008049208208249241241248000201248249a498c0249825069c71860301b7426c36db6180db0b679e79e6c00020806030c06db0934c30100d240209860001b6c24900004004d04920536db0c06036d849049248201201249248208268249a49249009049249249209208248249240200a08249249049040049249201209a6820200b3c1121a71b61810091b09b09b6c00036c2c9a78218200009a4930864834907066181180dc09240001001241b6dbc8301a682c814824920000920d04d34000134120924c00024834124900005104c34934100930520924904024810000124140920904904000104000024904804824c349200009a0d04d040001240904b4134d00034d0c82c820006820d04924c0013434133ac001b6c1449280002098690482412416000590c8249241009204149a4104d808209b68209801861268000201a48200209249249048208200009009048249248240a412092492490cdb0820820900800824924824100124924984826120924926902530904924b05804d341018059609b6d04030134c20024904100100934924924804024104104920100924c20100924104104924824824900004024904d36d30c04d30920728b20924820824d041061348069a08208268008008249249240001248049848200249249209040049249241209048249249240a0024924920904004924926120986826924824326820820824012030c24904024806185900004d04c309b6980920186d34000164000124d059808248001049049248061849208049840049249241209001a49a6d04806184100004104826d84104124904db0004d84d60934000100b2413cc001341b6824c3493000480092612092492690cdbc9669ed9b0800826924824300324964b00824b0c9c798603024742c80018600036002c980030806a209358301009240208000001a4824900004834d04938d860201a482048, 581126532383297, 532410317973131812080648656714270156060592381536589609893487351472106090256347781895432638757381357700, 536692438010464554972587582556171495452322513301567887446957442406563380909888364225226333405827055748, 538768617409379679572675544083912136848863734186044111133219137729056088180558669732936048947790889092, 532150795548267421505637661147626718737520760848372037069699673778529816838762538729637492797124919428, 581126800818753, 
    22880651856534919897796571963262768197530555202, 2923059048494365635494605585268043516020982351683, 2923059048494283207467539574900954004567378429763, 531501997402235843687493332922195703653322799687969577670948486604953746896055899063578761065055673605, 2923036747738455396175041981551837611953662001731, 531501997402235843687493333029322020693895454618899297157134076347610500353000813882013648945436450053, 
    73152495438401, 73152495438401, 45716702053113134554166614414863479636873974594, 182733003226600873697241947225412027925590446914, 182711411639159678339408113457370509612985418307, 583325823615553, 
    583325890726465, 73152428329537, 653694634904129, 2925868942219166618116724333477864400378807780163, 72723462230208, 72723462230208, 
    581126800425537, 3957286424923782331257569556467828053331168425210010546086560143435557043097217568828097116544454033870907027216580373203914836256757461218525825073781994965864405955643747910, 581126800425537, 581126800818753, 581126800818753, 581126800818753, 
    2923371260107421639725642598671598536351346139715, 2923371260107416771930006561720701465162449757763, 581126800425537, 283949951881408, 22880651858778649736908337632694754111205152578, 4142784228360910908802335766957165297584686752429553713591218414793005247489723738595705620903667883051826194319477719921617068314560369524703513283026779969382264217890930246, 
    283958550204864, 283958550204864, 4158242378682424545877174067372260302831595466214329782443051439313895390767125428682498538539463003428685601274898477001223470324476881317739071061181693870061752033151545926, 283954251043008, 22880651866836476162298248719182003534022317890, 73152160350785, 
    3966464703872461186898157878799336234098157318011621207045769850311440232446631214380212369876642769645565116847952843040836216669397369937008410841946012178945986894705406534, 480950554875126826929644583528179280854468969067850750811947600825277030449925936575315751774222591095866266286732972331439562377252866392898794370303574991995269379097864709499515719334495084545053400419890400047968463073944080809363777607034108950718980096246988553, 73122894581952, 354602174648768, 73135779483840, 73151959024193, 
    73151959024193, 73122894581952, 354602174648768, 354602174648768, 73135779483840, 73135779483840, 
    73135779483840, 90744681941569]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a69e69ecda09249249249208048249249249241209269249269048249a4924924124db4124d24d20934800820934804934d3c9059a41b6db6db0db6c34d46e34146d84824924924100820924904100100934924804000004920904104db6dbcd879b6020904c20934800004120100004924d20824d209a6c30900d36124d04020134c36d81b64166d80934c30820934824924924924820104d241340000209269249269041349249341008249a49249a412092c9249249041241249241309b6f061b8336c24126820820964835104124926d04f318208259209369241248000209041249040041a4924920800824124d34904166d861841b69840059248249b4126980024c34d84814904d3cc019b41879e79b6c40030db6db6d860049241061041a69861b6db6db0db08249249241001869241b4c00020104124904004820820824d209a0820900926120800020004026000026804d005260249200269861861879e00009801040008201061049249248260041041208049a4124926d209269049249b48249841349281209660061b00361848241001249241309261b4904d3000092492490cdc6dbcdb79b61bc966d8c3061e6d84966d863061e6d8c9a186083cd309b78309319361368000201a4c66d80026824d0090400492490482498d1b633cc00024924986c36db6d860243003059a6f04c40000d24920100000020004120b24960060f36de0d848003079b6f06c001879e6db0000006db61b6180824934924d04d30924c20820134c20820924924904d3082082410092482492492412492092492690492482492482412cdb0c36db6db09049b49209a4920d36c209b09a6136d04030327846d879e6db6d84e30820824900000104804020128c20820924034c041061001059b7926d34926336f241a6820c00004120100d859b6106d34d34130934d24934d34c248208249249240001041040040249209249209041041249241209248249249a4124920924920904924124924130b36f36db6db6c24134db0c2682698cdb6186186de600010490690480000412090080086492412c130966124d24c64124d279249a4c04367184166925104f60820c24d2080, 636102448859713, 565733704682049, 1038105601325226656261112741112999207100509286666393382647521464866551546190720057742736820234630277, 565733168267841, 2923059026716294152554543923612068640387816818499, 1128657620591425, 
    2923059026716211400007686314778966965520204629827, 2923059026716231844754557018137733261651234326339, 1128650909180737, 960962154094212046835216466568230249988890382151958133667347307562916465497342476593298410858581677141351845626939716737428015408988734512894287202788467335507517490986589776445971980008188546766582109799392845525641636039252194293468664316105634598600318976746188553, 73151959024193, 1128683121689153, 
    539483191105693307904989621127166661957158843076672128809109189208158024211080576296404968688880730244, 565733168267841, 565733638029889, 284258392490561, 565733637636673, 284258392883777, 
    565733638029889, 7729078731994588773169520666295190370044736057138367577000711215351148773730825284873711213720866435428376839004898402199146253314004926460552850802774666246128713286547527, 123665204429260709805884152655768039672729271479015920671161373315949523592261178329023232215178897785583604594890815598429400884760085049411903678569458531214518010549106759, 73151959024193, 73151959024193, 565733168267841, 
    2076211140774540933269119937789486073586706161992380090843616441385116925754003238058671115871733957, 182733003246539369395965508024691772293812127555, 2923059026716211724527477913244979128934212896579, 2923059026716211724527477913244979128934212896579, 2923036725960379045419537242039698944098643804739, 531501997402235843673079909978224604924631810079789385137073962041224972816257347243421760405147770117, 
    531501997402235843673079909978224604924631810079789385137073962041224972816257347243426037393710669061, 531501949882260587742187830038934959487520271390244335820502019604593704953167310292370176695077135493, 2923036725960461797806664319192544706645060551235, 1128657553736257, 531501997402235843673079910085350921965204465010719104623259551783881726273202262061856648285528546565, 531501997402235843673079910085350921965204465010719104623259551783881726273202262061856650372882652421, 
    531501949882260587742187830062414698959871339678885102289338414748087686833271703957193456929594369157, 2923036725960399490244361901261002340689109910083, 143490706068417, 143490706068417, 565716056036289, 636102449318465, 
    73152495438401, 565733637767745, 73152495438401, 91522607425890448388781968189744411859184784194, 91522607425890448388781968189744974811285689154, 73152495897153, 
    45850507034727868674423523919561280953562174274, 45850507034727868674423523919561562429612626754, 45850507034727868674423523919561280953562174274, 182866808208215607817498856730109829242278646594, 182866808208215607817498856730110110718329099074, 182866808208215607817498856730110673670430004034, 
    182866808208215607817498856730109829242278646594, 182711399388994469185623428775893614118303760963, 73152495438401, 1461685619180706259756309072167718863607716385602, 565733638554177, 22880653047523204120500907478049583359714136898, 
    1128665941819969, 1128665941819969, 132875517170549667140217855486514756485814493334024282925866310532012045412391917741433111343514474885, 565716458684993, 132875517170549667140217855486514760086094903975248972417451346408578128467875753464723197135902955909, 1464361710646224212118018748179132717475383284546, 
    1464361710646224212118018748179128776823561851714, 4395946588256910153339507021746856756526993965635, 565733705138753, 565733705138753, 732180859406542047643711596624480504912541684290, 565733705138753, 
    565733705138753, 73152428329537, 565733637767745, 143508288590785, 636102448859713, 13118309248616667272107690173392736222570352480123600913619309594185293497061910000012742799436464610117150602728684797479181431817217558434319867777828842740703085816971645683890256446625688084587286867679463819060570831369041289273386275260805725470825800546192113140234430244743126330637740224572523879608403734342628655220078940555756239560498060169546727472372224577610, 
    483068399734392256596603452072689932513709894038576676684204153094541681862893414819456972748453862434918885286530370798169125134349241099652625178944598872173024650767943, 3957769494675904269259459758409585899568650036697584459571806323892258860696191546691966396946209913725218452870230586146497581373401184866613989730179678296169141569352354119, 636102448859713, 94377113039711876845755382275474252474458641218, 73151958567489, 735038153274139606333390711018344170516442616386, 
    73152428329537, 735038153274139606333390711608639558661072589378, 735038153274139606333390711608639980875148268098]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14b36b26920300924924924804826de4d34d200209249b4934d20020d66d64d34060120000320b20020dd6d34d34000124b249248048209249249248248249248241b6c269b4984024124924924936d84d34930c04814924924d20020924924924904814b249269a41004a48a0004104104120524924924904804924924920100924924924804824db4926da0100494934924920100946d64d240000a00001209a0120d86104d040001249249248048105244928a49b6c269a49040120a4892514926d84934920002424924f34934920000924924902924924924936c269a4984024124924924986304924b04c371859649300048240041049040208248249248241000000201048208209249249040008208241009a48249249241269209249269049a682492482412c00cf36e36db09041861049079a0db6db61b6186224964d44a35836db6db6db6d80124904100000b24964964b65820104104120100934d34d24a24c26004104c06da0820c20920d24346d801ec236c2000000402490048, 14272542282624853759616613953690723930874118979, 91433404103817034175472404877669124905958904642, 91433404103817034175472404877668913798921065282, 145206474182848, 145206474182848, 537730971229698372133891057151166889629101739708057876080752228710400418396371358042565818295729275588, 
    145208621666496, 426687901733312, 145206474182848, 145206474182848, 426687901733312, 22925253517073164603934738472394639654562829122, 
    33337480364872433620033063122392292188351343667272613683014247267454124785754446501616075620815697797, 3957286431171079471261248611484284558459199474667190469820459079091066522235028647868966365581965099770802686808408360187110201132456464971529396908481543115599146293788978758, 22925253517073164603934738472394639654562829122, 145275260768448, 145275260768448, 2923059026716211724527477913244979128934212896579, 
    2923371237138357004766660277813788669521233520195, 285881622598080, 145414981423296, 285881622598080, 531566814648484225306162698005753055690791736613800684910737548945303556090407239312402718201226686661, 6707465088747716097056592077363274021238845272324962137946396857010650052059691504918520012960426692408131186242657219800893390210052934694794012225222800114995702396294789639112917014046835596866708468448334676333766859502849951039226590638613270576002678580227743731095390275047033215076895306427509412585598855299403748380572944054863460372194548866353945852318890094858551370, 
    531566878008451469248291847910385268445132525352942749205475973393246237103788046661461904778977341701, 616365761228219484122774134810168976315274398510608581417718984757285836194577597825788591838820229, 145690127765696, 145690127765696, 567915477733568, 616365761228219484122773920138249006311148637927689266523073865973301522587612790211007959937546117, 
    145703012667584, 145703012667584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924924d34d30030db6db71b6006136db6db6d801849241001249241209a6d641a6020120494dc8db79b61863369b79b6db7986186a24d36f30000936d34d3618612c924dbc830c34da4936d86e00804100000d30836d341061b0104924c308040001a4930d86c005124a49249249208049248249248241200041301801609a4d2c924920100904304924b04820820924920906d84940db0000924824924824184db6c30db8186124d34d000001809b6d861b7860c26db6d86de0000924820d261861249008349869841341061800008249a610002012093698480080048, 145275260768448, 145206474182848, 145275260768448, 2923103628376749969234230216413211729373108973379, 2923103628366115820749431080926204192899045862979, 286425741288385, 
    6707465290599979356628218148354348246390697347771048074129348749591642507406691282711097471165069303749107491780819887581419634563591164234428634405244644575429087819415383726433039413545207465102619092276549214160863521430248173076795981970181289781292312363056958004617080010001403944352723137143171628601481937193700356813301477083604293280311004321861337233655790187162808906, 290279937544640, 290279937544640, 8804960833984, 290279937544640, 290279937544640, 
    730842809600966263172718132996298772771879627587, 572304938504640, 145221506568384]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249249249208049249249249240a4924924924902924924924924124924104904920524800020124806926e36db6db6200b24926b30c30c36da0924c30d20d243248000601a4824d00064824d005249249249248201249249248208269249249269049249249249209a49a49249a40a4924924924904d24924924d20924b041a6324812094924924920000d34d34d340001249249a6c00824d249349301005249249248040149249269a00009249651240000a00001209a0120d34104d040000008240048048104a4d6496592000c9249269b0100b46f3adb6c0001449292410490592000c924924920100424924db493492000092492490c92d92496592c100934924924934824d34d34924d3092493492492482cdb1830c3cdb0925820921924124900004024900936da69a4984024924924936c269a4984024324b24924804034db5964d00004924924924120b24964964924980804804304924b04836d85964d00004124924924120814924104904d209248000201348208209249249049208208241009248249249240a692092492690282482492482412cdbcb269b49a0506de6de7b079b0926d80067b079b0b20c60b24986920926b30c008069a0924c30920d243248000601a4824d00064824d007248208209a48248208249249240009249048048209249249209041249249241209248249249240a0924924920904124924924120b248208209a481208, 581126331056705, 581126331056705, 185548483036114594907933588371938036899544891971, 88545121813057, 88545121813057, 88545121813057, 
    539677389416175754180142720732381428101396367631999866091299019051188106667144653456645549544305868932, 5936533528310646667113806574617407077591641402292804242591750871059028137496923511394000249447873146674166017831573732610212360207679500345195244781376968568178125193955193414, 536692881530235262567516252180837327163866389679883347443756637817793045490574824806010077438862966916, 532151239068038129100566330772292550449064637220874485291455509643441696374742716661822089558413820036, 299651555279425, 299651555672641, 
    564721303508401896340443749314800246689835370885154873777405938215245343906811346339501203798754607236, 581126800818753, 581126800425537, 581126800818753, 33997944660723052454634619292816980217158976951309074555820344018374948957062463847406959003542241412, 581126800818753, 
    538769060929150387167604213708577968560407610564359571130018333140285733527602566880404344934741852292, 532410761492902519675577326338935987772136257909086375796877246078481605768636587381737275845438095492, 581126331056705, 145275260768448, 145275260768448, 2923059037435106282537039512341279263034911557443, 
    2923371247857251562776221876910088803621932181059, 145277404057792, 145277404057792, 1144050716525121, 145290293153984, 145290293153984, 
    145277404057792, 145277404057792, 90744681482817, 581126800556609, 90744681482817, 91522607425890448388781968189744974811285689154, 
    90744681941569, 308415973843777, 145277404057792, 145281707413952, 145290293153984, 145277404057792, 
    581126801343041, 581094589088321, 3967612043732259643218270701464363010574791658765243638320885951298311187935000845454357857884137723426774258197145811828854422957977244381441790692767277529583037091241999942, 286156768940480, 286156768940480, 286148170617024, 
    709065031291584, 286165371458240, 286165371458240, 145414981423296, 90744614373953, 581126800556609, 
    971770568674508780509252751302704545651492431609591107316053327173187886948224019762523698552705873797, 90744682007105, 90744681941569, 90744681941569, 536692881530235262567517568549040775521819249173202131286500956769613306277589932386746342010238812292]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a69249a60001269a4926980804d34924d300009a69249a60201259c79b6db6000134100124924130000824806c241208009269b0900494dc6dbd9e60001349249b6927980804926924f301009b8db69c60001249a6d2c8040269a6d26980c04900124000d30800db00001a01049a6d20804000126d20806d005124a6924924920806d869a4d000009248249248241200041001801309a4d2c924920100904304924b058208209249209808000040061809248249248241a61895b71818049349249200009369a69a6000134904135000c34d86da6e00004d30924984100936106d86000134824926d040359b6136d360001b6c36db6d86067587b66db0000004136824120100000800c20030904104104c34c00006030000524c24924904024d86c269800049201049341209361b49acc3c1259a49b6180004966de49b4d800059041049249048040000200208049241249341209408349acc0c00, 1130861005534145, 1130861005534145, 2923192831697908886387651936941544393594923725635, 16609689126196327466149880462898959318900269375200180286792794641290245377117494581837161214421638981, 145275260768448, 1978643270781792212041431035879242555566871035108902433643129563067913232041089921111552508403485400109974370187816406695192883879967835062100443326683602031770018516152866375, 
    3965015557814214339220459148890416254270091649435382542129601923529679136043172297427938230213043582047605702885182496004581077420090745119060263285796511981446691973098359111, 163417622057664, 145275260768448, 286012749123776, 145275260768448, 145275260768448, 
    145275260768448, 3957286453284098376896551028664567146332245004469058099311390516680544999621145940517053922068667833202110629744380294155622708707943745821205643532978662883335803040618294855, 2923103628706398187670369544389578800327324413507, 2923192831697826458647734822749676930250901108547, 2923103628706398187670369544389578800330814074435, 286425741288385, 
    281483844522432, 8867811776, 281483844522432, 581101316740032, 581101048304576, 581100779869120, 
    145290293153984, 145290293153984]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12494b249249a6924b3010093492493410c12c9a6d2c835824924924904d04800124000d2092492410412012c926920804024924924904d004924a4924924920804926924920100924824924824104004924804c200041201801209bcdb6db8d8602492c924920100904304924b04c20820924920980db0f60db00009248249248243049b4924920000d36d24926000126d34db6c00836d87b46d80004db0924984100db6100d04000126c24926d04036d84934d000059379249260001b6c36db6d86066d87b66d800000041268241201b616c124000000104104104806d87b0cf01800524824924904034984934900804921924924121936186030000004964984934900805904104924904806d85b0490000492592492412180, 531567321528223829083114236531192012525116514603111965170684267243792379572013550759838713699908207492, 531567321528223829083114250270194788241833061448697483501271359788589217417678459876529331393138017156, 285943962538176, 145206474182848, 2923371238340061865204738286413290941140414047043, 145275260768448, 
    531567321528223829083115114109994311430434659402829629512586854342111017432851596892781981882271417220, 286081535709376, 523099889565986218262491289224620081819933025621341157408885371213817544283378474572292063464957829, 145206474182848, 145206474182848, 285943962538176, 
    145206474182848, 285943962538176, 145206474182848, 145275260768448, 286012749123776, 145275260768448, 
    145275260768448, 16610449074603487350192158912779425439564230646405489915487364804369025546570160584660448132715254469, 145275260768448, 286425468637376, 145687980282048, 531505989080171503924401620500493394305021254555511259503483889020333626000478100393841226185928024325, 
    830475814727703601799828497203070363632255091376532704305389550755564398010167678914312854877694533893, 537796105275778724860766365770801359317317145066018724072477156492332602328982792117555886247869956804, 2923371238339979437474744035422607332006485370691, 2923371238329345288989944899935599795532422260291, 290823787799361, 572298764501825, 
    290280742064576, 435483994755520, 290279937544640, 290279937544640, 154009018044864, 8804960833984, 
    290280742851008]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249249269a69b00009249249a6c208249269a0000d20924924c20c248209a4b2c9249249a60201b6934db6c30c2c924924906b06924924d2092092410400002400010480000402c9249249008000040241209201249a49a4924924c060249249249209209a4820800036824926924920920824924924934925960000926d249248040248249ac80000496492000192092d12080406480292492492492082692030c1459049278618251641249618600a49a6924f301009249a6924f301009249269a09a4800004824d34de0000924934d37800004924d24924104124934924904104924924924104124944924924904da4d249249209269249249248249649349041048208208249209000000201248209b6d34db6c30c249bcdb6dbcc30c24924820826920188124124d34924904104924924920820924d24d24104124924924904024934924904104924924924920924924924924134934924924824924924924920924924924124100020820934824824984d30004d209b6c30db6c00024820820824d309b0c30c30db6c20d2092492690cc31860c3cdb08388269249a4020b24904836824104104126904004104c04d309840001009a4180000134324804924d24104d24124934904134904924924104924124d44924904904820820800900900000020024824904904104904f34d31804960920524934904124904924920824920924d2410492412092490402482493490412490492492492092092492492412413493492480402492492492092092492492412410410402012482480, 11774883299618267346435291120746512726550909506, 23549676765605515298271939803261061505528894274, 23549676765605515298271942090657326645513294658, 11774839743475301466311967808796761460219843138, 90718577115713, 92057827352349384869809606208535335649887130434, 
    92057827352349384869809606208535617125937582914, 92057827352349384869809606208536180078038487874, 92057827352349384869809606208535335649887130434, 290279937544640, 290279937544640, 149675450568896, 
    149673307279552, 149673307279552, 8804960833984, 8814087640000, 149604520693952, 149604520693952, 
    149673307279552, 431561011892672, 149604520693952, 149604520693952, 149673307279552, 431561011892672, 
    33287806150511640961945655581099213456628561860633009089032974790252749802665398718993531847324147973, 537734519387873474264164768669462879741807840785824949313991930004584615638095454490052206395140620996, 79236782166208, 12131651666569038890335484983409351183915029314, 79236782166208, 572299036594624, 
    183045934897078910834226933387451476302696097347, 149675450568896, 149675450568896, 290280742326720, 149606668177600, 290280205980096, 
    290280742851008, 290280742851008]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149228a49249249301009b49a6928100124934d248240269b6daca049049041241009209a69a6100126124934d2480402ca36da08049004a28a4526b26924e040049a4924924124104d04904c000269a6984184982b24924924124014924926db6db6f301809ac924d340001bcdb6dbcc00024924d36d008041041200300009869240001a412c924d30c069004949249249241009369269ba00012493492490482692492cb20902936924d340000a59b792c92c00016410412492412000000080082012490492490482080012cb001004a4a249269000029a49249248240a4da4924900804566da49249008049041049249048000249201209828249249240240269a49249208049049a4d80000924824924826124c2010400402493492000000092cdbc9e49e0000b003079b6f00c2082092492090000000400413092482492482610410c9648008049248201009209369040009ac124930c240040269249208069029069240001340a4104024006900000000800800124900120004c208000208201000041260049019b790c0009041204a4a26900026b029a49a41241a40a51a41008069800041241441604001049079248000209209a0b048248249248240001049049240661e430002410280, 283745944932544, 72639712399552, 72639712399552, 1135254622978881, 1135254622585665, 1135254622716737, 
    90781673591488, 283745944932544, 72639712399552, 72639712399552, 90781673591488, 1135248180527937, 
    1135248247382849, 2923728051624285395128762460768468135517653911363, 2923371239690474756673698753789098225278822458947, 2923371239690474756673698753789098225259495106115, 531502947801800442927492992558181451690610560201522772818282412050456805156615153628966956289605239173, 183044606434718451490465572372984062679598573123, 
    853773741220673, 290823787799361, 572298496066369, 145277404057792, 1135263212913473, 1135263212913473, 
    2923371239690557509060862098716539182097773961795, 145277404057792, 286014892413120, 145277404057792, 145277404057792, 163419769541312, 
    163419769541312, 90788124431296, 281483844522432, 281483844522432, 163424072897472, 8867811776, 
    73135779483840, 145703012667584, 73135779483840, 145290293153984]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124948944a4924d2596002092492492480482482482c800004924d300019205249248248648048a44949249249201009249249248248249208200009209249249248248105244928a49248249201001b6d86db78618120a4892514924904924020822424924926924f301009249268209a4800304925134de0000924944935801802924924924924824920186124124924924924984934030826d8493490490482492082082012002092482492493082692092492490cdb1830c3cdb09249249249a4024b249848008249041041269069b0c00c06e309240001009a4104924924d241049241249349049049049208208009809248000200248269b4904104d06f36db1806db092048, 90744681482817, 90744614373953, 88519553860161, 90744681482817, 92771453920961300177846456900257787100375552834, 90744681941569, 
    532053419195225453159961223452989326768769381284567048433784117499900101998226761418470086277440226180, 158469400301760, 158469400301760, 4254305046636047378541644972107202048891929538553020190431143210666200547386925953482176841484804357, 17601053856192, 158538052669632, 
    158538052669632, 158469400301760, 88032875188416, 88032875188416, 310614997099329, 158471543591104, 
    158471543591104]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x128948a45149a49249400009249249248208249a49200009209249248208248104a49944929249849a6020824412db6db6db6db6136924924824824926924920804da4924920d309349249249240a4d24924924904db4d34926d30b6cb249249a4124924924864824800104126900824104004d20524800020104804926924d24924104124944924924904db4d34926d30936d249249b4824964934d041069a08208249209248000201248205249249a49248201249249248008249249249249049249249249209349249249240a4924924924904924924920920920004104a24136d34d24a248121249a49248248249a4924d458368249a6924934804024934934d84904924924920920820000800004826d84944904d04924924920120812db6c30180f36124904030134824820920804904d349318040009049249240200a0124924900804924100c04d2080082492402412480002010482492490c024b04504926924d241049241a4934d04d049069a69a08008009a6984030020826984d04104d06f36db1806de09205249249248201241249248209348249249249049049249249201208049249240200a4924924904904924924920920924820100a2c11208, 73152495438401, 73152495438401, 73152495438401, 73152428329537, 73152495438401, 73152495438401, 
    94198707058185130793920158283701001145049682754, 90744145068609, 158471543591104, 158471543591104, 158469400301760, 17601053856192, 
    17609920615104, 17609920615104, 17609920615104]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1]⟩⟩ [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b9_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_15_0
  · exact tv_b9_15_1
  · exact tv_b9_15_2
  · exact tv_b9_15_3
  · exact tv_b9_15_4
  · exact tv_b9_15_5
  · exact tv_b9_15_6
  · exact tv_b9_15_7
  · exact tv_b9_15_8
  · exact tv_b9_15_9
  · exact tv_b9_15_10
  · exact tv_b9_15_11
  · exact tv_b9_15_12
  · exact tv_b9_15_13
  · exact tv_b9_15_14
  · exact tv_b9_15_15

private theorem tv_b9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 1, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b9_0
  · exact tv_b9_1
  · exact tv_b9_2
  · exact tv_b9_3
  · exact tv_b9_4
  · exact tv_b9_5
  · exact tv_b9_6
  · exact tv_b9_7
  · exact tv_b9_8
  · exact tv_b9_9
  · exact tv_b9_10
  · exact tv_b9_11
  · exact tv_b9_12
  · exact tv_b9_13
  · exact tv_b9_14
  · exact tv_b9_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H2 := by
  intro M hFirst ⟨d, hM10⟩ hRun _hUsed hForm hMissing hLoop hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hM10]) (by simp [hM10])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  let m : Move := ⟨2, 0, match d with | .left => true | .right => false⟩
  have hm_cmd : M 1 0 = m.command := by cases d <;> simpa [m, Move.command] using hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  cases d
  · exact tv_b9 M hG hm1 rfl hv (by simp)
  · exact tv_b8 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H2
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H2 := OMA.BB4H2.step_proof
