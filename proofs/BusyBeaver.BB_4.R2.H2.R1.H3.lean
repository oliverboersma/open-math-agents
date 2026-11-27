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
private theorem tv_b10_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144a69acf0002698493592000492092692480402482483c900024804920001924920920c0406492082490000c9a4902924b2c0009241049249a69200069b0926da4820d248248200008008009268208261248249349849349049205149a49b8200820144da5040d04026da4db0c34d20820d28180820134934c30134824006900000020926100020a260000000061048149208001a5920124936da68201a4824934d041249049049a4820124824924136124d24124820827124824824926d30c049849a69b4d36020126b26834d36006006184dc6c00c00820106d801800001058600308269a69808001348029249241009241249a4d04026834944924804904520806924800800400004920024804d049000059049249041009205249249040248105249a4904026824924904004d04926d24900920924d24920124124934900804d048209a4920020014d20120100820924134020164104124820020812424806004c008008209349200008208269bcc018009041349260040000049b4c04d20000020980224000000824130820934820804900826924c00800824d248201241009a0800000802924104924924124900904924900824926804900400104920124824f27924900800534804024920864100004134104920100924820534804024920810938c24824984024000c30000c36104da4000d04024136900130100824c30000820135820004135824d30900104d609a40000209a6100030c003208041248040249208249041349641049201209209209240241249240001079e01048249008049041049001a49240208149201009248209240001249041348040249208124249a6904826d6c8001309341a4800006135904120000c28b00b240000009243008249bc9a480000c9a4030124904360c000209208249008049241049201009a4820924020124904128800024930802924924c301241249e50000468249269b0c049069a4924981b209b6db6d86036c2c920d34b0000032080402000c106de09a0001b209b6000186000c241249c09b7800134c24934904124904924d24124124120984800104024904104924904924124124924126800064934826d66de18641208049349349200009409249241049241249248260040249b4d04904904900100804800924104134924124824004124824984d049249045359e6c001c4c10514924d24800024c149249209b09209240040201200149209209249205144169b69340009a0d369241049241b6db4d21004034db4d349049049200069249b0180100924934124020da4d24c24834d34d249049069b08000048005105249a4906026814926d249b0920d149041a4926c26814926924920920524020820120814410800100804820100104924924000004000124804004d049049000049269b4100104924924124020124927124804134d249249000079249301009208000049349204001e6d35804c105a6c04026d20c16db0d209b49208001249a7924c169b49249b49208001e4924c04c145a6820924d248144149300019b6db0924820c36db6c24904104d249008369200009a09241a48208268208000009a48209a68208269268249204905129a6b3a0009aa134925800934824d24920920d20920f20000920134820065834824920920920d2092600032092c0a69acb001a6b041125a69248000258149249209209208208040200200149209209269209a50200061458144124a6926d86026984920934984026802924904184826b04482494da4de1804120924126920804920524d208209049204909249b4c30120124934c30db6c269a6d34d808069a4d659b0da09a92492492412409a0d34d801801861b6db0337820804030006000c3018003c1e09ac1249b6db6c30134c249049a4c30134024824820c34135834812820804000904820926924920020920c30dbcc00c00104d249801000209a6db00200000009240069009209800201a0824d26924020036db6db00300249349249009040a49001b0c00030c04920934c00020984924904186826986db0db0db6db0904920db6dc00071e092012698000412092612080010412092092483016493482a920920924da0004d24d009201000309240209061b0d801801b0926c2c920000186c36006006c24904d8492690c9208001a01a09241200209243249049049269040921249a69b6c001b50249b4900034a04924d24020124104184800104c24100004f349849a6020126d04134c00037934c26de79a000d930814926db6dc0007160924126900034120924920830db4d209205b6db6c00046c36e3ce8018ad86db6de1830180dcaeb79b02661e6c001b6de6c0600603db3d280d80c36de79b01b0dc6db6db6266030db618603cc4d2c92e100ba84c145049a6000026800004104d041041269a08209a09248001a69268268200269a49a09a08009a6924824824812524800026d20834d049049249049208209a49a08001a49a6c268200269249209a08001e6d24c060269a68268249248248124149a4930004930524924900026c269a4980026984db69240009b08a09b4920004d80004100000000c36db0000db61000048000200000208000000029a69260009a61c6d24c00134c049269240009b09249241009241249b4820c34824958d048049025249248201a68208061048068004000048201a4809a08e00009a065a69b5030dc78105249b4c31504814926d248301209a692618682c1b6db6c30d87826db49b0c34120824da4906020004924c30d04830db6d861b0c019b6d248301201009200000000000000001048108249000000201249e480002cc24924904045904924d24830920924f249361241a6964926c6c866dbcdb6d8d9848249e6924c24810c36de79b02301b7336db61b61041209a01a0812422520804920104000004d340069808200208040200001b4d06026c34926db4d80006920b04b6010492412c1240001b4827924804108d249a49025245c6590000c361b0db60001b74379b7400036d86db0d80006de79b15e0db6db6dbc1041e590c82d804125904b05904926d2c9e0920924f25966924364b17992400026934c24980006de58351200009a4d36b240001b6924068824b3ce26982902524924c00d34814924924920d209a6926000db6124da4904026822826d24830134000924004d04824d209209241200008240308240a69a49800269841249248040248149269209209205a6924820d248128000248249248149209209249209144124a69a49861b6f04920934924d86902904124800da0986920db69b09204824949245200209209b4920490912820124834104000124d20d34820804820d008000069249b0d20d249269340a4000924920924020935864944800024924926900824d24944da09269a6b240920949a0004900800524804020120000020f001a0980004124134120900124904c24800030920920804c20100824800004d308288200a698080412400200082c004820000184904d04804920100824800924104920924124804820134824900104834900804924006920400124920824822420820924020800834d241049068079240049205841a4d30934810524800000134814920120804d20004830006820000da4104d04020024180034120000d20826820000904000904800134c209a08008269041a4120824024100820130c20100030810920120804d201248040200200249041240041049201208049209240241009240001379e0d048208349241249049041a49209248141069b4c24d20020d34904924224800824124812400004020980d00004006c06c000001069a6130000105860130826b34d26b000009049269a0104124924124000024924924804124924924904522524510504004820820004104924904904920120800920924124934924124916912400004824924d00004004d04d2000012cb2692400000082413082c9249a4902000120924d34000045535145400004924938b00004d30d36e30d28a269a60000261249a68041049a49349000009b4928920104926924d241a6924924800004824d24d00004004d34d0000012cb369a40000000641b003c9a49a4b02000100926db40208651348468000041a693cd008249249a6f209acb349a40000241249a68041049249049000009249249201049249249241a4924924802524820124934814920920924d20000838006820000924104904824124924920120000c2c8248241308040249208229a6020124904080020800020b04124804024920814920920926920400124824824814924920926920820020924924812914412480120c00020984900134820920802926904904926906920db09b6920482490024de19b4d20920026920924920524490000100826c340208040000000000040209b6d808241658000209a8db69ac11200012092493402080400010480000492492690082492493002092c9a49a40a48920a490080492410492186593db209a6120020824124834826db48061bcf268269841079218049308009a4824124c2483c980024804934c040249208249acf3c9a09a61049201009a482092430cb27b64124834826db4834d289051c6d00807926004800c30f3bb00e3c1041a55e01608001ccde0c6cc059a6800164d34836d8a2baddb984d209240201269041a4800066d24c26984904920804920100934830000dbaaa09a61203079c5985120820d200009a830c1e7164134820186931034da0b24134800026d20c2490432d9ad9049208001b59a0d341e41669a4000186066db0c06db6d861b0186db6db0db6db09861e7160134824db61b61b6dc632693482cd3c8361899dd8071e0820800904824100004007804930820120020824000184024120c3c9349a49000008079e49601040208000040000219e7964804120924180107935964d20820024124904000004164d24c20804904920804100d20924830d28b26b240000048609218041048208201008209001059a01040049000241e6925336800004824d24d00004004d04d3000012cb369a40001040641b0c3c9a4b2498c92490248, 1162192523235776, 1161230450561472, 1161368023863744, 97053213341864731057460873792812928236276175682, 246842648500417, 188397414118862715603836679240523322994332816194, 
    1161368023863744, 1161368023863744, 2923059026737489031994782433108270003917781226306, 2923036725907219914712008682437071028210169303874, 2923192831719103771185641743525885129746305536834, 1161166294815168, 
    1161230585041344, 2923192831697836194241497359674730537644030186306, 1161230585041344, 1161230585041344, 1161368023863744, 106105088837697, 
    106105088837697, 106105088837697, 188397414118862715603836679240523322994332816194, 106105088837697, 106105088837697, 106105088837697, 
    1161368023863744, 97053213352498595588559408669680042971727156034, 985889914280106651719924973826288712043684318479730169496497164527679558014588998369740912979680820755405772109578928494616766799405411329572887502194929266338054798634062906685618445229351269002431945118315857618598142273889314426316805587969925458652300296245997512, 986300481606681895427722655753053326368583723889986813524878326578036852294067907499053623132902443349788211349047888460455792793759774369213984471105067616945340386692844300646201735839664793614843784857956026971956027224222263936224880390231134596382065672245997512, 64888527178777394292726084530644438069374075529142258349331624157991835659082872260827106435462660, 64888527178777394292726084530644438057171389755550550944434849519276132146179893276789023342392836, 
    572854693794240, 572854693794240, 581667966686144, 7759266745547319253283132029449942412559925652816067110688989280332624922651537520929031454999474710403676530026757081107937933005238216907955156682345197897021306645246534, 33283751484824637256498319210394984672175035088843919516823192365638499410766864089871601360896587268, 265751224421003750996681556266260857299344152924196091844706190003795997299451077668383975182434468100, 
    572854693794240, 736462597071960573118131364815653605554618651458, 479600174901430983578310474522501919309756913474, 572854693794240, 566259771511232, 572854693794240, 
    568460942250432, 572854693794240, 28545062787022455079218812018139998298270880578, 105624522262593, 105624522262593, 106105558599745, 
    106105558599745, 105624522262593, 105624522262593, 188397414118862715603836681306558659249802597186, 1461685619201901372444224211602021964651211805506, 150642228859328, 
    91524001263601485326136639974898517690527273794, 4217239420481885636211881718396241121996895082345312794086836267525469162424114352590520647534473348, 8369598326593329836429376000480950749743964767251073467543208054131263541702573101187822702062767620, 33283751484824631724446425762283836221746149921812809320166915086863740099003813990999637272300843140, 8369598326593329836429401759434414719626425658249086019247005487842290790100768789934303109571474948, 33283751484824631724445106818017367416921045251240919612251833609528510926415343107504816478192103556, 
    596966457810749960805340755984358309692571200534275863574133148774981028531476980720163477217934012548, 15488342035310490762460673676091772705252472612117988229446376022676007557192402720366662819703721693859016909411165331390792609413803036893372780840654234898326256916540998, 15488341795068494133853986833984627734271689341328638928502284116372349735127885266764201037434158309544781211930698668204737939428561689884167019417593684233261547949043270, 15488341795068494133853986833984627734271697659168493383766268703331999056730705825393123380919875839201715718698198812130593278809271276644349482503263508347383428393643590, 33283751484824633568462844125612451598521274041525347180320281697844698591785250072572157526664082948, 33283751484824633568462844125612451598509071355751755472915384923205982888272347093588119443571013124, 
    33283751484824755273633521923436043029485874619799508328075090853728021312363860345724549604250285572, 572854693794240, 566259771511232, 581667966686144, 568460942250432, 572854693794240, 
    572854693794240, 105624522262593, 105624522262593, 581395120223413659886869390627426463909128703304873447816465668733001657821266443973340683125721886852, 175993266444481, 105624522262593, 
    105624522262593, 317005641099585, 316730754804033, 1461507215281996944391295781243578430755270841154, 566259771511232, 581667966686144, 
    568460942250432, 1461864025844049158974665033710070905308622910274, 1462220839128360308925541993883560239316120654658, 1161368023863744, 1161162066891200, 3957317621643694791034181319997630199813984359540437279068292281375116768908022258221836439962487129932173204658429136777709511399564708129258197048555146229777290346285223495, 
    531571439926105778932383466683754414254415366513983012490357296471514409535946556116477042130935535493, 2924441673409015413141749008097622393832108741442, 1134980013232576, 3957286427485527111778661891709499483189078032854766494377452646512407294094090371499094231434318853575002582213786962644090683534981877962100942506844505505841942197551746631, 3957286438542057654937405121470994564346813970897303669436962639168614438158654912456589168604147546091738867614109842307289040258395360688393606558461779899435428004912082503, 1161230584779200, 
    1161368023863744, 1135254622966208, 246842581457089, 1135254622966208, 1161165958877632, 1161368023863744, 
    1102970368515424571948412233889837151021649385243829491517916915498320403237105686623651011145813380, 246842581457089, 188397414118862715603836679240523322994332816194, 176473902289089, 1161368023863744, 176473902289089, 
    188397414118862715603836679240523322994332816194, 1161165958877632, 1161368023863744, 123695392677449368553386493471178429479502205860844919282900085640861996919430318870277143993937610328876646812884823367471226792667496555945268613412874485965207376273649223, 123695392670135118874259415819966837262054512654089215527300686440461783328613314510414723335322932683629246455174791043641143820629116834448554724178701673764603522423500359, 736460179664830126306997170297233696473661592386, 
    316943362167232, 371089997073237616976474383349547598989246878530, 3957286424260705703930545572090561063477159175196915907376166662676140462400758948036828680258092899397552820942187192684118345580442472371582868210868398658724065560241679943, 960962161246946106553613076086465357131036759671323635134125297822113308052209484351011208165369165167585729455828723300064517432407811837568855559408312297481478623836337589536748278140847005429440600183959410902179622900818718637618171305242591205055808512249156553, 1161161664238016, 1130856844759488, 
    1135254891139520, 302860714939843493534362401949584212706720400288109217380040198069051387860436502344591765287378642155063049270810756273281712076087905856026110805998151174884995404484167, 1161230450561472, 1161368023863744, 5777511356834555515219647630061847477074702918647034492580000267644424107759305187858171693335561120613301092601108927869281436339017249992738947069412923402862317832662456387116890667247950542555145567328107730873023725020458136249479471563609309248448338870870752591488233847408274250949729578306739540056693151178710352788246251495207536508511086212525130427256661802318671081112579799163939941987588600514141358464089859300136673698110059841684445791511762675968234259309289097409660700527376700461420981570655880742527981200325737724943936123351443382326291864014593536957925160478334247753731829500928012105648068604904111704183352163567745113173521313359, 387099505469761, 
    4217239420481885636213444533290124918089668315388447499760306120234593242876281150848256258046390404, 33283751484824631724448431660043339586902202521825504101652894335913188321997658367203223186693124228, 1161230450561472, 1161230450561472, 1161230585041344, 1161230450561472, 
    1134842574672320, 2928723416146187607405006377856594668239693306690, 1134842574672320, 2923103628356156592299588970364563135031341503298, 531502440922011507987686236580303748944326178567855615118265343644398169661714195309067696898845090693, 1134842574672320, 
    1130448823128512, 1134842574672320, 2923036725865349225239460515353958832178645193538, 2923728051603692018194121214461564138981534225218, 531502440922005843165168365441897534846965065808643746884658228480132777112521542389293554413890223493, 2923371238319386060540102789115703335470365692738, 
    2923728051603692018194121214461564138981534225218, 1161509556654528, 1128595545067968, 1130723701297600, 1134980013232576, 1130723701297600, 
    51381112941397519878449242232109965178484839234, 1130448823128512, 105624528750657, 105624528750657, 51381112940722843231948597316778935594842606403, 150093009916352, 
    6767287374885997093902291746569410401516562736030096685260387596054770198621356829905004381020575856440712208873417660643163690767172507248492580287015461377575345985139061508745500451996405190663663101462151455170974205526079472978868483445672848432555219362146549978389285898337030129289822055620379656985261218352891635486950567727872617254195299076847163970355737246087094218, 2923362178651623597769214953275735501830860337986, 2923719688834211817208348016785164358056950125378, 290830498402752, 284235576119744, 290830498402752, 
    308439864316864, 572305474851264, 565710552568256, 572305474851264, 572305474851264, 572305474851264, 
    572305474851264, 572305474851264, 6059625031706314223707550154661728396192740636449871314918306649817884444022675186291152654844532043355990048385154516023714760416572814287395814614091644176329060717734874695, 4081465830602461327507528779642176134397774141327783471364675099441821308888342557529135202338182853104100934823193066249992841744034666622276491267195010211252349730199391815, 4081435635217552574686924372804637969392972500873030933009469706770203752378123918112068194951308797191233209151372697301015160145172498772514786854189268435212661420141268551, 4184086473139170113139551377906408244332120736991461723925990267582204679616301682622973871527116236367547345819557558558940907498549005058638793046746551988221484175298886214, 
    150093009916352, 150093009916352, 2928723418532815193509639225596081491855743669058, 943478696055744, 2924430615081810508775530735286283366472372770626, 582838882145216, 
    371799420474063851423504315845482329124391375682, 1139244781801920, 1134979610841536, 1134979745059264, 1130448420344256, 1139244647584192, 
    1139244781801920, 1139244647584192, 1130448420344256, 1134980550365632, 871389817476032, 2924433315402834117110101937132143026071945663298, 
    149818131878336, 290555620233664, 308439864054720, 732002495629432090340960182324718831202253959746, 943478696055744, 366090429703240011899271171967684348578860389186, 
    290555620233664, 871389817476032, 146248074531264, 146248074531264, 532345381924043839394587228580701299332535439625827021254190390578454937288667962801542454418498351236, 551485156945714612344931938677766749185404960269287372796916445009045462464603912841366031205199941, 
    583925464646046210032322761879718552918034719655875370994745809412683899127542596306089656005983109, 930128885513709663117093471377052421616564511323571471858714647401482207368242196036652152236750893188, 156209043083712, 97053213332550039479209989992959978697417298755, 5935929639385535577429803503125780323649620057910127867448906346559964672246525825790216583736411111414682439423199127955262291716340387068156758203151989294637829299168574023, 123695392443150858820958396886328704180835870242187726439453002486238387720688085043371051444047312456240092311681427703789799012663347074877407775982532138229399071926242887, 
    123695396123262342757292935738136197860268167280718649810263118275536539591136108077374228011139987859525106974202982857763503409433510200787219110482954005964305673589050951, 33218934237609691583668613582334353027404647282541255635333050550130512604901900712293545108513411269, 537276300084205755764961924168696525500972770977521969075963279112239176127777947883655760180101214340, 33283751484824633568463998202056886966662908155405518760116632386452271230494776857040693778890807173, 567907428209088, 572305474589120, 
    1978673477309610648612325225753955259882136714895893642931657234658799148506035481573122551025847668995834903669766358728148743452035579207366056967280552725353316639571965510, 572030596682176, 1978643215585518646171095656064068763669315682367955551771229793093406090190997195851982664773632348219999078997239770330436657443484239948494396165335502703251999318651927111, 2967964821535522878989962557807750047221304721201283969975632787949562824173355386810400718756207461749177681335349906406377302153529670506698100698616581778068372813034519111, 1462399242410390906282614950250348926568039994178, 549133597408331164252474600524216215481041842754, 
    290555619971520, 290555619971520, 4184116666679525967585436766626298376858117259588101159830069557051822214627639089090615781128348263369365304253940447844029119958275967991772120349792277763535762167131241030, 537796105276741744684020501629611755130445456271463894500083793965740089657655925186543969689174975172, 146243779301824, 146243779301824, 
    1461685619180623542704268465899486437583890748227, 290555619971520, 290555619971520, 146248074531264, 1134979745059264, 1134842171888064, 
    1139244781801920, 1134979745059264, 1134979745059264, 290555620233664, 871389817476032, 79311948353984, 
    79311948353984, 79449387438528, 79724265607616, 75875034993088, 79449387438528, 290418180886976, 
    283821111120320, 299214274171328, 583925458845267951735794218836553334534592207725049883765662838731439605221917755555461922276538245, 581395120223413659886868525070238542403632482699997916094739524046029575447783464417124879683231641732, 583925458845267951735794218836706879856607631964104951617987403440057297799590417335824911856859013, 17127037646852446046594006511604511702962668355, 
    290830498140608, 354604320035264, 290830498140608, 159437918704064, 146243779170752, 537795352846196041671507566507691956330410347606432603434034180867665844880598418481707272351648018564, 
    589699837819074160131238203182591064576023755405719285643747126829862168797695421558464737237473128580, 583925458845267980548559346308943340335940677614917147610024537459734045785078116201487487389430917, 597874794202302459844176738222032291037700726359850857452666572039214007822403573179433007083672531076, 105624268965953, 105624537401409, 7172613131733410130375772333950610988237470931491797415099183765071978095699071877389589218366715611088318725182725699243453282792926693128384266449449252193492778326519968326, 
    566259771511232, 17138188019285557858111373427175232349852140099, 17138188019451711357584487911288208301106659907, 163857843229632, 4152422173266235318099053321687403872139351983163629746053029730044369508543084092836984672021208453, 91433404145939703154661549671229100899273036610, 
    91522607467016192568166156007694301777065169730, 91522607467016192568318481242040399998826337090, 146243779170752, 97053213332550115538246003687879241812620088131, 97053213341854670943921207494865043340079928131, 97053213332550115538246003687879241812620088131, 
    97053213332550115538246003687879241812620088131, 290418180886976, 290418180886976, 7759266976060414801213070427961325411673719582358885995275181567931121550098634189431189829757072577890527525301894252312794851410381571867626128613403276153124024239972934, 30946491887137527512635394397712577111512823296761823934514076658901896438619759386000862258463422778083601639399050759481929700299007868716984128092618311609727700052520519, 16674316293503636767759155338488789874573383475383273916762540505837848875220696401019872641034294725, 
    2076195733906855321612002474673359026728087012909682768786220147972022392550647139071258568154997188, 290555619971520, 290555619971520, 146243779170752, 146243779170752, 146243779170752, 
    1461685619180623583269087673203982458791403787075, 290555619971520, 290555619971520, 290555619971520]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249208049241049218379bdb20a269240208241249b6c26db4824105931804930800164c34124c2482c980024804934d040249208249a0f3c9a09a61049240009a4820924306b27b64134d21026db4844d461851b6904925806004800820f01b009a40001201e0d00000020804800d04964305b2db641b6c00164d24c24d041369b7104924d0c1bc9ed9009248201269041a4800066124c289a4904920804924100d048309248209200009a036c9e6d641258201859b10049b0b26134800036d20c2490c1ac9ad904d208301859a0d34de61369a4120c24c301b81040000001000241861e0100124034926d049a6d04d34db4136a24336f3cc3cdbcc3618780d805120d34db6126a44020820904924100005835924930820924020824000104c3492cc2c9a4924900000807934960000b003209a40000219e4d648000209048619059a5934960820824124904000004164924c20824904920804104100d44830924b26b26000100834d26c00024106808d000048301849a00000241008241249249b4800024824d24d00004004d04d30000924b389a4000134c641b102c9a4b2498c9a498, 1162188228268480, 1161226155594176, 1161368023863744, 97053213341856942582462510608521005894203364162, 246842648500417, 1161168509407680, 
    1161235014226368, 2923192831697828405766498996490438615301957374786, 1161164012982720, 1161234880008640, 1161368023863744, 3957316615583996840305502105275119275146462354483584645858008412828272418220689533581972247716342617507631939523255966978482127237097631810502091741832596975364596424349363782, 
    315644150232281319585688704440047274065724013520331488019333708472483661730984058615409985961264902276, 106105088837697, 106105088837697, 188397414118873100197553748895780383986991256386, 7759266745491082830854615465272516286695947219170259193229193032845680277271928609702070183409153745425390482043033845228264497877660088695242869581933548039617762857793606, 33283751113574826881503524441640741768576169950949607551338065188493535716951132493214524170132746372, 
    106105088837697, 106105088837697, 1161368023863744, 3957316615583996840305502105275119275146462354483584645858008412828272418220689534290860767521769375914189116393078085580066195202852812546177276587702096847823663435043089990, 176476053967296, 33283751113574826881503524498662970085759807968099669022920617515048280873030983126616949409942040708, 
    1617723703641840315648101931354441611284239374022718320678913565690803504456614515368334511843149237858463555402642672372596272993555216932475359167439158930829464993646144893095612648015099757893960491486739638065256248753868789068244535795556152740746888200245997512, 3294089090345329113525181418652120263633986933570, 3294089090345329113525181418652120263633986933570, 572863283729344, 581659376751552, 736462597071981342345179585383299896336707539778, 
    736462602516499213080195000797293615244998923074, 581659376751552, 371085815683523277117811753219554224322121847618, 736462597071981342345179585383299896336707539778, 570924688307149195025008166154798084985582583362, 572863283729344, 
    566266213962688, 568465237218240, 572863283729344, 28545062787014666604220448833848075956198069058, 51381112945385219077611192589574204322985562946, 105624522262593, 
    105624522262593, 105624522262593, 106105558599745, 7759266745491082830854615465272516286695947565753970958331050480147453295157392060737914547014663726457434291774350584945937844695333966827441866113674544479870465584609350, 106105558599745, 1461685619201893583969225848417730042309138993986, 
    84682268545984, 73687152268224, 91279338312640, 75886175523776, 80284222034880, 709207020671936, 
    150655113761728, 144058043995072, 163849253295040, 146257067250624, 146257067250624, 91522628564564480160368481458899827305853571906, 
    150655113761728, 172645346317248, 15488342252101899237017496154746437805140404184502134242012094905180621061254801855520760079657442436792198065514231942198628014210375451931267902132864348055375229809176134, 15488341795068494133853986833984627734271697659337723697256933060269423403162753533445378956628061171276423459325383095500193663285724662179423189649262574998780811251134022, 371085815683523277197194658829025044817323774786, 371085815683523277197194658829025044817323774786, 
    371085815683523277197194658829025044817323774786, 572863283729344, 566266213962688, 581659376751552, 568465237218240, 572863283729344, 
    105624522262593, 105624522262593, 175993266444481, 105624522262593, 105624522262593, 105624522262593, 
    1461507215282038482885006303636003181116220592962, 566266213962688, 581659376751552, 568465237218240, 1462220839128391462825535446620727928684411966274]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249208049241049208009a49209249200208261249a60249a48000040000040008208008249201000001000201000200248248000000209211849200009a68208ac9b0c04d24104184100106d341049300009248205248208249248100009a0820920420c268249248208008249249204925109248201249860a49249049249020001000000000840000040049009a08209a69a00001008268300a2924db61369a40a2134d84038da0814926d209b49204009a4c249a4814800826824924812512430c30d86db61800078379b6c30c30db6030c36000186c36dbcc2c9b4d25102c30c361b6c06030c36db6db6c36db6d86db6d86db6db6db6db0924d369a4100004026d34d00820900824920000106934d34020824124824834da49249024a248, 1161368023732672, 90575098211533486263658875835525405557956262325384789411561096367837584018056756665999346799387155741933830245068078368928717095825903206743989882786374883481125897154119, 176476053967296, 513259120171080175753226092837196870740343357413711208872743735545406521996694640062494244155431912229273297616590101396474417815677950181293249552280126172327256519913031, 581659376358336]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a0804104d30524924004104c20a20804d24180000804104100824820134906100020105804000000020920904c341009248208a69a0804924102000000000820104920000934820924104926924124820c041a4824920904a24900000930100920100134126924020c240241a4824926904824900800004934d208b6f061b6db6d849205a68308071848149249209241208249a4030826120926904da0900104d209b41000001008248200a49a49241248240000000000008108200000041200a49041049a4902924d24124924000d860351c0c04004d84824906924124124924000026c241348249b6904c25924820c209b0934920820820904d241800040041361a08209a4030824000104006920c269a4924904820824134906000025104db6c20826904da6904104d409b4d30924924a24000100834db68041049a4c049008249b09869a0104836900d24134925924800024824924d000001000041000009249249a40001040040008249a6a2698000080492492010412492092400002092592480410092482490c9a4934920800326164b36804104804024d0000a9e4926920104820920124326d2592482450, 1161226155856320, 1161226155856320, 188397414114211718193375211086718723749283134018, 106105227319489, 176473902289089, 2928712461435939096728503192229893567414777444930, 
    1161226155856320, 176473768067137, 1161234880008640, 163849253295040, 568465237349312, 531566814648491542382947272046950254175005522743756402358304206477694553888936836442413428821875944709]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249208049241049208249249209a49241208201a4924824924804124984c24d041069a08249200009a41369240001a6824924824800000104002926c301b4c001208000269a0824820d349269241049400049a4820524c209269248100009a08209204208268269248208008249249204925109248201209061248208269248249249049269049269a0924920104924130934080026904da49048200000001200a4936d84db69028a2124c000249a0814920820926920400d248249248128008268249248125124000040200048000048269a49200000009001200001a6824924824922da49020001008001240208249a69248000000240049008269a49249208a48b28a2100024824d24d00004004904c20000924b3692400010403413082c9a49a598289248, 1161368023732672, 1161368023732672, 176473902289089]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a200049008005269040201200209a0804124000000004134130824820104900100000104c24c00000020920804c241008248000000008268200a69a0804124002000000004820000000104d04c04924000824800924104920924134900020104034930104024900834804006930820d00900924000160120004000034004804902924104920924020800124030024104104804106837804c049309841a0140104020834024024900526800000934014924100824c00824824000820000000104904020920904028900104120004d300001008208200000000001048000000209a08000000041b4120824824100820120c20900030810004120004d201248000200200249041248241049200300069209248041009241b6de01b0db78208340340249041300009060000001001001241041a0100134824900104824904127804c04d30924004100924020984c24124826186804804920820d00900924020820904124000004004d368008208240008240001040369200269a4d24a000009049369a0000904124904000024d24d24800024904924904922924920820824104900000024104036020820904020904104100004130b24936a28104100830c200000241049241041040300069200001241349241a6926924800024824924d00004004904900000924b2692400010403413002c9a49a4984000d30924d34000141135545400034da89b6980004d60d46e30e3c92492a0001b61b6db6c000361b6db6d8000ac36dbadb0000db61b6db61b6d26934c00024824d24d00005864d34d60000924b369a4000134c651bcc2c9a49a4b0200010092cdb400010000080080000412c9bcd80004900820020eb8b389a4000020134da68000241049241000008349369200009241249241a692493480, 1161230584779200, 246842581457089, 246842581457089, 246842581457089, 1161155221459392, 1161368023863744, 
    2928713681017920316200118024811600876564977308482, 176476054491584, 246842581457089, 106105095590336, 317217971900864, 317217971900864, 
    1161368023863744, 317217971900864, 1161368023863744, 176473902289089, 1161368023863744, 2928713681012603383974260210473049508715708830530, 
    17127037646852446124119546352047797124823274306, 371085815683523277117811753219554224317826880322, 371089997073248001689033696776201166372221244226, 371096966056122542508765426688161368985191863106]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24904120804104920800824820924100820020124820024824800020900da09849a082000000000692003082c0800000040040008208209a4920924d34020d241249a682492480002090cda6d808208209a49200000041001a60209248249248049348200000005249200248248108249008248204841049049249000009a08209a04268268249248124208248249248109241848200000a490402490490200082403082c0801a4900da09808208209a49200000001001040a4934d049349021049241b69b4084124904db4902134c40c08020814920c049b0920400000826834c108209a09a4920104124124924112420824824924812400026934c24d00006db4004000000924db6b2600013418400602693cda69820009a4d309b60209b6834d36800024934da6900824926934da0924db49a40001a69261aa8041249049249000069a09269201049249249241249249248000208040248000069848248200008241009240001a0124824834d24d34902480034d04034d00820920924920000d34104d34020824924924824934d2490248, 1161226155725248, 387305666062657, 960962623049271792066550222853127700216391238233388630342511442079169491564066320503265385309709892588194564491764103108313298865179883064971183086674359025162856497505490205855152649079206193176215506676135415689459679103771867610828237410619062414880015368749869512, 2923192831719095977640021636541774791055786398530, 3957287367290623191565779142076835871100275577086034096759580964391097153022990195711243382652522260208150548836840749121141801039198066556563110042556327789462996730383398471]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a4900000000524800100004000020900c20b04c0082400080000492003082c0a0984120004000024930184120186926030820160d24c06104800020980c208029a0920000180060d24006104004920800000800924920106924124800020004024900024804900804900000c00884104904da49000001009b4830104124136924020c24c2792482c1891349a4900800900184d60820c25836d45806185b08e28b005a6836000034814920004800d20000824030820000124006105800124800c20980c349301841208240009000240861a4a00c20800000900184160100920030820186000060d36810920901800c200a490480400410292400090012400000400713580c300d8cf3cd80c20930db5920104124136924000800124024804104904f24900c30900185160b061b4136924000024c27135824104124138924000024924824d00004d05824100000924924b280000001040060249acb24b000049269049a0001b260209a40001249a49658000289e0807984937944d60000924920934000124034945800024924926900004d059311a092c9269ac000134da4128800004024024100004920d449200000001201241a49a5135820804120104000004904c00000820000804020000000130004024926da4f040008241209340001c6035944c00024904920980005137930e50926da89ac0001e78361bcc0000d98cf3cd80006db61b7b60000f379b82661b6f679e6c00024924824900004d319649200009249249a4000134d24c66c249a69ac900004920806a3010492412c924000124820da68041069249a49049269b49204001249a4124804134904b24900004924924920104b249269241249a592480, 1161159583863232, 1134784592352192, 1130384398095296, 1130384398095296, 1161155221524928, 531501997402235843673079251391498396625605312665097025177289656288938192430147855236054781760230295428, 
    1130865434432448, 1130865434432448, 1161228236231104, 1161226155725248, 1161226155725248, 1161226155725248, 
    2923103630738124074265805632697383515061938576194, 2928723416146197992038337528768982772124921944898, 1134855459181504, 17127037647351882010215725306021564419439352642, 6786989525284217980296104277765329144192625998130967865061676583174901665904577925653375850707244479493780080054784518556583337422052719078734559139883209660750435033596220401088714670092525501679293968436894751846429540632769706694363440998347725520685384728528394830190933410904589501128634120853027746468888454638374056668817283638298208065932368269236664943263033780881228874, 28545062745142526938805336373567276776832392002, 
    0, 1130457412801472, 1130457412801472, 1134855459181504, 1134855459181504, 513258889805605223322660477602494454177167359680385778523987163160918799298785694561489060155259322522689009820791894111673779590028702276146522366209840511257557805792839, 
    188397414114211555934098459755508811647340796738, 371085815678861874791532236836240209365629426498, 1161296955707840, 1131007168615360, 1131007168615360, 1161580423614912, 
    1161374265184704, 1161580423614912, 1161368023863744, 531502060762209460540554850491807979999878697559114700297190145738864701914066095432877487310573194628, 960962154094212046835217857624440951243359382280315518482490121334476533306185990189595048697409830025583479115931750073887918846042871854180621295508945741583309341626936967091649550899027742658509871233899840945804589701710234356934680079270449217890435593246988552, 1161374265184704, 
    1161372184744384, 2923728051608344333965626677507742543217508242242, 2928723418532815193549330678400815776194847855426, 387305663899969, 316936919720257, 2923728051608344334045009583117213363704120234818, 
    2923728073386415816985071244773188239337285768002, 1161580423614912, 1161226155725248, 1161226155725248, 316936919720257, 1962460461133904581120051055661515031743141500265131503804660760558819597681332446183386008156141299122240077625885138771565201544707108174050501812506983404074189043641926, 
    531506258360201468241526406609260494532571186939662600175167222363530425292141727991221803521690100164, 1130865434432448, 960962852420952156108866577342046869517301313185600229925932242417537337386704402273726342439597801209705035097878318716212170909209304278620644701171996983605831712829047668602789437944571079846200623469717325480237640274096312540300163765824212436068074504749869512, 1130869327008704, 1130849932284352, 1135265158927296, 
    1135267373388736, 1135267373388736, 1135263481074624, 1135263481074624, 2928723416496427864135943205825999822611313349442, 4152374699697205453578210812462678843257511339888420574023145928562375941121238797791042479849534980, 
    4152422219673169487284364745720631680533805825575917028903490445916333060823360904008926746340554244, 960962154310961563796381349092987151144748375090170272406645434056601509036110545314688252114259625885789893472573917070039537801698584046544082916862614964330498045730834922862597267007520525196185360990221862995668512425312157730258658308859542877111321608249877512, 960962161246946106553613076086465218325102661266057768697720979430207109555524067777828971004691926426173572727874711773197570002640726331273244134434109052772558808194870656401960031318829511440270071298927364683000215624717864912764677311986854811383366664749877512, 2923036725875357780537895060156365969151378862658, 2923036725875357780537931328069304988579441685058, 2923036725875357780537895060377726898035893482050, 
    6707465440523364112167751531215043645898589142114637738100752393845089266622328091197551797422297112616002094817482167332815268125104674335932041935451709964997657826810215892381048109902110738521926083062695477888262894905352451857907601557115875355047335489473843573136739961743604517970409327475042078278144731556384659257028637215435451755413730548874421137896332020707575882, 2923371239701149794513623937203904630659446043458, 960962852420952156108866179897415239361024108221294425755693281533781367665818651474375850183486627175161911000239853280137360688780863369190918989262565005732184638794188869475812766439351400575904332176787556539181348667805927147696764426983987179591566344249877512, 1130865434432448, 2923728059791103090571527337015482366916839953218, 960962154094212046835217857624440951243359382280315518482490121334476533306185990189595078771172902829105508456952616332978182451059046332268236488364312721002263001953528906685707064146866170824260236878469883888574496579390632703190086213016822203014988297246988552, 
    3957316620106304986593311820918825768331474619161198352934768992404644119681652957342703752295506418225560697734893472186900809010331893527713115634455680620167324352919862855, 3957287367290623191565779142076835871100275577086034096759580983630358026942147873426733313853665863834293534521592480683983591869107542208299343420952661162447357494576511559, 3957287367290623150376993181293177581232129621775134213640547544622941715674683641855468391396737237472716147772493884366643837143062828083511816114053315980876295000001837639]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249041208049049249008249209a41009261a41a4820124824824800100004802920004000120100020800026804104024db49041008249a4920000100d26d2400002092492482480403cda6d84d049448200049a0524d20020924810824900824920484104904d249000009a09a08204208268269248125109241008201261248200209248249040249069049208049209208200001000200a49000040009001008269a4920104100936d26080004134934902820104db69b40a2124c240000268149209008209a0420124124824812104124124924112420824826924812400024924c24d00004925864d300009a4934b260001b6164036c249acda4d82000924930936020934834d34c00026924da6900826da4d34da09249b69b60002269a83268041249049249000069a08249201049249249241249a69248000208040248000049048249200008241009240001a0124824822924924d020008201009200209a68249248000209040249008209a4924920cb48a28a209248, 105624520099905, 1161226155725248, 4173730716559838907521224156855810685737056856902172784545311953959516555008880659825660147390942183064862771431879823203547171173685881144870086474713058639893111255156619847, 316936919720257, 1962460461133904581106957493229739927852546993902125008682957726876891679551987603384016381118248908026741802662286742022715614034815490511057936514801802008172690434010694, 1962460461133904581120051055661515031743141500262487259755672592434767288375416216805801822828789154078951514001101357273225380734255155832899442754905135128158421269196358, 
    106105088837697]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a24900000800526820100020000020900da0904c008240008000009200308260a09841200040000041301b4120000826036826100104c06d20c00020900da09029a6920000180000104c06d048049208240009809249201069241348000200448349000040049029249201069240201240000300241048040041008040049b4830820904d369240001300061248000201049a4904904c379b4d209a4d00186134836da61bcda6900526800800104814920024000000000824030824000104c06d04800024800e208000041301b4120824000900020004124030000000020a00c20980000004c00100100926030826000000006d048100040201b412012483000002c0249240041a41049200008001009240009001241349201e6d348041000248049041048061859209240009001240209b4124024820824124da4904134c379b4d300009841369241241001a6d34820826d04900920934800d369a4000024924824d00004925864920000924924b26000134164036c2492c9a49040009249209340001348041448000249249a69800000341001809249a89a60001249261288041249049a4900004d209b4920104004920924124927124820804120104000004d04c069b08200008040200001b0126026c24926da4d80004920904b2000012090c904000124824924800020824804902924934920000824120934000000100104c00024906828980004130100c009a4e26a24104030100828000004024024104100000c00100000c00130124166da4d26800024924824900004d04004920000924924b26000134104066c249ac9a49028001349a4126800034120026900004920d35930000924c20336126de4d3480, 1161157436117440, 28545062744643415571262815846320327822743197506, 387374385473857, 1161226155594176, 28545062744809609001729837519659450851429209922, 387099505469761, 
    1161234880008640, 2141060021566760805619948035611080667358320270466109414635935582067122313379131891727005723079529540, 105624528750657, 1161226155594176, 4173730716559838907521224156855810685737056856902172784545311953959516555008880659825660147390942183064862771431879823203547077637581091967083321438883764788556481238619093575, 316936919720257, 
    1962460461133904581106957493229739927852546993902125008682957726876891679551987603384016381118248908026741802662286742022671768985951966186996260481541669357882790527741510, 1962460461133904581120051055661515031743141500262487259755672592434767288375416216805801822828789154078951514001101357273181535685435868216537488721895241176834651230416454, 371084770341401239745653416226315238015823270722, 2928712635670479399483337775518561934056961890114, 176476053967296, 1461529513347638476386347103257350473108093666115, 
    106109457338816, 176476053967296]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x248800040000040049208008249201000001000201000200248248000000040040049208209a4920924100020d2412482082492482690000cda6984db4100106934104490820800000800420020024824824904104924900820000b260005a68208249248125108a20001000000000840000040049069a08209a49200000001000000a49041049349029241041b69a40a21945368000269368141a08209a49a0924104124924104820020924812524820824924812426db7806006c0090612c9b4da4100c379b59b4000000924f38b26030134db4d80036dbcdb6f3618cda6c36c301b0d86030db6c36dc6c02820830834d368269a4920934da00049a6d36800100024934da6904c36db6dbcc001b49b6db6d86db6d840001a68249248049041249249041241241249240209a69a6d800200069a69269208069a69b6d800249209a09a0924920804104024db4980820900824920104100936c200209a4124824836d249bcdb6184c30924db6d881801249a6920804134d24d30004000d34934d04124d341009241241024a69208249249209a69a4824924804124934db0004000924d34d04134d3cda49b6004d24d34d3412492410248, 316943093993920, 176063737500096, 457547304145344, 2928712635702382940195397476339526405876294374210, 176063737500096, 316943093993920, 
    736460179663825413032072919536632941031702156098, 457547572580800, 457547438363072, 316943093993920, 316943093993920, 371085815683523277197194658829026170708640682818, 
    1464361729723262950219676828343286315042191004482, 146239484596672]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a4800000c24804d40800004100824100030a2010000000000402480c000024804d20800000d209000000000048249800008248029a83000088200208000001068048a08208000009009261001009240200000200040200000048049008200008008009241041009241248200041a4820000104824906930800184d609205949200001b0920120904006c26804100800185120820100100a200a6d318000059b092c1001208201c70300301b68149218018059200a29c4c00006134024b040040249041208001859208000001001241848200001340249041040049048000041001241b4800024135824d20800864920824904c06000c00904d268061b48041269a4124800004db5905160000824b00a20000000d041a6824826a2480600000da36c01000c36db6030db6000020030000020924900824900824a46c04980824924120820104c21004004004934300000e34124d040001b8d00d00000184d0080482003610400080000cda6984130800004100b263000009ac12898c000024d80900800104d600200003369ac10098000c9a4100800c00004105824136930100020004926904920100020924028900000337986f308208289202800003071b01c6030db6d80c36d80100830180db0824924020924000186e400300209a4904820900000040000c00000124c30136006d861b6c36d841b60061b0db6000124d20924000c24d24824d00004124804920000004920924004164d24030026db6db0186db01863060001b61041248041248351349209041001341061219240200201000041208048001840008249a482c0060048209209801860201b4db0144004124926004000c36db6c31200000000900224000c00030c06020904024900800106da6c01320826100926024004024834040804100826804920124920104924104936824904907904907800c009861249b00300208249340249049269a4800800904020920020806180004161804920934c20036108024826000030820120984006c20804d30000184100820100000820000000000d0402410080003418092610002082c1b6c30006104024d308001041e0000000920024804d34804125104d30804920180134000924124004124100000020004924000c20000924d009040001249200000200000248009201b6000104030134c20124804024920804930920824d20005904920a349840241b08001249a4124804000824900b24000104da01868249a09a48000041008601818209a6d360209a400002000000082492490082490c9a69241209a41049241049209241249369048249049249268008009041249a00208251479b4900c009b6db6c061b6c0618c180c05104920524924824124834904124824904924da4120924020924920926020004124804920824924924020024d369b0104d20d8630603013412492480412482492492090492080, 80268786536896, 80268786536896, 97053213332550399493218394849395384036026749763, 532345381924043839394587228560890267803219799951076824376393939687286849720736025968505713119697531012, 961781914072982554326947800875174227090394140932011133272030275468811910536308172448335333523592454172955071982440930704509081254841316752344426293743398848013098025342028054288333346443958212815747208368938065040349936588664777691595851134999119428665213448245956552, 6788908546439210076729245246080569588370271574375095490805151853352107588362934943118204715555414584539392466394166566595898969755829397195355542337380363734020873110986665158955650146973690770988819731362690643258685016495239569606792831460403182436573159388312985162773005544829677399019815221758330097747010881572566825128799608447584957358748224461934449925756536343551144906, 
    990991763179976232357937877685350807161266908696318179930298669912388256378152414629410193643163016063093270640896441059847125725174720882023093042640252511496536137511246691416999381487336584683099528694905352581836708657292059792346183001317377107011043848245956552, 930128885513709663117093471514576619272731089636914613665743363781940069524210559287151115239584231556, 3965498569491706872499699489452407154688529658460578611213993368459437178933119504942303673154897302384945645392749073269841256964677815619353088220962820629812744677960448070, 961450161018512355988725026902066334706281316218122013853342406523312704098790716990024912293692080627718609497296472527265844840640183179869864001477271052799225541846190187853696592836300995486363813336148457884625442573414284775938117088311630055736345608749877512, 1038343202259883994768923266640158561829485373178150443628987548090679415780022582056566035270652996, 1038343202169246833807740543720626727587617300785395845812386675637128573527716547169091159230305348, 
    316936668324161, 1962460461133904581120051055661515031743141500265131503804660760558819597681332446183386008156141299122240077625885138765625658890580707419793889113809474227895208460594758, 3957316615499469982613701026949970206157261116843783760598096930747172428223431036261196785016095388258149956928433328915761504949033386054559597795422134095085876710338637382, 51381287167288566494271649909317494190049883715, 15015502880113495859264050485694884160399745310558569153899589077804510367438702592869274372590686649420915138280769756843317183941006074922258595944008813374469377338624089339070510778120126363114741605905587950973208829863566205831884129751391544750900232749869512, 291375019069888, 
    3020056487994356235900588060281961423347891835715, 316936668324161, 6810631865913720620457058171311035327782310330655124230545107782487930982815876812596032207241955313299405951392443768422799759867051915326862842544717428084863795959576735161331451364107256241083334877047148182954861523809340697244108981708750318208443281413724089965819282091083178412742577420712246526779967587674135944610720364865011453173238613586443907653587025152685670474, 5784956773199115103783776397074239025554492555712750831006393108340552546209451223893080456213065741080083993329247120105988450191318670616067603528768188541481633105098333783442468344263285171931604520636873062198589766896262866108275059017595255079852944524106561458492147984898625605672155809866325360728057774228303701914179277227691654235508435681523118718002026943635743161283895561213877950294913792846204869329038109500593916224632954639842596685975774549475234415836864373885039018406042140715149703446480036626875329986511866947128736102421874576058858491954176446967151807178323990951837008476550374852835532713800082456934156241564297359552824718414, 8369598326593329836429401746227057171012358197331087879978764043238928737177893702019844377047733125, 960984148772202939775489852405612533455804850080814786982979020217367351276564554763723209398747656978410764339688687061553686472018813116694321128237111292048616994319783040704098632002051836559083204444024562628438695920121377596688868969055061298215141897246988552, 
    284777949303232, 284780029743552, 284777949303232, 15015502880113495859263652749966112872573547049480687073144299086536775311389906829487199454272907587160906529483380360881785394496667674749541901955232587431907533841834040327108994011485866503016765013219500018689067153279661822761977846545808998434604040249877512, 365466006455704444305170270850659030476758471490, 365555209771630480104977683068793074137457251138, 
    365555209776780933718674877187124231354550604610, 365555209792773268890190957238013935489929794370, 291375019069888, 368231309409075616123813067281080257701199500098, 188398111017150392755177291222686647486502683203, 316936668324161, 
    316936668324161, 980281271336710796636931575029092713821678966986401862880592682920402834640318437778204167746857366728216577195917913299360789748676075100071364724103432094181823592205949718087592447877994163468922305270573375415216111406785957466092364142639347874710684168246988552, 316937205195073, 132875735960495930061876752971200258046912243841536599009219596024801506660145502076439467570959023300, 480481546266110744842554508686322220301213297080224476221576583989058135165810506710177553683086680337862520722595673550412548950691578128704148770727147213737639164253264264131484478553208810385470380663347414385102102212121047049359001681680363986584863752749869512, 247360593230090965501624659966305234041047830270056508149236969820521352927646154908216511104655243606314505825275888374417430603759596172034697266133872532506865035143065158, 
    731467232837867824773836406165920945243206767426, 129777547423926009027780781102568141247809614630750972816215814379959977636285776786036271754562948, 2076195733906855321610250751793454803913980796492993811941002800266376297353556591906568139194819012, 33218886717633724322929770282846208316897019609211577292832712416407294898690901696809532253276272132, 581659376751552, 1038216427127841050626293396355569673326158933651021827598302640312507228351327647994806827390994052, 
    365466006455704444305170270850659030476758471490, 480481546266110744842554101926582037516884295026952688057685822915922451476555041798932418578729115370555014336420357743572125930804867973184077134045225392741351259572840640029944724969043680722558461179519755554088356162248097288089348629017050018863907848249877512, 365376805856876505665456302565932502156251779906, 1461685619180623867224060064365498601014810448707]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492480000cda6004931800004b3082610003098012006000402c02480c0000240049300019b4b40920c00064d20c2498000cda4d849263000009b61044948208000049a0520820020926824904104d249048200009a48205268208269268125109249200001b6800120984106c26004920820db4d208241001809801249241041b69b61a41945bcc00038d8001292410412492410482002092081252482082692481242480002c0000029200008000001b6db01e71b00249a49acda618482092c9b6a0c1861249249208041a4924db41061849249a4820000d34926d240001a6924924834da49bcda6004924900824920106d24000d24020924020924802820100900300020924020924820804120006000820804920920926926b369800a0824926da61861849269a4820100924936c00080034d24934902c30924db69840841348041a49020001248249248049041249249041241241249240209a69a6d000200069a69a4820806de6db7180c269209208209a492082482c9800000028209200001061861a0120920804024924d241041049249248200009a49369240001a692492482482c9a49a4004924920824924920100000124124020820924924802db6c301b6f0c1a6820924924836db6d86db6d869a69a0924920106924934800080026924da4904d34b249268000a28b4d041049a4902092dbc300000e361241241000001341048040041049009208209a4920124000134d04104904104d3490492408, 366090429703239870199702515205918814333908833090, 1098268501511252861370602039401303312380238811970, 316943093993920, 11446249606038909791595293632431916925033984578, 22880651898655641884198941638312866693444032322, 316943093993920, 
    4217239420481885636213217601802303497115326521374029147114658860942937829314342847275797782536142981, 316943093993920, 457547304145344, 1962460704686820593779992290798329989834049757711014652977392115646431684129812504207018496129758145811134284098791754939300871892342785216809214445031903329977286704672326, 176063737500096, 64880609116516277184813734186923593362560480604678022488897823357108663795628167019326130175926724, 
    316943093993920, 176063737500096, 176476054360512, 1962460692040655099431226208491831903385485126292170185509679446260588540400350100683369653359495465822170418519465795807804209558056784623405270797795965084114116964429382, 736462602516499213080195003158479108488225149762, 365376805856886890259173372221194066765717459778, 
    146239484596672, 146239484596672, 91522607467016192538472520312248781562731057986, 146239484596672, 1461685619180623907788879271669994622239503356739, 123665318678276766716113370088301741753311484091595902776425324917401800048546041823665746994598276685745084181812074415429757505458639784305199320665164444690235727033970246, 
    365733616418933912545684089860058010822740300610, 366090429703239870199702515205918814333908833090, 366090429703239870199702515205918814333908833090, 537796105276741744684020501612001949339104881696594565793659786720081807489899613697586978278321857220]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a480000cda48049318000049308241000309a0120060004024c2480c000024804930001934930920c00064d20c2490000c9a49029243000009241049248208000048009208200201208249041040249048200008048009268208261268361b0c06db6184920594920000030920124840000124020904006c20805130000000000820100000820134c300001340240000000000009261000209a6000000006d040148200019b4120124934800027124024d06000026984130820984920924104100104104820020124824d860001b6d86124820827124824824904c06000c00904906026d208041269a4124800824db4d04d00000824a00b26020030d041860248269a480600cc6ce36e3da00c36c301b6d86308d8003cdb0c20920804924100824e36824980824820124904104c00008d00802934820104026836da4100005104c04905800c00900125930040020024924804100804924800800820924900924000000920024800000104824904920804100920924820904024824984100004100800800004104824136100d34c20004926904920100020924028800034d36c36c00820828920180100306db01b6030db0c06db6180000000000000824820124904000186f381b8c209208049241061e0001a36020104020904026800824104024104100000100100020904900104124124100000024104934001820820924900104000124920020020824924004104920020100820000804100124104124820030024820104020124024806004c00800830c301b0000c249a482600600cc36c3cc01800820928a002001801249b0040804124926004000834da4c04d000000049801a0020000034130020904020804900826a24c00800824104820124100c30c000008029041a6d24126820824924824900820924920924000104920124800000124824904b35934900800934986024920865940005934104924100924820904104024920824100004924100938c200041c5824826000036a20104800000104020984000c288040200001009b0824000000820134800004d45024c200001348309a4000026a26100000000020984134d04024920836180024964104d30180100d309a6c30124d04000964d20926000024924004100004124805930000024900924100124924030024926180924820924c00124d041349040249208240008308049209a6030124904024b36f06c3cde0c0012c9a41248000659a5904900000824b008260008209249800249a09a4800006dec0019ed8309a4c30124904360d80030db0c249208049241049241809a4820924820124904128c00036d30802924104c301241b6c60006036c24906030c049071cb1b8201b30db6db0c000001b7451986036c30c36c30006188204926000020920d3480000030c16c98006082080402000c10000412080002080000cc60186026d80820004020124906c00006d040241040000269040208001841009041000201b4100c00000104024900004926904904000124984126c00064d3482682100000410080, 75870740025792, 987180268735274236721164190570654642113553882096932472587493340292329456568739926872019955161832706010577600073590516391830707632160048426497882075540031063474585803662384418438363980157274735011197087356898937887837003457043571834290533364756535187007865352245956552, 6810605479372839473312678947313685515888999450940939642987787995526756837538343710895857923223530994946574148252278649910723035125030497535518938738908742523216390987522157255564012301566093795945653189513156577549667634380828982539092083129159423498280428508533947311137847834868913415602742370580757660267453617512269102732528564667225217567850858764754192232721594768705637322, 123695392679681251582055760644742948658005300172004416333658412149568600602428776360705829141086206777631794296168607029881183594369825231163129119366000409578288784031919686, 581395120223413659886868525050427510874316843019434707441899713608543722068787808368804439158768758916, 105624268965953, 
    105624537401409, 105624537401409, 105624537401409, 365733616418933912545684089860054633110134870850, 366090429708556802465251782349202214713877877570, 22881958551052760409978602157834375398577689410, 
    366090429719190666996350316635775770899026826050, 159433623736768, 146239484203456, 144040460947904, 146239484203456, 146239484203456, 
    146239484203456, 537796105276741744684020501612001949339104881696594565793659786720081817341735860740162242862926439108, 159433623736768, 105624268965953, 105624537401409, 581395120223413659886868621243258330693075244354193489877734265255405148105417089149582831220631498884, 
    581395120223413659886869390627426463909128703296509075172314841182015632995667887918699038224128635012, 589699837819074158287220465640199798039190773543900892484645411581795371308298060350388577047822954628, 566266213962688, 581659376751552, 261549947706041557390176538361675074190761867923720445898180746225538557692964671058852946911571589, 581659376751552, 
    37895173739116018876381519242215575713563167298866293257704974100558416907332609088622784439090613109959126044473285271598591266498444704678960060311799124623476790489882456264985193549889372617427956911486388019181155269910342876509121350861991691544495522894800830629431851393031502733661362970585439910608052264104885276811527403646180874158149836038654422126701851268824568798420587619699182526357107625934812398085269187200954576541631008832934614674421803768780802186291556582452925061546228415807308, 4217239466888111241578027001395728598050171987921162959811410130351327234467080501698969015634063492, 163849253295040, 229804448354752, 1962725818090091579651638347060604675358202756129981882174978147264245295070825826987194369241592217806597071581695540766731368302656885891152357237078387182028542457607750, 1932504634610075330541888326597019018174692574434342298315643794977988994244199696733782811690626758876920293851953191930159645084929868405333391360948965865847358441846342, 
    146239484203456, 97053213332550440058037602153891405243539788611, 97053213341854995463712805960877206770999628611, 97053213332550440058037602153891405243539788611, 97053213332550440058037602153891405243539788611, 4217239420481885636211459009447011757397331037038499409718394504232562167625650712101975570646319237, 
    15488341795068494133644489835076226072023621789523985468774741813217046803138248546360433364164626455615415769241154484030994273143548433157026459005997523007285952039398982, 15015789008703664364621442323710524463035778721684877943375810869140854992632250509065913257213580367565029486817663703436621944532231773879024425771242154091479256948629484532966926569514184518705489663781995379565086655735413748473090177597271921420944384496988553, 984031134860398729935032438333938181533334618187470085077173038011176967564846358823996060250939581600991362108177590201206189772174103375346686864890632031874923781336557315991666663278504605656532601034298593304183465210108712569716263008725927001940034568249877512, 188397414114210584911291741378516993596501014083, 316936668324161, 8369598326593387000979265560356319812834796094080789978614383980016580763289836275029659286869382021, 
    371089997073238265976211384383362794333501671235, 15015033881354251346468457295809488271381027041708212402232588244311368243913276078397597483212470435915314556538594539260218318327692114978880502376842915345720131955950099092503205137920375025365275323300759313547557173490526262203167814782323577271091456749868553, 33251310933491616332457798577226144844615965494142563324535519893935401826040348282831800031848124485, 316936668324161, 3957316615499754679502291219524629626874653578324212241901702282177686025862834024344906026180929133002406981213395449578057914662518438203260822076419712211119916679070527046, 316936668324161, 
    3963113421784280567019334247361027607891104697625748922885791126424424314030057337986473555277332392846794966228359189856920559762862823873813053504673019054730010289232719430, 1962460692040655099431226208491831903385485126292170185509679446260588540400350100683369653359495465822170418519465795813042231426513268528316679672093581250819539254816326, 316936668324161, 2076195733906855321612002474673359026728083102767198364344308971456243558107870186589764944138396100, 366090429703239870199702515205915436621303403330, 146239484203456, 
    146239484203456, 146239484203456, 1461685619180623907788879271669994622222323487555, 365733616418933912545684089860054633110134870850, 366090429703239870199702515205915436621303403330, 537796105276741744684020501612001949339104881696594565793659786720081817341735860740162242862926439108]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b10_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_3_0
  · exact tv_b10_3_1
  · exact tv_b10_3_2
  · exact tv_b10_3_3
  · exact tv_b10_3_4
  · exact tv_b10_3_5
  · exact tv_b10_3_6
  · exact tv_b10_3_7
  · exact tv_b10_3_8
  · exact tv_b10_3_9
  · exact tv_b10_3_10
  · exact tv_b10_3_11
  · exact tv_b10_3_12
  · exact tv_b10_3_13
  · exact tv_b10_3_14
  · exact tv_b10_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144a4935964920000924d24d2490002493cf24900002924930004925920920f309200001249040249608049249a69b69b0000926da69a6c208249249a00069ec920924820820324820514944da6944c30c25934927137130926d349a61801349b6d34c30824db69a4d20c209c6c311c6041014124924934d24904104db6db6db6db61249a6924c208249248249a4d36926000924d34924d300309351249b4d048269b6f26980004924100824106130c36db6e30006100d24804104802924924924104124924d24906034924924924904d34926926180534d249a4986024924924924100524924924904024d34934d00000800824804920400000120124810936d249a49b4824934d24934c31824d44926934d609a6dbca26000124904020904184030e36db8c06304d34920904100124924924900024d24934904104924d269249209249249249241349249a4906024924964930004d249269241809a49a5924c001349a6924906014924924924180924924d24c001124249a6934d26f0c836db6db6db0c06de79bd9bc300db6db6db6c303679e6f66c000249249249208049269a49a4180924924924820126da6936800000104124020d00004184d04120000000800824000000124000802924964d24964c30c25934925934d20924dbc9a6000124964c20904134c30f36dac806185834920104d201249249249249041049249249249241369e7934800024924904124924900006184100020924924124924012924104924924124920804924900820800804900400000020124824924100924800534d04024920824900004d34104510000000904924020804000c00800000034026900824934830020c36db6db6c300000001a0db4c30db6db6db0c00000006c36db0b0636d830db6c200069a63200008209201009a400018603cdb6c20824906026904124904024920824904104924904924100924920924820124924134d04024900824920804904104d24100924020924820124184104020820124814924100924820924820124d041124049349369b49b0000924d349241041349b6d26d248249b4d249249045149300009b4820924104924d241048000001248249b4d04924900514924da6d26c00014d26db49b49209145249860269208149269b09249204169b69b49b0000d369249241041b6db6d26d24834db4d349249049269c4934920000510000804000920100924124124030db6d26d24834c34d249249005a6da6d26c00016db6db49b4920d149a6d24924c208145861a69268248169b69b49249204149379c6db00009249a6db6c30c24944d249041069b69a49a00009a69a69268208249249200009a49208240208269248204949200009e4830924104924924124db6c06124834934d049249001069b0180930104d341249240341b6c26d24804934d049249069200048008005179b00059349609204248000201200109269b09b49208041a6c26c24c10d26db09b49208248209200208144670001659348144105129349a6934800824924926924120926f3692c0000a4934c20930d6482083cc26800004920920925920112524924da49000149249269249209a51a6945830c149249860249208109249209249204124a4924934d24b06182924482494924d269a49608205244909b6dccdb6c000249249a6d369ac00c1249b71b91b6c00020dc6dc6de00601249249249a6935830c24934824924926934da6b06184920db8db6db6db0904924926d269b4d60c40924d20924934d3483082a9269b49261a0db6db6db6db6136db6db6db6d849249249249241e6db6f66db6c249249249269069269ad9a0c200041049009b41800000240209040a4924924934d26b06184926904924924d269a5960c209249204921249249b4f34a00004926d36d25000134db7935000024f3ac001b6f4ac249000349c4900006180100000924c301249040149249249269a4d30c209249205145249a6d26800034d349249249049269a49a08209a69a69a69249248248000248268248200249209a09208124924149a4934920000524924d24900024db49249240008a69b4d24da0002920004104124120826920db6000104104c249008049249249241809249249261041249249249348249269b49a49025a6924924c208245308241069248204001248249248105249b6d35030814924924924d209249a4db69369a61349249b6c30826db6db49b4d208061b6d36d24814124934da4900024924d24984104924924924920924924924924124a249b6d24d248149124229229100049269248001049241261240001249a49248041269a49a4902524534510000c341369200209b6d35834800036d84da0900826db4966da0924db69a41041249a4904804124924984904924924924920924924924924124914912402524924924c00814924924924120926d249249000229a6d349368000a4800124904d04820824836d800049249209241201249249249000149249269249205a6d24924c20812914d041248249268109249269249204124a4926936da4da6902920926db69b69204824949245244909248a44920a4924924920c0492596db318209a69249a49241249b6da6d34824964da6924900024924101804935920000db6db6db6020934124d6c8049269a49a4180924b2db663041249b6da6d34834d28a459b6d04de7b3db6630c1a6965934c008379ecf6798c304d36dbcf6d98c184920004805920c31b00dbcf360040209001348209249269248301a49e6924c000269a4924926984924d34934300924b269241349b6d26c0002492492d98c1049269a59b0c20d349a69669a41b6db6db6d88036db6db79b6d86db6db6db6db0db6db6de71c6326934d2cf3c824db71b6db6db6130c361b604d180c36dc7b3cf3082cb24920824924920100005924934000820924824924000134924d0c02492492cd000079349e08001048000000240001ac9690308041208040001059b4d659208209249248040001e5924c04820824924920804104d24934320924b269240002249269008041249209809008289259b4d201049a69368241a6d24d6c8028949a0004934920524904024920820006184104120906124d24900800030f20820902924d36180924820000c308200000849261809248209241049249241249a6c24934824924904924900834934924000400124924924824522424820924924810524830d041348149269b0924d20924100d348208260009861040008200369a41041a0930db6c061248141249040249208249041349249049249209249209249241249241249041a69249208149124200049049249a0104124124924000124924924804124924924904524522510904104824920c04104904924d04924920924920924924924924124914912400034c24924900005864d34d20000d36b269a40001658249bc83cf249a4902912000100926926020834d34d348000041269a6900824d349b71a0d369a69a4082524820824d34814924920924d20800124904104824924926924120000c308208260a4934d04024920800030c208000021249040249208149249209249205041249a49268149249269249208009e79458048149248208249248124124a4904134d20820b02926926db09b69204824949200269a49209205244909240009209249a4020865934c4680002492492c900825964926f20924b2c9a40a449208, 1161221994844608, 1161221994844608, 1135246033031616, 1135246033031616, 1135246033031616, 106107236389057, 
    1135246033031616, 1135246033031616, 1130439757021889, 1139240486834624, 1134971155124672, 1134971155124672, 
    1161359433929152, 1161359433929152, 2928713681017909931566786873899211646775546893122, 317209381966272, 317209381966272, 246844728940737, 
    317209381966272, 317209381966272, 3957286453284098376038451321148240931959496092091848580117833555939956294793094855578250662849319524187174116480719513788198836047545677422041720846681272661864763929426284103, 1161166361858496, 1161157368943040, 1130439826215105, 
    1161359433798080, 1134971155124672, 1134971155124672, 1134971155124672, 1161157368943040, 1161166093160896, 
    1161157637575104, 176063733305537, 317076107964865, 176063733305537, 176063733305537, 1161157368943040, 
    2928713681012592999301237606755925994587174228802, 316934504059328, 1161359434715584, 1161359434715584, 72709640818881, 72709640818881, 
    74908664074433, 74908664074433, 583925464646046210032528848549142634165963574687313643932211154248300066469092686748599198157409796, 143078384996545, 143078384996545, 563500255547840, 
    581109621461952, 282025547272640, 282025547272640, 563500255547840, 427174101258688, 565701426287040, 
    563500255547840, 567902597026240, 176476050690241, 143490701856961, 572021202227648, 583925464646046210033188320692203937169199032612393893443549540359684594159696503221438210193788420, 
    90575098211533486264477223487511349508520508283931030681254463423603578956287863878594014764253704796557724531153587550556146974223892500802999431653036526405073985777222, 513258889781001788508752372384011230216198211446080363634990166979188729044093013380941140376675049326145827188858423582703147710042805591794375891410248417132548909382214, 583925464646046210033188320692203937169199032612393893443549540359684594159696503225715198756687364, 583925464646046267658742618891931016445229715976052867333303189001030256292315590935517959322897924, 143497685373376, 150092607656384, 
    145698856112576, 163308222026688, 150092607656384, 150092607656384, 284226718011840, 284226718011840, 
    282025547272640, 308439596143552, 290830230229440, 290830230229440, 308439596143552, 282025547272640, 
    290830230229440, 290830230229440, 284226718011840, 284226718011840, 282025547272640, 286427888751040, 
    308439596143552, 290830230229440, 290830230229440, 308439596143552, 282025547272640, 563500255547840, 
    565701426287040, 563500255547840, 567902597026240, 581109621461952, 572304938504640, 572304938504640, 
    176476049707201, 176476049772737, 176476049772737, 176476049772737, 299342318539200, 1461551814199009254797950837232658299739999065922, 
    563500255547840, 567902597026240, 581109621461952, 572304938504640, 572304938504640, 1130719271719360, 
    1130719271719360, 581659376751552, 581659376751552, 290555083887040, 290555083887040, 145273251697088, 
    145273251697088, 4535763341760, 145273251697088, 145273251697088, 145273251697088, 145273251697088, 
    158485107971008, 286010740052416, 286010740052416, 286010740052416, 33284385084494712632638531821882354590088529999742802665149313087092048640171546857277812645524290949, 424557929304512, 
    33219377757385355898275814330050409486995068037841236248948427487257491011279415213503482774457026949, 286010740052416, 18159668040640, 576290533937600, 286010740052416, 576290533937600, 
    73676011672000, 565703582171713, 73676011672000, 426748228407744, 290545957081536, 150642228859328, 
    150642228859328, 572854693794240, 91279338312640, 163849253295040, 581659376751552, 163849253295040, 
    290555083887040, 583925458845267951737113164577006047042602439525695413977381248462280187782765464490526278252263301, 74909079308353, 17127037646853419605659315719223550270863835971, 105626693011521, 105626684885057, 
    105626693011521, 105626684885057, 149808737161664, 149808737161664, 73669972332992, 143078800233153, 
    143628560257729, 73669972332992, 9071248806336, 290417242280384, 290829961793984, 290417242280384, 
    290829961793984, 286148179005888, 290546225516992, 290546225516992, 299342318539200, 299342318539200, 
    290546225516992, 143628560257729, 143628560257729, 286148179005888, 290546225516992, 290546225516992, 
    299342318539200, 143628560257729, 143628560257729, 290546225516992, 290546225516992, 33218933866359174949876067095137005966473614880526735990574261584280175203012984685081586211003600261, 
    9071248806336, 431081649082816, 431081649082816, 290546225516992, 290829961793984, 132875485490565941905506620202759736912914288813742658394879708828169078294623432373004100487553802692, 
    581659376751552, 581659376358336, 73671649595840, 565703582171713, 73671649595840, 290546225516992, 
    290546225516992, 290546225516992, 290546225516992]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24900004924104920804924820924100020924124820024924800024934da01008249249208201069a6d6c9241209a692492480003cda6da0904924820000926820000c368660000849300009a48205248200249248100009a08249a0420826924924804104d24904902516a208049249204909240001249040a4904004924902000924d648040841a6934da49008269a4920820104d349a69a40a38a2134c00028db0c14920c009b49204001a68248008108269a49209a0104d34924124020826924824812512400024824d30d00004004db79b0000924b36da6000104034dc0c2c9a6da49020009209b6c34020834936db6800024924dc6900824924936da09249a49a40000260209268041049249249000009a69249201041249249241a6924924800004034934d00820924920920000104d259240208249249248249249249024a248, 106107236389057, 1161367822537152, 176476049903809, 28545062765744990579237307101155715941027305282, 960962612318422722514276120579029485995887052264404733803492738587652128064625435033862841978854379236664378699397460550450053680800963383633787881044931947600576279073921730403133446905479277806618024208296383887324145763555203294709579708451470394177618952249877512, 1134838011138497, 
    1128240733766209, 1130439826215105, 1134838011138497, 1134838011138497]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a08001049205248000001248000209b09a0900034934134120106926c26826120904d86d048000209a0820982000c36820006124d30000824820000c368260000849200008048209241009209241248000001248249000048249000049269b4180104924924124020d64da6d24824134d249049000079b4d60130924930000d249208a05a6830040206814920000806120000826c20824000d86d04c000041a49b09a0980c3493613413010092682082c080030da08002000061b41000308001868008008108261a41200200a4904004834902924000100924000164db4c04004124924904d00834937930d30904924d341240001249348248200079b4d601b09208269a4920920800024824c20d00004c04104d200009a48388240001800041b6c269a49a4980000804d67930000b00e30334000020964db4c00020804c399079b4d65930000920934834000034134d34800026924e20900000181936db09269a69ac000124126d06000024024004100004d249b4d30000c00120124124934924800024824d26900001924930da00009a4936b240000368349bc8249ac9a49000008049249201041249249240000209249248041049249249049249249200001009b69a6000044db6dc78000041a6e28b00004d30db7a30db6a26db6000124136934c04104924d24d00004d249a6920104134924d2412492492481450, 1128670505341888, 106107236389057, 1128670505341888, 1161226289811904, 1135263212901312, 106107236389057, 
    1135263212901312, 1161155422851520, 1130865165996992, 1161164080026048, 1161235014095296, 1161368023863744, 
    123695392520532176087520368668498964167765860521866567404282814782946282688101452997004289403734589490615705948029570896972914070892963701148080145374448823734767573880057414, 106107236321345, 15121341268955300454560687058317760675804896124643772855640321490097963233144917338838306941178170005223793357217524085409586083207107847802964867881091127199157114436564199219266113689471987383838337811969881927592931049267197245621000337872564223215128496956552, 30946491887137527512635394397712577111473074314849674795086644395861206193840131426362096455553043426810858305986210358781743338894500053098941582553159740249957277906546246, 106107236321345, 106107236321345, 
    1139244781801920, 1134979745059264, 1134838011138496, 1134979745059264, 1130439757021889, 1139244781801920, 
    1134979745059264, 1134979745059264]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249000049241049208049249209a41001200201a48200249248041a4934da40041049249208200009a6d4c1240001a692492482483cda6e04004924900004d24102924000300804124800024920804940004924820524c201249268100049209209a0420924924826804134d249049025169a080492492049092400012c90c1248201249a4824904004936904920800924920106924d44900080026934d849001069a4920820820d349b61840a2b2c300001b2c0a4904004db6902124c000249a48149208009249204001240249248121041249241240209a6924824812512400024824020d000048049269a00008249001240001a00249248249249229820009209048340208249249a68000209240049008209a49249208a48a28a20001a60248268041049249249000069a49209a01041249249241a69249248124a288, 22858351068388466800296415174393955260722860866, 22880651898657589153672566758510255480170894146, 22880651898657589153672566758510255480170894146, 23549676806731259754957114281999262063611892546, 24263303375343175062993964973720869093465150274, 25690556512567005679067666357164083146729214786, 
    2076195246641484044976885370241558467496539062731451265407867139338675772718944592366580374412779972, 259649206675262503700158378804345852033651807665281829674453551065767536865166065331778536107071940, 3957286438548131188546637175438305938039366142412183245213188893831077710837500379500010852624858682321754102322109989925265940342048335877163803107797415324067170422921408070, 176063733305537, 316801360073153]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a20004934930526800024920c000209a0820900004124104130106926820826100104924900c000209a0820902924d30000924820000c36820000084920000924820924100924924134820024904034904004924900834924924000820924924904000124d24d24800024924934904932924100924924024800134d24824904024d24900526800104134814920000d34c200008268208241041a49a0820980004134104130100926820826000104904000020004124104180930c30006124814124800024920824904024d24904920800104920924100124924124d64d34d20020824924d24104104935964c30000924924d24124124934d00024d249348049249000069a4934820924100124924000024824d20d00004c04934d200009249b6824000134034db6c269a49a49000049049249b0000900904124000124924d24800024804904904924932920000920934834000004124d34800024924da8980004100d36c309269a6926104000824900000024024104104100800104920000d00124124124924d24800024824924900004004924d00000924b269a4000104034db002c9249a4982914000100926926000130134d348000041269a6980004d009b71a09a492692610, 1161368023863744, 246844728940737, 316801360073152, 316801360073152, 316943093993920]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨1, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924920c049279bdb31820a269249a49241249b6da6db4824934d24924900024924101804935920000db6db6db6000134124d6c8049249a49a4180924b27b66304134d271a6d34844d46db51c6904965b25b6c3041b6964d24c00024d34959986104924d389ed188104926004805920831b009acf240041a0100124c000268049ac1009249249248301a4964d24c000289a4924926984924d34934300924b269241349b6d26c0002492d9ad98c104d269b49b0830d34de6936da4134d26d249a6d04d34db4936da4336f3cdbcf3cc34d34db6926e44120c3403602cd0082db34b6db20000d80136f2402c9249a0824924920100005924935820820924824924000134924d0c82492492cd000079349e08000000309a0b040001ad968c20c000208648201059449659208209249248040001e4d24c04020824924920804104d34934300924b269240001b4d26d0080000490682c1000069b4a249300000249000241249b496480, 1161155221459392, 17127081203036625782721933749296776542920127042, 1161368023732672, 1134979745059264, 1134979745059264, 1161155221459392, 
    1161159650709952, 1161164080026048, 266594411932911499093404785498504934513857636213620729964618737285307635395699175925094352864345813124, 176063733305537, 176063733305537, 317076107964865, 
    583925458845267980548559480583713391177709692934585104808384948649770533268701457091893565351751812, 176063733305537, 176063733305537, 1161155221459392, 2928713681012603383934568757668315224376604644162, 583925458845267980550099590646493615935118350449752165953708187346557897945778862245358505645273220, 
    316943093993920, 1161368024650176, 17127037657320805558879493943852041607915263810, 72709640818881, 2923049270129584007669778485813772244746191820610, 72709640818881, 
    74908664074433, 74908664074433, 79306710585537, 74908664074433, 79306710585537, 28545062755111125968913028733031741550938314562, 
    143078384996545, 143078384996545, 581109621461952, 563517435417536, 581109621461952, 581109621461952, 
    563517435417536, 565716458673088, 581109621461952, 567915481928640, 563517435417536, 572313528439744, 
    176476050690241, 143490701856961, 572029792162240, 17127037667954670169206191334983493936910194498, 28545062765744990579239726124163193879933245250, 90575098211533486264477223487511349508520508199315852281441596616471538763068820963668238353141956975964110557804250150811533906023262970393798465539161018994663621701190, 
    90575098211533486264477223487511349508520510822385939970090217222108681814802512305488324595156352461303402684780188257797579364676242699224771599909390430752233141481030, 28545062765744990579239726124163193879933245250, 28545062765744990579239726124163193879933245250, 145707446047680, 163299632092096, 308439596143552, 
    853797363520448, 284250340332480, 286449363588032, 308439596143552, 286449363588032, 308439596143552, 
    290847410099136, 308439596143552, 308439596143552, 565716458673088, 581109621461952, 567915481928640, 
    581109621461952, 572313528439744, 176476049707201, 176476049772737, 176476049772737, 176476049772737, 
    1461551814199050144291692243950190892035881391938, 581109621461952, 567915481928640, 581109621461952, 572313528439744]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249249200049249249a08209249269240201249a69a48248269a4924db00049a69a69a00009a69249b6c000ac9b4d24d3000cdb69a6b20000db6926936800134e26a26900020000104d241008208048249201200000000201248200248248049349a49a40005249269248248169a49249208204a25100009a08249a04248269248248109249a49268000a49249249049029249a49b622c0a4926924d869069a69a69a0820924db69361a40b4da6924d84902800000000904084904004904902134dc4da8d80014926d249b09205a69a4da49a48149125124229224800001b410400000c9a4924820000d801001040001a4924924834d35964d0248, 1161368023863744, 1161368023863744, 316943093993920, 79306848997824, 286156768940480, 286156768940480, 
    581109353026496]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a4934db0020524934d36904826a24924d20004db49249a40009249249348000a69a4924d20002db6db6db6c00165124926900020004900004120820920db60001208000001048049249349b4000924924926104124934da7924824936d249249069b4936db00008a49341001009b4820104124926924024c341a7924824936d249249005a69b69c6c30814924d249b6d209249249b6a241b4924926db5824924924da8904d349249b4d30924924936a240b6db6db6db8e079c6db6db71e0836db6966c308109269279b0c200a4944934984102924d249349241b6db71b4d860649b69b6d24da4826d04104935324904924124934924024924b1450, 1161226290729408, 1128670504817600, 1135263213425600, 143362125468096, 143362125468096, 75192404545984, 
    567773613789632, 79306848997824, 1135263212508096, 172104583484352, 568341086344128]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249249208049249249208209a49249269a41a4924924924824924924da08029249249368201269a69a6800024904124824d24904100824924920000db69349240001a69249248049449a49a0000524d269248208169a49249208204a25100009a08209204208269248248109249269268201249a69248208249249249269049269a49249209a69a49349a40a4926924da69048a2104d30936924080024924924902124da49a68000149269269a08205a6d249249248129125124229124800001040248000049a49248200000001009240001a69249248229249249020000041009200209a49248248000000040249008269a49249208a48a28a208]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a249349b0000526924d269000269a4924d20004db49249a40009249249348000a69a4924d20002db8db6db6c00134d24926900020004100004120826920db60001040000201008049249249b4180924924926104134934d26d448349349251a49029249249261041a6d249b6c00024924964f041049308240069b49a0820900926924000130006124800030c04924900526934934800014924d24db4000924924a389241c51249471b4c24924924e26904d34924db49209249249389a6124d249b6c20c36db6db8e36d84da4924db4930806134936d24814124936da6d00024925925984104924db69b492092496493692416596d9249e4904d36db6d36200925164936d242289b4d24da4826d208240351a4900826d249369200009001349240249229100049a69b4800000124906904000136da6924800030d249049029249349200000041009200001b7124804800000004026980006da4d261a0924db69261041269a6d008000049341a4104104f369a4920000124934124126926d2480, 1135112893247937, 282042190271424, 283816011764161, 282042190271424, 290838283293632, 290838283293632, 
    299634376315840, 308430469338048, 563517435417536, 581109621461952, 563517435417536, 286440236782528, 
    299634376315840]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 0, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x248a6924934da00049249249208209269a6d3c1261269a692482482693cda6980004924d00004d241049208049249201200000001241248200249248044969a69a6a240005a69a6924924824944d24904102516a200009a48204248200249248108a29a4924db48000a49a6934d849069a69a4920820924d349a61840a29640001349040849040049349021945369a69368000149a69a49a0820924d349241041249a692482081251242492c9a6db6db6db6c60236db6db6dc6c061249a4d3cd861b58540079b0000924b361a6000134d841e6c029a69b4936c308269a4924936da09249b6db6db6db6d84004920830db6180024924d869041a69a69b6d00024924924904104924d249249241a69289a89a49249208209a61801268200069a69209208269249249208209a69a4924924824924d34d34924924104124030024904000924d049241024a49800075e61849260001b69041249a49a4924820804134d2490410492490248, 732180859438381333674704630431738142616482534210, 105624528556480, 316943362036160, 105624528556480, 387108095398336, 28545062744809608924977555083965873807683508034, 
    283815873351873, 316943362953664, 732180859438381333674704630431738142616482534210, 290555083887040, 712642994901952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 0, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a492c9a4980004d44934d30020924926a28186124964d66d048249ac9a4b000029b6de6de6c00024d30804005920820f369a00001208200041648048a69249249b40009269249261041a4d34d26d24824936d24984906934934d60c30936db6db6d86184920000924820924100926924024020004124824926c049a49005949249a69260001249249a6986184d34935130c3092c92692c2080a6d379b59b00009c71b69b70308149279a59318200a29c4d64d34c00024b24924984104924935140c309249a49361241b4924935800024db6db6db61861249040349a49041269a4900820924180136924024934d269b69b4c269a49249249269049a49249269a6134da7336c41804124924026d84104db4d34d200008249809a40000001841b6c04934f36e38004124d34db8d80104d34d34d30000924924d34c000269ac9a6980004934934d60c30b26f369ac0001289ac9a4d80004920934d34d34c30824d36939936db09269249249249a41a69a49249a6908d469ccdb0c301049249009b61800209240269071c0f099e9040134d24926d00036db6db6d86184db6f36db6db6124934d24924934835134924935130d34d37936104030d24920126820c24924c24900004124804d30000004920d24024d24d24930000a349c49b4d8c0249a49249249249079e6dbd9e6e309a69249269a41e6e38f36c30c00124924024d84000824900824104924924924104124936924924904924946db6de59061849249208049209041248201248209249a6db69a60001269b4e26988204d36db4d4000092cd36a2c1861b6db6d44c30c24d369b59b10309a4124924924da4834d34924d04104d369b4926db0935a24924124124934d249249b4c24924924936920db6db793418600012410012682000412480092081450, 145277546664384, 145702748427200, 145277546664384, 145277546664384, 581109621461952, 145277546664384, 
    145277546664384, 145277546664384, 158472223068608, 145277546664384, 145277546664384, 145277546664384, 
    158472223068608, 158472223068608, 143628560257729, 294819852194240, 290847410099136, 145206679704000, 
    145206679704000, 145206679704000, 435557340549568, 145702748427200, 286156768940480, 286023759172032, 
    286156768940480, 286449363588032, 294819852194240, 290554815451584, 299351445344704, 424562224271808, 
    435557340549568, 576294828904896, 572313796875200, 572029792162240, 129777547423926009027780781102565142315753786178973515911885283130728663145684658919350936839179652, 424562224271808, 
    424699663225280, 426761247527360, 286156768940480, 435557340549568, 581109621461952, 576294828904896, 
    22858351068388466800310922339569351924910150466, 565703582171713, 22880651898657589153687073923685652144358183746, 426761247527360, 286156768940480, 435557340549568, 
    290554815451584, 431159294038464, 290554815451584, 290554815451584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 1, false⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249ac9a6d80004935934b300009269269bc186126d64d24d000249ac9a4d80004924940004b45920920f36980000124c00024d608044949a4924b20000526924926820824934d249041025149a0004b2c920526820126b248109249269a69b60001249a4926d86184924924d30c209249249b6186124926000d34db61a41945bcdb6db8c000129259249241041249a6924820812526800128a268124229a4924924924920820926d34d260001a6924924820804124924d249061849248249200009a49060200001a69248248029a69249248208249269a49209208a48a4934d349841020049208009240800249249049021a89a6934c00024924924904104924d249241241a692492c9a49208209209a60003248240069a4828920812d34d34924d34000134da4934d041069269a4920820924d34000134924104d04004d249040a2db6000b209241a48201249248041249341a49840049248249200009a6d0c0200001a69248248341bcda6024984920804924920934000d26d34124820124924824902000c34b00824024820124924820920800924920104924c009260800269341849061869a4820920c20d349869a40849040349b4d028a208, 123695392671695679596741587065254242806862682383296486115391462691264081170442092437765086705249606004201385905646747166704124603554418992362868810780472616589563364581355078, 371089997073248001570191453004804659981905318722, 51386513902451585926615030049402227701592382274, 1978643226843600527308614323863389164844584279914989389625026667235688865996128023422812997675478192583287505487787326630681670117618239710428701054855516923521694010931719750, 33283751484824631724446425728741345977411954196981884002069236177180055163219620215710468591796318340, 290555083887040, 
    572313528439744, 581109621461952, 1461507215282038483043462627483940235585897190210, 1464361718834227208908102322543829804221099758402, 1464361718834227208908102322543829804221099758402, 581109621461952, 
    22858351068386519689279115082720808413289273154, 1461529513368741998433686316367436668615880934211, 22880651898655642042655266666837108632737306434, 22880651898655642042655266666837108632737306434, 290555083887040, 290555083887040, 
    712642994901952, 290555083887040, 290555083887040, 290555083887040]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a492c9a49800049359249300009249269a6186124d64924d0002492c9a4900002924930004935920920f36920000124c00024d608049249a69a49b00009269a6926c20824934d249841049249a00049ec9209268201203248205949249a69260001249c6d24c000249249a6a00005134d351b00009269269a6180134d34934c00024db4d24d200009b71c6db6000014124934924d24c00024d36da6980004934924930820924924d36104124924924c20824924824934926d269860269a4924924920c049a4926924830124db8d36800004124924026d84124db4904d200008249809a40000002041b6802934924d24906036da4d34d000049249249249241009249249249040249b6da6900000804924804920820924920924000104920124800000124824900934934d24800024d36d34d261809269249249248301a69249a4920c06de6db6da00001049249009b4100020924028806db0180db6000134d24924900024924924d84104924d249249209251b4926d241249349249249060249269a49241809a6db69a4800120824904024904004920804920000024900924024b36f36dbcf0cc2c9249249249208049249a49a4180924924924820126db6d3680000012492402cd00065904905920000824b008240008209b40648029249a6eb69a60001249c6d64c000269b4daca06184da79b4934000924e369a6000124924800104d44c30f38da6800005920000935030134d36d34d34c00024d249269800049a4935130c309349249a6800126d64d348000249241000269a49001b61b41000009340001a6904012920824920804900820924920924000104c20124800000124834904920000924800944000024920824d00006926184920000c369049240001801301b4800030db402698018d800c36db0806360c30db6c24b04324830da4c20006db43200008209261009a4004166c301b4820824906024980004124806da0124800024920824920000104920924d64c00124000824904024104184930004d30000824100d241269248301248249200009248209240001a49861241069a490492080, 583925464646046181219642020544493836866945337416872723235679389603658296578379015221037712270389380, 582173687498006831640714275609924194970788483707286492939578585283517330495694694397486063496778182788, 74909079308353, 105626693011521, 105626684885057, 581395120223413659886868621243258330693075244360103100979669289345665139133758812578188305421139406980, 
    17127037652171710163778038942639645362680517443, 583925464646046181221292185132233903301347068088414544210366560472453921190308570360451239419344005, 583925464646046181221292185132233903301347068088458937315323888519253147049200311216636146658866309, 149817327096256, 11440325970595550242135845588452746147670283074, 143628560257729, 
    290554815451584, 431150435668416, 431150435668416, 2928712330767093355636065619780760113681614778946, 123695392678893941668010701277751104419160586077851355394805759816521724352149048184693294972524940961851639783600752724593041214953110249388869493712114461495318207750516294, 532345381924043839394585471685884124357262325992706243530575145932913892559999819714316286474834899076, 
    532345381924043839394585471685884124357262325993153726104560325759068133198383730055504959236805456004, 532345381924043839394585471685884124357262325995608487646776129219794154060405258043278604239520362628, 532475143136476034682092729134973136747705552886761781512049685724019501218805782687531698895780540548, 581395120223413659886868621243258330693075244360103100979669289345665157182924867760241879180442300548, 143628560257729, 143628560257729, 
    581109621461952, 581109621461952, 581109621461952, 439955387060672, 132875485490565941905506620256427718104988142541047592954575904192173592505439619621787516026681024964, 1464361718834227208908102322543829804221099758402, 
    1464361718834227208908102322543825441342317744962, 22858351068386519688974464614033045217561564994, 565703582171713, 22880651898655642042350616198149345437009598274, 290554815451584, 290554815451584, 
    290554815451584, 290554815451584]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b10_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨1, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_7_0
  · exact tv_b10_7_1
  · exact tv_b10_7_2
  · exact tv_b10_7_3
  · exact tv_b10_7_4
  · exact tv_b10_7_5
  · exact tv_b10_7_6
  · exact tv_b10_7_7
  · exact tv_b10_7_8
  · exact tv_b10_7_9
  · exact tv_b10_7_10
  · exact tv_b10_7_11
  · exact tv_b10_7_12
  · exact tv_b10_7_13
  · exact tv_b10_7_14
  · exact tv_b10_7_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144a2924924925920000924d2496480402482482c9800049349200019209209249040648049249249a69ec9b0000926924f26c208249349b49049048208000009209249a6c20c248205149249248209209a02001c7134930040814920804c01820124924924924d36d241241049241a6020824812524924924924924904104924924924124124d04104800024924904104906db6db6db0180924924924124012924924924104124924924924904924924924180534924924906026924934900c04534924924906064934d349000008249048249a0400104920124810938d24924835824924935924934c31824d34924d20d608249a0da0000104124800c04030db6db6d86f05834924120100124924924900024924934904104924924926920924924924924124924934900004914924924924180924924d24820000124120926812424800806004d20820904c20d00820924924920000824904824d20824924924800106d049a4c0002cdb1806c3ce30824d34d24800300da6826900004124824126900004d24d84d200008249049a40000001a41368029249241009241249249248049049249241009a0534d249040268269a4900804d008249048049a0400104920024804134d00004904f30805804920510924924830124134da6800134c269a6924c06904d24924180d309b6db6d86036c24936db6db0c00d84830100f0ca28106134db01b6824180806c06da0124924904026824924904024904924924900920924924920124124924930804d049149249241001a09249240201241040201201248124049345149349349b0000924924d341041249249248248249b4da49049049049000009a09249241041241349349208040249b4da4904900514914924924926c000149249249209205241240000268149249249209204149649249249a49a00009a6d26d268208208049a00009209a4d26c208248204949249649b4000924924924104124d34926924834934da49249069249349300005179b59649600009201041009a4820104124924924004104926924804934da49249005a6d24d26d00016db4d249b49209a6924d24c208149e79649358008145861248269268169b4924924920410804900000800100924104924000104920804004034da49049008049300049305100041008008001041241349240201249249a4804134da49249000001019b49309205a4924c00026c169249249b09209a4924c20d24814804124826c26810924924926920400004c66d248144105128a4934924965800824924924920120920920b20000134c26000064824924924921920112514924924924c000149249249209208209241000268169249249209204124a49229209249248060044824949245241249249008204905249249249049249340300348124a4924924920924936806180db6db6db0db09049249249261249261000209208209048048008209249309240208249248249241249249249209049249249241208209a6220f36c24934db492090c9269b61a00201049209049a403cc301b6db8c00020924026904092124934b3adb6f378000249349b4f000049a6924d260201041051878000241349800049099ed9b0c301809249248201240149249249241249361b0020920514892504926b260000000041041049041249b69a08208009a6d24924824800da7334d0c0268000268269248200209b69249208124125149a4934930000524924924d04022924d249249241008a09a4924d20800004104100120826926934820100124904c008049249249241809249249241041249249248348249249249049045225a69249248208208049241049a0400124924824810524934936c30814924924924d20924934d34926934c248249249369a6006124d36c308109249249b4d20124924924c00024934924d04104924924924920924924924924124914824924d24d24812412512920824924d20900004924d34000820924934824000124926d04024924926900004924920800104124924124000124924b248041249249249045225245108209269348240001a6934c34c20826924da0904104934da4d309a49349a61041249249068041049249049049249249249209249249249241249149124025249249248008149249249241208a49349249249040228269249248200001249048048209a49a4d208049249249201201249249248000149249249209205149249249248208128001249248268109249249209204124a4922920924924926900926db69b69204824949245244905124a4820924924824000124d24930820824924920900004924924d209249249a40920949a0800004920524924100024822800104d04d04c20004124124120104924c268261041249049008000208209a0904c349040009209a69208001240849249040009a0924924100924124904920034824900024804904904935934000504124934930820c24936d26100824924924000400124924924800834964d241025a4820020124810524904830004814924124800120800d24904d058248041049208040041249309a080400092482482c000104906800810824924124120124924100026824904004024904924124800920924824900124120824934924104914104926d24c20020924d249041041249249208124124001249241268041049049249000049249249201049249249241249249248100049249049a0104124124924000124924924804124924924904524522510000924920804000134c34db6c00024924926800004d37930db09249a69ac104124100806004104984924904924124800920924924934924124914912400024924824900004d25804d20000924924b2400000012403682492c9249028825249a4800134814924924920d208a480082490410482412492492412000002082c824130d249040248269a4920c049021249249040268149249249209205149041249248268149249249209208201a48209248124124a4922900104920820b06926db69b09204824949245200269249209204905124a400092492092402090480400080002492492c900824120924020924b2c9a409208, 1161359299580352, 1161359299580352, 105630964713537, 3957286427485527111805477507569384677388243018328455666079766738251596518336578620495032736071012614513715620139643542658555203000134667771807297350003511796663589802405231175, 3957286424721394476491768881696603703764903845916415270785722545237327847286408454184998575484682840409691404443257343987046119318483121873060261906697835663519351648858582599, 1161230450561472, 
    105630964713537, 4217239420481885636211459244034785128008435974957801383675895482957318402716536464819957321136566404, 1161165959205312, 1130861139726784, 3957286427485527111805477507569384677388243018328455665837680812180948838056472901290049311097875977803968598157271522375025248909109301658137492610278919365824122660530911815, 3957301523335226397970886499367316251753047029954145032524126202245200438130444064716486586767383210819819193297390412072331197269727497266838601003162222900714226198920519239, 
    176068032467392, 176068032467392, 532345381924043839394587252627284302906700368276091089244433314792401844646009287474446127971943280772, 72713935786177, 143082679963841, 143632855225025, 
    871389817213888, 871389817738176, 871389817476032, 871389817476032, 551485156945714612346253472188418277530366474055436674970173038161088733259501335865536846861758533, 145698319241664, 
    726257638577088, 581109621461952, 581109621461952, 532345381924043839394587245754428666273818154591183782513016689868243853581338255640839237463870500996, 551485156945714612344052655694372894586506322881252114208931317795003209432943126521811583137542213, 106111548065857, 
    72714878521792, 72714878521792, 565707877139009, 145410556432832, 145410556432832, 1135254488355264, 
    1130860736811456, 150092607656384, 282025547272640, 563500255547840, 563500255547840, 163308222026688, 
    308439596143552, 308439596143552, 581109621461952, 308439596143552, 581110158332864, 16674316046003773019189936114363085810836845717216220097143622214992470538512594340472631036924191172, 
    106111548065857, 106111548065857, 106112017827905, 551485156945714612344052655687821627595199460505514859162362310038991476018799406993431726509846597, 106111548065857, 28545062765749533700341516866965586403964487491, 
    537795352846196041671507583681419323271693062571789364692860480157454761173268711321004055397020168324, 4152989022987072960328209257074960466135974817092101661374951751740783349279601498084908630481833177109231262750953888317699477692061222081005651580576256358152041889192212550, 7729078731994588773169520666294999833543339133274738177802784375286565296603294473452008666805128475254611150799584987649230448709988073188065654462883966493956449201258055, 426692192506304, 426692192506304, 427173698605504, 
    440298648900032, 145281707413952, 2076195733906855321610243882291887809736542929444660162770419005231977055492943987128757070204035524, 563500255547840, 581109621461952, 581109353026496, 
    72650454012352, 72650454012352, 565707877139009, 145281707413952, 145281707413952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144a2924934965930000924d24d64c0402482482c980004934960001920920d24d040648049249249a49ec9b0000926926f26c20836db6db6d80c04824800000920926926c20c248205949249248209209a00001b71341400000149a0c05800000124924924db6db6db60301049241260208248125349249269a69a49000049b49a4924030104104104c000269a6980004906db6db6db01809849a4820134012924924924924180934d24924906024d26926a00004934924924906065934d35930c008249048249a0820920920924000104920124800000024824900938d24934804024924934935534c00024d24934d301808249a0da6000104904000004c30db6db6d80c04024934100030134d24924900036db4d24900004d349249361009a6924d24c30124934d34d30c049a69249a4040124924924924180924924d24c30000124120926820004024824904000824900924024800806004d20830c00030d80c20924924920000824904824d30824924924800106104985000020c3d986c3ce30824d34d24800308db6dbcd80004124824126900834d04db4d200008249049a60208001a49b68029041261201248249249241009a0904124904026824126900006a008249048049a0820920900924000104920024800000004824904b40805804930920924924830124134da6800134c289a6924c06904d34924180d309b6db6d86036c24936db6db0c00d84830100f0c9a8138d341b01b6c24db0c06c06db0124924904026824924924900100924934d30c04d049249248201c41208040240249049249241001a0000824100924124830120124824804924924926968b360001249a49ac980c049048059b00009289680003241241a49a080cd008924a49349359340000a4d24d64d041029049340001240a4d24d04104902124924924da69b6c00024904920d360300348328e2724d24d44d000024a0924134d04102482524924d24da49268000249269349a0820924da4800024824926930820920824d24964db4d36d80005136927924124104db4d30c06d851369261241241045b6d35124c000349249a4904104924926924104126924d24c000249249a51041049208249249a49a0800900924924000134800124800034d849249005b6de6db6d80034d249a4904106db6db6db6db0d34d369249241169a4934930820914420d04126920810004920924920414900004000000504020100060830c24024d24104924926104924020124c00124c041249841251008049249b48208209009349240001248041a4800034d849249049048059b49309205249e5000046834924984124904d24d361241241169249308349208009041201200100049209269205a4100166d248144105128a4934924d67000824db4925930120920920b20000134c26000004024824124000100122924d24924924c000249249a4d841049249249309209b69b8d261240209241000268249249840049069349249301009240009201240165249229208249248060065028a4924924d24936104126da6934d84906124d04900000924120100124124920924004900534d24924904124934000038a26b3cd800049a6934b26000012524d34a36dc0c309249271b6db6db11b09209a4936988300184d271c0c009041279b4c31804d369b49261b6db61b0c301b6db6db6186186db6db6d86180800904804c000201241309360008249248249241209a49249a0904144924124160824c301b0b348209b4db09a6900036206230c301049209049a603cdc61b6db8c000209240269841041240201a48049249a4984104124da09269241241b6db71b6186126db6db8db6db01b6f6cdb61041248201a092482410080c9049208100041248049201249269261041049269a49a4904924926924920924924924d24820824954926184934da6e34d34806dbcdb6d84100824904824920800104920124820124525126924926c000249249a4d04104924924920920924d36924124000124100026824924984104908924d20820100924d36924124022492d35134d25900802d34d36924124084130c20004103124d36924124084514524b24924b301005249249248248100041040008205a4924824824810ca2cb6892824924924104092114d24d34f3d000024934d349b0100924d24b06924f26820824812420924d26126804124804904100824104984820104d269249241269a69c4924920186db6db6db61268209801a6924820006830924920812412594a24934930000526924924d04022924d249249241008a09a4924d20800004104100120826926934820100124904c00804924924924180924926924104134924924834c34965b249049049329249269241041a6934d24c00024d24db49041008049241049a0820926904d24000124924c040000249a4904900526924d36800014924d34924180924934d34926934c248249249369a6006124d26c308101849249b4d20124924924c00024924da49041049249249309209249249249241249249349a4924904924924d249240209b4da4d248208249a4124904000924924124012514920824924d20900004924d34c20820924934824000124936d34824924926900004924920800000900124904000124924f248000249849249049329249208209269348240001a6934c04020826924da0904104934db41009a49349a61041249249068000240049241041049249349200009241249241249249248049249249241809249269241041349249a4d45834934da49249049249249249a4180524d3593698c024934924d000008249249849a0820926104924000134820a24c00034da49249009289249340000a49a4924d041024a69e4924920820d34924924104092000124104124084124804d04902124924d24d060249249b4d04104924926924d20924d36924924114965964b6db25814924d269b6d204209249261268100049209249204249a4934900002924d269241040a4b249a49249025b7936da79860224a24824a4510004904000800000926924904000104820824000034da49249049245a492040012490082c0041249b4904900004120800920104d36924924114b14514410526924924c000149249249341008a4934d249249040228269249248200001249040040209a49a4d20804824924130100124924924c000249249a49841049249249309209249a4928924124924d34924c00022dbcdb8db61860001249040268041249849849009349249309209249a49209240169a6db91c0c205249249a4934824922920924924928900db69b6db0c204249349a6d34802924924d261040a4924924924904924920024d36964920104924126124124924924924900512524820924924824000124d35130c20824924920900004924d34d309249249a61141249249249000249249a4d04104924928d34100924d36924124126924935134d00004400124100026804124984104906934d26db0100924d369241240249b4d24900802924d389241240929a7924924820834d24924904102480004d24104902d24130924124084924d349240005249249a49248145a65100041040008204249249a48248109a69a6dc60300a4926934da4902db69a69b6c400b6da6944db4908db6db8e38180892892114d124001241000200000249b4d24100004120000900000d389249241a89a6924812414a20800004930526924100024c22800104104d04c20004104134130000820c26828104124104d00c000208209a0904c349040009209a69208001240849249040009a0924926100924134904920034c34900024004904924965934c00904125534d40820c24da4db4100824934934000820926934904000134924d24800026a649349029249261009241a48300001248249040040249005269240000048149241040001a0800104104d048248041049208040000209b09a098400092082482c000104106800010004104124020124924100026824924184024904924124800100924824900124136db6db6db00048209289269041208249a4924104124d67934c000009a4d24d24104134d24900024900024804904924824900124012400124924136c00024024104900004924d34920000926124124134d24934c100049249049a0000900904124000124924d24800024984904904934922920000924920804000104100c00000024920928980004d319300409aa9a69a4104124100806000024024104904104124800100000924134124124d24924800024924824900004904004900000924924b26000134104036024b2c9a49849049249241009a0924926104924134924a24c45834934da4904904904124d26d248208249249b08008209269341040001249a4824800034da49049049049040000205249041000008241341000041009289040009340a49a4904124d024a69e4920824920000124134104084124804d04d02100924104924092124924104026024924984104904924926920d20924d36924124114820924928c3c01000492a9209205041048000040149249269b0d204249a4100004902924d261041240a4b249a49049025b7936d86027822480124804d049024824a0004904804020000926904934000104920924800034da490490492492452040012492010c004124984934d00004126804920104d369249241149145944100049249849a0000a0c8009200001249b6964c00028a30809004b459b49305105269a4c00104014924d241801008a4800824100104830db6db0c06d84004124004120000020800824130d249060248269a4920c04902124924d000268249249841a4904924d24830100924db6926124124904124d26c060041249a4d84900834d249b09209b6db6d261240201b48001248228169a6db0030da05249349a6c34826db6db6db11b0922c36db6db62360471b6db6c36c00004820020806186930c30da05a49349a6c34802924d241061240a4926924d84904d24104d249361241a6da6934d84900006d249b0920920512530c36db0d86d80006db11c71e0c30db6db61b61861b6db7046c36db6db8d84000924930924000104004000800026924dac980000020900020926b389a40001a48201248041248049a49000089308349201041a0926924124d26d24810004924984920104920126924000134926d24804126c249a49049249b4920124924904026824924984104904924920920100924d369241241208369349b4920900124926d068041249a4d04104924926926920924d36924124000106d06d04824d341000041000001800000004249b4d20004902924d369241240929a7924820924800004d241049021341309241240840249041249024849249241009205249249248248145240049249b61205249249249a48100048341e41605109a69a6c401b60a4926924d84902db69248301b60b6da6934d84906db6db6200db0892004920924124092114d124001a6820138804124804904100006930824920104120924924124d2692481240, 960962612318422722514276120579029485995887052264404733803492738003668640030994337853923382876166591537305823477303555362496530297635651331192021766394825960003871678146298500452889648243859361371490740263206911619649492606725924266905990936395527218331124744249877512, 960962154094212046835217857624440951243359382280315518482490122125738730098024829755723285347109844888239342624799798493857152853764856633074727943498121867480440437896548269718918257985225241981825943133679129672249578827891566097450518098999190748210937857249559113, 571833028449216, 1161367889514944, 105630964713537, 531501949882259879639372883726243813390957502081530724936505807947513964104867485007629413295107536388, 
    1161157436117440, 1161168509407680, 105630964713537, 188397414113883790944883821505896061168034805570, 3957316615513757548701185265680621633635424460897731885283746459919765842102682894529163030276046821639093329151096260576151631833200870176155303980583957351363247147842711110, 79253966689216, 
    571833028449216, 580629121471424, 3958161983082584315783377305838629048360584189274436247038706637810177186608226863742141379476662837971091404282253546278056331005845287904011349152736968893262809665929951558, 571833028449216, 129777547423926009027780781102568141247809428432542757610719523840796178873988920637810912876612996, 1161226155594176, 
    1161368023863744, 105630964713537, 818982257500273022899745771748955030458532749643196524251233070500069225194824008802867860959531771060224764443196674639840229700913364043611015409768051297572242879335131863069227453070805641324212964634067829903868346410713331335859314207294058779264821113294186720964815510178839488443151227451713456250493480132528090235068950264051218236025531672110948624286999646700618, 457822182052288, 316943093993920, 960962612318422722514276120579029485995887052264404733803492738587663266840975931649575993447377030997014020390733898953638218975834180433436056703771840495911819196463544281146868827009493327424989055924281276205687744061256326996471017988626344748133647368249877512, 
    176063737500096, 176063737500096, 316943093993920, 571901211579328, 143082679963841, 568052920882112, 
    1161234879746496, 123695392671695679596741587065254242806862682383296486116061296796602787317119087531335825061361901607239307733988121721289573348011519037652135530234479852108656756839984710, 149693041480640, 571901211579328, 580697304601536, 424562224271808, 
    143632855225025, 145286136598976, 435557340549568, 145286136598976, 145286136598976, 431159294038464, 
    158497992872896, 158497992872896, 571901211579328, 143632855225025, 431150435668416, 456741910946651840557753849108081470352966832962, 
    513259120142961964537331115444631005067305970827513490513621155315030549041252634073283826062781304656581872513783638941639635985512339478380175799997029571499942403681862, 572313528439744, 563517435417536, 581109621461952, 143082679963841, 143632855225025, 
    581109621461952, 581109621461952, 581109621461952, 581109621461952, 581109621461952, 79306714780096, 
    17127386106468751301444613831724721838108185155, 79306714780096, 79306714780096, 79306714780096, 513259120142961964537331115444631005067305970827513490513621155314896159982220516254626530780942743764651843077610698183120763787913299146203367744522330474877291930627654, 106111548065857, 
    4080951628229277640960629114006027705366148792960945003932273890867412815902625971441557810675078365827140133699429445535750807145462268577304649103726353954675925281572644934, 4152989022756841046879059921035904353189284551263581981754876995186233102643058495689535166197420415569111350428330168536705140023605627727226880313529133821519200980274509894, 424836967961024, 6774210443576695379785539423776976701868206374763172037442616979180009647428171487959687158598653222098005567180360708501111682499087875318537647120550390036560018106644430046213550185864627496320173617932539497814683104991072136080123011399096044067073754429142966872547909226102855607348176310943348015206704745237463634975963067858127225419839587088217804056877825617022551114, 283815877546432, 283815877546432, 
    284099479605696, 565707877139009, 145419146367424, 145419146367424, 371085815699474074033166398212501170313674904386, 290847678010304, 
    176476053967296, 513259120142961964537331115444631005027556978090606574030776884938378043426091999909010165881973597957515830645063562538516634573737676137676278163244858240582132885139014, 853797363520448, 308439596143552, 308439596143552, 572314065310656, 
    581110158332864, 581109621461952, 581109621461952, 73120752931264, 73120752931264, 22880651877387912666330914305620875841810487106, 
    537796105276741744684019622315804649667832666493252434622938069758506340246732130329869075856287244996, 145689729307072, 145689729307072, 990141234549696, 16674316046003773019189936114363085810836845717216220097143622214992470538512594340472631036924191172, 106111548065857, 
    106111548065857, 106112017827905, 3965046722488752238797939231919101635782396474621457287225603822571031448500248693989937298319145301927894814804643056529966887080031576335624009872319801241938852792533772614, 551485156945714612344052655687821527630798349489931733200198276311002458254013917290993955038621765, 106111548065857, 28545062765754726017007092323160201298679695171, 
    3957316615500260807304147868602224556643527479921026238584239199174047645516279437510131512872289889195319835102852105636857237121806723995932782093364585758686739829129129542, 154073505468864, 154073505468864, 145277412446656, 736462597050703228649651517015231651152859792195, 581109621461952, 
    581109621461952, 581109353026496, 72639716594112, 72639716594112, 283958550204864, 565707877139009, 
    145277412446656, 145277412446656, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x249a4924924924926d80004d249b49b00009349349a4c04020920800d80004d248300009a0d369a61860201349349840248049249649a69a4a20000924926d34104126da69268208249a4b249049049a08000009a0924926104124126d248208040249a4b249049009249a4926d249b60001b4924da7820836db6db89309209269260300001268268278000249309a09b0000134e26dc75a69ac800024d249b4904106d39138924124138c00c26800024d24984104906e269c08209a0d37136924124024934d27934c00026a26f24a00004d349649b0000934d2492ad80024b2cb249800049acebcdb60001b6db79b6c00024800804126180c00004984820820c3c0060001040040201a08049b49a79248208249a4946a30000924d3c924104124da4924820826da4b24934904f379e49400009a4820000824820924100924d24124c208041248249a4804924900b252dda4925c000124d6cf269a8000126b27926800056f26946db000092cc201349861b4820124da684d20c286db0c06db4dc0934920124924924f24904106eb6936924d241269a79b68000249b0c000209a0824904024934904d269e0820820d36930124924024934c00026d34c20800000da0a00c00900004820904024800020800000800020984d300009b48209aa000036db6134c04026d20824b0000cda49849a003c0001a61049b4820026924824824940000830924d3c104924126c24820904026da4b049049049a0000b20800924100134924120c208061ac8249a4804924904f400019b49309209359e78001b6c24e56dbc0001b61b69a78201a6826da69e08009a0d20c2c0008201269a7800026830c30f00000006da6960000db01200000009a6120800020126836db6f06038d809a00008049a0124924924f04124906e369361241241209a7800000824904004924904d389301249241268000269b6824d269e08269a08028a49249249249249b6000124924d26c20824924d269b0920824826036000124924c20c24834da4986180904924d249b09200a49269249b4926d80004da49a4980d801049069249249b49308209a69b6926000124924d26c20824924d249b0920924b26926000126938dbad8a106db6db6db0c30920020104984020020124124820930d001801041201208049200a4934934db49a69801049249b0804d261049029249208309b4920826000036826020024020120824120120800920000020000824124820c26d24826906180db6d04920d209b4920924000336924120900d000009040a492493493498002090490490418cf269049020a69a4e26924d24d80006da49249a00009a49b49b60201b6da69a4804026924c20004d06da48200009209a49b49860201b6da69840248069acb26dbcb26e30000924924d241041649249249049000200309a00009249241041242469a68208268649249249049009a69389a49349360001a6924d26820826926d24d849069b69c49209209a49308001341a6924c20824826926d241808069b69c49209200924b4db6db4d000069a6a26e30000d36db6d34000134d34d34d34d00004db4d34d34104100134c00004904184d341041241024b4d80036c34d000209a0820000d36000db0d34100134d34d00004004d34d44104130dbcdb6e00004d34d00004d34904c34104134d241024824a49a6a6c9a00009249a6db6da68000249b6da4d000049269a69a082093d1459361041a69249248248040000000041041269a0820920c271341040200009249248248069a49a69b0000d349249241041b6d269a8820834d249249249069a4a36e300009e91e71b78000279c79c6de00009a0000000826820104124924d340000061a09a4804d04924924900926a26da6800024924926db6934000124db4db4d041041000000001041409b4d841049040b6e3db3da40000da4da59b49b79b00019c6e46de8c06030f36e3ce00004044830001b30d86dc6d88066c028b4e36da49800069a69a4920820db6d369261041a692492492483cda4da7a30c04924d00006db41241008269a4926920186030d249241a6824924924802d369b49260001a69a8924820836da4da4904104e369b69b6d661249340001b4d04904106184db49249040b0e060000248061a0820824820c36100100820000924924824830da4c218001848009a69a6924800026a241249800269a69a4920000820130104000824924924800024a3cda4984902c30db40009200000269a6826830db4804124904c369b69b60601240001849049261001849b4d04d04000d06f369261240824a49a0006a6c9a0924924db6c000041269a69a0820c36d38d341060009249a4924824b3cdb6c000049a0c001b6da6824980036da4d049208269a69201201040001201a69248249248069a0004b26830d341049249241b6c209081a4834d249049249000008200009801041341249240000060209a4804d049049249069a0004800c009b718003d1d10279c00079c6de092092680002ada4824924936db0000130db4db4d04104826f36f30106134926000db69341049841b4d049040b0e248371800061a48269a0820c36920d34100000924924924830da4da5a30c04d30e36db7a30c040089b6da6de6000924924924800024986024100024920826920006820104d26000824924924802c30920db60000000268209a4830da4834d04104c369369e8c30134d34000926db69041001a4984d049040b0db4da59300061b4034900000c36e38b38d86000db6f3d18c030e36e379b0c0cda4a30c04da413c1800059b49679b0c36030b38d86186036db11ecc02cb4e00036da49869a08269a4920db6106c309261a69248249248000040000040008209a69a4920186030d34d361a68249a492480000cdb6da4984db8b36020de6124902d360001b49261a6820826924836d84184924904000100004100106184db4934d04006030f2692613492408248, 1134850895647680, 291388038583232, 291388038583232, 1134988334732224, 2929459343204296902304627236097969932546139542338, 1128184905012160, 
    1134988334601152, 1128184905012160, 1132583085806528, 1136981266666432, 1128184905012160, 2928723418532825578142970376508477477070384976706, 
    143224422281665, 72709640818881, 143078384996545, 143078384996545, 143490701856961, 143490701856961, 
    143220257333569, 72709779231169, 143087117545921, 143220257333569, 143645740126913, 143645740126913, 
    91277190828992, 163844958327744, 581659376751552, 581659376751552, 581659376751552, 143645740126913, 
    143645740126913, 581659376751552, 581659376358336, 1139386246894528, 736461208688022691041007677589137812219733529410, 1130452714918848, 
    1441443975742222822104577926557302146391725766925392137959329916202759396408613549405730227037681374816850385688954185106820596313071883313280633952185926760890864684074847660732035341792338280990805057635381558395918555106183617462946280927627492555082437640246197512, 74917396623809, 581109621461952, 581109621461952, 17127016039108744813344941081280023783083661122, 583925464646046197433974099083655411740788828240384486640134483128563477512639056729737844943390596, 
    28545041136899390375759852262940436888828303170, 75050536411457, 75050536411457, 145290297349056, 2928715058480951996792890876297630435703076737858, 145290297349056, 
    163432641860544, 585507265319872, 581109621461952, 581109621461952, 581109353026496, 581109621461952, 
    163295337124800, 308431006208960, 581109621461952, 163295337124800, 308431006208960, 581109621461952, 
    581109621461952, 581109621461952, 581109621461952, 581109353026496, 79306710585537, 580629121471424, 
    580697304601536, 581109621461952, 581109621461952, 581110158332864, 581110158332864, 300183996994496, 
    300183996994496, 168242601661376, 299359498408896, 12488464953387753290700870440817778883981013570, 11774838384775837982664095306966653445991363394, 79457977373632, 
    871106349896640, 290564209775552, 4142815831847351501733523158230794308145579523367216052598048673735435713320944213988031756274861962417543726292135420377327855306347972914986781946855917449841246404983384646, 290564209775552, 297194374456906221681086841812971744999716844703441252118404902340226846343059893728836748192300206126620157205127272059416271378745852849188716378049240607027465804295382252668949800219892400387952388480027111228411076919544650520449260660108438284939957784118727426226771332991491080650679271296210710017959982069217196772054868733159416410621040035147612291030018381661508902925613667634154405365804528435620802610662598844495035042376566217085505127446241740771440548803341730365061677385547952231885, 871106349372352, 
    871106349372352, 871106349896640, 290564210168768, 290564210168768, 871381227541440, 75883624928192, 
    23014456880290496075264368003651437409119294274, 261581628146507880495587293551552130535249084435028831685913737242258382016202976398302604998277764, 411779005811161373478442628608637397377149620071630037209638555437811661680600384505564763160749284672132337141803417924496381329352436804047656384633897623981700912216437799804022198194624000543548127555165763755819427296218980277648574998232314671282847533542577291403042233427058515103965997869502098327835750181400199579596234563911974093633115887077351044806957403382752395862195003435022304892870949301218081562190221372332798494810519643774140002303841693835906126907522770716115353953168990542104549804453070135922797812250993551394691839806280158253336163593884747353987381696797343106140169243822762727421179335219587769459865332791730529063200120305429496552351305486026267694006398651212317130689122144274861096928383790419965460878924603402122462737278671872807311695708798515775466259247365803416649270996798021482819751277141187164062654290731499255178029759448497174979776099246296610982606362065380841413053649482084770935348389792267205611949478585002396975111057243790360440434370747601663060567006897936203749100686890864715436364762594977863229475709316755657158371536107827593448121000619435029995727758252841503063934869768765441113531410485153516592904894528835765755074332188791147156319800465360951612422526266549458441377643803816445955244854079789687821727269565095532257217680494237028048312367091141826805131924338202693588956567611850488462048389009212217376420547087468261702214294039761325435828967249314109165484759888461028110824218513333112269510172436137955763344327244592228033839241538415314478455168186263965846091332207174702497055437785954287764955578526182380881247522737039428634992333660046912225845304642789015274519220873348168255896722915551985993055172546313510554358355300600067107659565280590182709951346947679378533443801185413073513389550017388994340474119370574378221622034087855874427583376789345894052290654744377698572089496835365965827360834059716699373156637328002616777419935760504794377086310237891456085184773428643170796078648793816534482498288642748854449374373429243673371657612974406345542743495821281495033993983694266928883591397965637094338778336720890073116303172964847497373997178614152053458766394952630369842136817009430379085929328862938612103731413102940206733422957884400407522778020455648959854250847641045913267151621250675178679061655353196527819190986042161178741234528358714269275495883856384438493277018181150010982018651329334711554768177086223144257528062443236801019551043002051500868535854670720016062614538548560115583604382896396235797105648943069421940239775364141884172284095381499388975061380659385973544754514480371803815223097251335719450662011214490602922127165681052716515245766209983995491494122413656668405071975221303643084423534538356760152533503737406082099813142316151496959933705084298043045786139273400532365923019469390717412420723103611011802917702606453214253014704304034688557817722007449341298471272676185432505201358794798669058976582135112753667190300307524538426217612227215147332254599895578453847049794358200969206908908373290673535937024325572860512059840680285886627805363069701769252570973537367797141723538616986063016244545363925301498729473091232661506907974030953417093106114220065140942512832270189119997767866700410621019068232056169845550705582902925375713362899906178368250971760878491515761054866137429653357918638917350755049747708446106469492238391407868880939079977572674698145618076640743597636191970255319707993912065443425947243528570106293254866203087978673345512596464179920433843550843226471519845628446705001610738295528000344480177189993606579624965670737262767735983947837889139043354160209344293440162613622531991142779777514418353999344303035922484972234912971474413686911414568574380756787946648565191141456641086979593623685457314746260684833407750877716200702737861338333909415403836292074353506668688369893851956037783719955947624615714411959587385984901871003247455587900424299803207756905602696187588116423730767462, 79457977373632, 79457977373632, 564789732273735344921673781874312416709392249345721235815221750316531469627369535442905926897635225732, 
    146252369105856, 581659376751552, 46385725601324262738697497935930828079008641858, 149825917031360, 149825917031360, 581659644924864, 
    581659645187008, 581659376751552, 871655166448576, 871105410634688, 871655166448576, 580834475119552, 
    581109621461952, 581109621461952, 580697304601536, 581109621461952, 581109621461952, 581659377275840, 
    149825917031360, 149825917031360, 172504015442880, 149825917031360, 149825917031360, 171816820675520, 
    4080982759733772265525728496982386161057153974320744732555339347434241250296684963795262071506863186425435413197050809256956814961211591830329578594213179218902620454007073094, 435698806035392, 290563942257600, 581109621461952, 290563405386688, 290563405386688, 
    581109621461952, 290563405386688, 290563405386688, 290563673822144, 290563942257600, 145221577872320, 
    426765274059712, 292557074731968, 294824012944320, 290564210693056]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125259649218641209249248248048209a6800024801920800105920904824824904800800000b24905130d8186410092cdb630c820084d679e00071205149249201009a05249248248248208200009248205249248249248244904929248249201869a00a41241041a69ac112092524904924020924814824820824924812424924b301809a0924930a24800020804d64dc0000d609b5927000135800804100c20804100000180000864820006104004924924c249201869a61240241040308261b6c36c36c36c241249249849240000048248048200060048248249201200000208249049248008209a4924d008049249249360241a49a4800004804104126924900830836db6b200001009249a4030c30f36dbcc20f30db6db6db090292080c028828a04920c26d36da0824934824906804104004824904000100124b2402482080600483480c024b2498cb2690248, 371085815720731418620478969458332678545981068098, 371085815720731418620488640901783224464823046978, 105776595146945, 105639151999169, 105639286212673, 105639554648129, 
    3957316615506559286616511616928790261601833419865142522449334657741801648710266275264481018757332605902909644794273396145976782706665173148992891744518446892001845705301995078, 105707804430529, 105776595210433, 105707804430529, 3957286424264322408834782460213906390211914191063211702606165099325140497412023484244963083155339114362023616398190802297774998967526075248244121878842886715866937104394661446, 426688903188928, 
    427169940378048, 426688903188928, 427169940378048, 862585134781376, 284777882194368, 290547030299072, 
    290547030299072, 871389817476032, 290409590952384, 290409590952384, 290821908206016, 283816816153024, 
    283816816153024, 241534516580182981861307981157575458020754603741198741551111290745269406792766261111221977998009069184093290767328163384317212775339059897479465578002822778921439515291207, 586521187104198254813645053532168626105420952735416532703152134040220108188719579141898222304090091652, 586521187104198254813645053532168626105420952738320197398965771572589825121850245060686639044578472068, 290409590952384, 290409590952384, 
    290821908206016, 290821908206016]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524c00064d24c2000000000492092412480000080002c8000248049200019249209241060209a6120c0006492082498000c9a49049300019b4930920f3c000000082534c20c061678149208201a5920904020804165824000920000820104905860000824904180820800004800004020926104020b2c134c31806966814920820125920134904124924904d24924124924020820024100020000800924920124104134924134c60125900024924924920924920824904f300009a0904c00006d05024100830184140900024800020804d04de00009209a6106030820020130000124020984100c20a041000001b0020904c00006d05004900805934d30924924100924104020134934804100124804904d041248201005249049200348041249040241008008249249a0400020124924800804864d249025041a41b69348108201acc3010c024d308301b4180904020c06104024000920180820126984180c20804d308001841008261040308201b6c360301060241201e0c00160124104800024804124904024904924120800920924824900124104104920804020824864924104924124800120924824100124020020926d00014104906d24c20820121924904104124124920812426804026da4980800824db48208201009b69ac1041301369b082082092410080180083cdbc9a0820824900024020800824000804004126da4904104804da4f200001009b69a40000363249bc824900db4db49b09049241049249241349249049249008208009049a0400020024924804904104d24904921804964f20522510934c001b4db6c2ad34101936c30104100120804100004004926800d30820184d60c36180dbcdb61860301b6db7026186d86db6de09ac124904024930c249041249249049249209249209249241349241041048000040249241208001209249a4134924104020125926814912424b2492482cd3c80410c004824904101805964d20000100326b2400000012403682498c024b2498c9249029249b48301348209241249801a09a0824d0602012492093400690c920da0c04d209201049b69261a0834c26da690020cd8cdb6db09a408, 105776595146945, 28545062755131246119312244772586320414485250883, 25690556491317449418804977125493900021760000835, 97053213373766324928055044935943188880048542530, 105776595146945, 105639151999169, 
    105639286212673, 105639286212673, 105639084886081, 105639084886081, 105639084886081, 105639286212673, 
    572854693794240, 564050010837440, 581659376751552, 105776595278017, 17127037689224021982623040195642197567374119746, 105776662321345, 
    105776595210433, 284778083520960, 730932012943292308569336701024598321680483373890, 105639156256961, 105776595210433, 105776595210433, 
    105707804430529, 105776595210433, 105707804430529, 105776528103617, 105776595210433, 28545062745826610851591228548041215903119971139, 
    106120121290945, 51381112940732903622486450468935704762275353410, 371085815683512892761701799559486371707165365058, 3957286424260719763022745916236227742819265831699568903212611379691485104047015021762543682422066548031726556739534546138182488078177405818682655619893683505456358782280445510, 3957286424264304834952824695516593235453631610461841924321801404770619401215989568535185070058910495580890337200966606862856462468877355978110459201658787537714734596976324166, 23192863565144762642012027708528283121550140227, 
    23192863482566482911253630816099780726907511619, 105776595278017, 106120121223233, 324403039781655621515434535743637919327946121335631634779571525715231723501657636509257185728304581, 23549675405742972881518202308462717463112508227, 51381112940732903622486450468937393618578068290, 
    371085815683512892761701799559488060563468079938, 73671649661376, 73671649661376, 284778083520960, 73671649661376, 73671649661376, 
    536692881530235262567514504771521129154836536089997166122174610940496253593828592639934096096751743108, 28545046421577633914807599363830083633402643267, 80268719428032, 80268719428032, 89081992844224, 89081992844224, 
    89081992844224, 259538272591457719330497462963486464606774842232850722952677358820739852741728343776070699544106821, 259538272591457719330497892307323205754262264456749588698623496636368977441573387741742517000230725, 144049050882496, 146243779170752, 146243779170752, 
    146243779170752, 259775872474346333411709944770439476569845449095167679584999211472962820284787397427025287473406789, 159455098573760]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524d269a4d20c209249249249348269269a49000048a4d40844d26d2082cdb0f361801249a48249348045149249249200005249249248248244a69a00009268204249248249a48104929249a49249a41860a4992092524924924d24820814912424934b369a40009249249a4926980004d64dc6db0060934d26d34800c249a4924d20006da4e34930000824d26d269000049249249a49249a41861248249a49369a4036db6db6db6c24124924924924d34830824824d04026830c24824926d26db0c20924924924dc68269a6924d269049249a49369a41249a4b6484082690410412492cd06e07986de79b00001009249a41029249208049261049269240209a41249a6900c20904100804924da08269a4136820000020124934834d060249a4b049268201809a6db610248, 176145272281281, 176076617814209, 176076617814209, 176076617814209, 176007898337473, 286156768940480, 
    9071248806336, 7775365053957718559579597671664242524272040866747054545432256283987388152685317427442288067311785072625779536033765002105718238879321659389824287753387541575968296401882695, 427169806291392, 581109621461952, 143641445159617, 143641445159617]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524d66924c000249279e4930000924924924c000249acb249000049679b49300009a4d369a80000a4b3cc2480000000000490012092cf3cdb0000120000000060802534da6d66c310149249a5921020964d24964c31024926924b26188134935966830826934dac9882049249b59a0c20826d30b262001149269b59b1020134924924904104d249249249241349249369b4c249249249b6d21924d349341041249249249249208208201041a6820000804920920824934f369a4000934d36d24c00024d34934d300009249a4924980004d64de69a00009a6d369a8000124d36d24c00024a24924d20004d34e34940000824d36d26900004924924924104134924924924904d249249a4d20524924926d348649249249041025208208249249204000201249248109a71acd3cc30c24d369b4db0c60934d24d34c318249a69249a618c1269b4da8a08304d369b4d30c308249a4938a240061b6d38c31024126de6db0c60124924924c04024924924d041049249249209209249249341241349249268648249249249b0d209249a4934124116db6db6db0db0820824920020812424b2492492cf3c826924924d2690c9a69249369a43269e6b24f3c82498410412492cd04105984d65920000100b269240001a6124d6c802964dc4d3500002ad34d36d36200db6db6db6db613cdb6db6db6d8d9369a5131030a26104106924e36180004024938b061349349a4904105134926924d241b6db6db6dc7826db6db6db71b19b6db6db6186124820820d249b6c2000080492c920824820804120104920824000824124030134d00024820900020904900804d349b0820824100820020020126d0002480c0249a4b04c30180f38db61269a01809a6db6104901805230800924104920924104020136830804100104824900800804a20900400020126b248041041248049025308040249349045108208048008008209249248200208269a4d360200000301a6db4c24926934d8090c9261a00300200001809349a618006c336db6c00006034da69040041009a69a400c1b61badb6c00024826926904124104020900804104124824904924120804920924824100924104104800024820804024924904924120800120924824100924104020124924814100804d24d20820100924d2411240, 3958161983082584315783377305838629048360584189253880050633205067377134473659346473624215732254781846597536157232473253931015881857356071556288973153546839065291769535929465158, 176145272281281, 4217239466888111472080273688103668648365242168503149450838301469891249895027436595424667388893230981, 176145272346817, 94198707078061318989726117345120799547086603075, 4217239466888111472080135868731690876749345125542705938117016979880939633238376449440493745994789125, 
    176076618207425, 176145272281281, 176145272281281, 176145272281281, 176007967480001, 435690216100288, 
    143086979125696, 176007898337473, 299359766844352, 290545957081536, 581109621461952, 581109621461952, 
    176076617748673, 176076617814209, 176007898337473, 176076617814209, 176076617814209, 176076617814209, 
    176007898337473, 15488341795066791663667654694697035730377966841928738439672026527444889011267689674650926020812337535023857811629342690570216344125900623562219849869535435979412304021048902, 15488341795066743610084033780429030694260499029960274070576392557394007554807810581889303486059341225647768509874795495521722408281678939804887055629130268625828566879587910, 290546225516992, 290546225516992, 290546225516992, 
    176076618731713, 143091269898433, 143091269898433, 563500255547840, 581109621461952, 283953450717632, 
    494862248972736, 424699663225280, 505857365250496, 508056388506048, 501459318739392, 1073223081923520, 
    581109621461952, 581109621461952, 290546225516992, 286156768940480, 567911186960832, 581109621461952, 
    290546493952448, 424562224271808, 143641445159617, 145281841631680, 149679888142784, 145281841631680, 
    286156768940480, 145281841631680, 149679888142784, 572304670069184, 158493697905600, 158493697905600, 
    11451432787134601598066467498002989476011323970, 2076195300782788956301356523062313155264093754374837000783108643835218619438308456406188233358464837, 143641445159617, 143641445159617, 143641445159617, 143641445159617, 
    286156768940480, 567911186960832, 290546225516992, 290546225516992, 290546225516992, 290546225516992, 
    299359498408896]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249249b4d24d80004da4da4904f041049028a49249269a4926d800049349249b08209249249a6c248209a0800c00004934920830920db6924186024124924926c248029249249269249b60001248269240360041240ac9acb269000049a6924b261881a49a6926c208369a4926a000049249249b0820da6924a2818c126934926d2482c9acb24980004db6db6e362061b6db6db6c30c00000004126100800824904920824c30006004020000020124802924924db4d349a6004124d36c30134984124080800000da09041a6104030b2c024820826d26800804100c20a008008208048200261040308200200000200248000000000209009208209b49201b6186030dbc026830826d2480098000cda49049a01861809a4102dacdb630c1b0124924c209240008241241a610433c9a412408, 291370724102592, 291370724102592, 290409590952384, 290409590952384, 290821908206016, 286981267526080, 
    284777882194368, 284777882194368, 284777882194368, 290546225516992, 290546225516992, 308439596143552, 
    296950155973056, 286019329987008, 290546225516992, 290546225516992, 308439596143552, 182777604928272491304697865278729782853028041538]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125248a5924936db18209349a49a48348209a4836c00006dc4900c401209248249a48048045144a69b69a69b00005249249a48248308008200009a05a49248248248104929248a4824920db61801920925249149049241a6c208124249249249209a4826d80204d64d479a00409e4925166c01004924924924126906db0c30d209249249248249209b6186124124924b24d24b36c00024904924306c008248249a4926d30c049269249b4d26124924926db48249a4926d249049a69249369a6124f36db6db6db61b6db6db6db6c04004124126d80004904986d20000000d86db6000000120134802924924db6db6db61b6124824920db6186036db6db6c36c241249249a49049a41b6c300348209a4904920804920020120020924924124824124934824d00824924824906c00804004124126d8080082683cdb0db6db61b6c361b6db6c36d86c04004124126d00c00f36db6e300000009009a410248, 33283751113574825037484909273484443740322546308347282019519150310084983555868044609290426616181223685, 316745325807681, 581109621461952, 15458153778478996681317252369848986837080623924931352753084020394936162316352938373715351863326583065108456100509600422938332275831810024648747983614164420851409676727504455, 9071248806336, 9071248806336, 
    283815877546432, 11441327723343495532322295548235886148381061698, 283815877546432, 479601568672752410562509191191805158226359505730, 426687897539008, 427169403638208]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125248a4d349679c0000924926d36c040209a4836e00000004900000120920004800064802514924924824920db63001041359b6c60814924926db18201349249a4d04d241e6060020837b30c0c104924924db63040249249249209a4826d800049249279c0000924125967000002b2492492682c9209b618c1a6124924b36db6f37000025904924326020824824924926d30c049249249b4d261349249369b4024924926d249049a69249369a6126db6db6db6db61b6db6db6dc9004004124126d80804d04db6d20000000d86db60200001209b6804d24926d2492092492492c1041349249b4d248249269249a4902524924924e04104534d249b4db4c38db6dc8e492008008268249a04000003201248109b6dbcdb6c37824924db6db6db623c1b79b6db6c318279b6db6db0de0826920db018c1041b6db7031824104966de0c60124934d3490c024924d24b0410492492c96492092492592c924134924b6593482692496cb2690492492c966d2092492592c1241e6db6f67b6d814d2492cd66d30924925b2db6c0200001a092c812420924900824900800824824da0824924020924104d24806184020804936c04d20824800906000804004124126d8180cc36dbce30c36db6030db6186c06c06000004004124126d04100804d84d200000009849a40000001a4136804d24920d20100924924100924134924834c040249269249849025249249040249008008248069a04000001a0024838db6d80c00000804f378049205109a69a4d300201249b68019b48269a6934d808069a6da4930da09269a4920c361a0100184d80d26180000004000906db6db6db0180000930f009ac2061b61b11b6c24124924804004824924904024904924924930920924924926124134924824804026924904900804924920900120924924926124114d249219001009249241a60300001241a012481240, 6767303366728955361338858020691928854773103564592880878259777991636075645430706129701694566574902696197642661141673206817781344364097141430300136547850345567800644691506945174542195798398802503525340976907440830987291278310519768928220959101747243124199568719423448070685985186725330557687011216270682304101949857510275816936795855709478049572897684910491689712418598460882526154, 316745325807681, 316745325807681, 4022983576437287596354050139202407331305053726698939149830103631049781931035138523654115057499409584466940890067772215287835186860834729514735493773134094292880398407020686918, 316745325807681, 316745527134273, 
    316745325807681, 33283751113574826881502646815875692283563193868687215315925540561504768976735681974796320910716990597, 371085815678549037712426335883504164078453524291, 188398111012020059368484253040821676696922227267, 143086979125696, 33218934237608983480854871581501395354763428388165425197269363946286348694137729932849382596133025669, 
    143086979125696, 33218934237609691583669880253857686451264504278404938041854845635967592845401787608313680884063064325, 145281707413952, 145281707413952, 145281707413952, 426756818342336, 
    426756818342336, 143086979125696, 182711399298544637389823700524105491278458835523, 143086979125696, 182711399383615229120058316389949143136400891459, 145281707413952, 
    145281707413952, 145281707413952, 158493026816960, 426756818342336, 426756818342336, 426756818342336, 
    426756818342336, 426756818342336, 426756818342336, 426756818342336, 145281707413952, 145281707413952, 
    145281707413952, 708236358455744, 725845724369856, 426756818342336, 426756818342336, 708236358455744, 
    33218934237608983480854761240135352879883661575463385052542844635568790730319321835532044185722451845, 72709577904576, 424836833743296, 283816011764160, 72709577904576, 33218934237609691583666868836186822429738658957193458736589849108640038984581644225169727102125782789, 
    497404534067648, 989986213073344, 497404534067648, 989986213073344, 33219377757385355898274052408577105148337795543999216834438886053858158330988990186921724178560059781, 88669676377024, 
    18159668040640, 188398111013183097736753796800123847388218528323, 708236358455744, 15488342021811998855061131474848414288938310930184573776262402886227407488615882391889037808171798131634044405807290971501956749768989207832458421058336084006257676640472646, 286157574246848, 290546225516992, 
    290546225516992, 33218934237609691583666909999527528259666470571293718827130634773504509283553579459001884543828884037, 283966872494913, 18160204911552, 143086979125696, 283953450717632, 
    143086979125696, 73121894764992, 73121894764992, 284228328624576, 354597139911104, 3957920452942559774011439111213755252686269257527929192149412905855699754193710145100738828088512626327075720573395912619288765306768877954759135737094220938373264177549538886, 
    284516645102401, 72709577904576, 72709577904576, 283816011764160, 532345469047865660768624110573826104194972757739581446356114688253984789910377120189248069560762016452, 11451432787134440606440240855605496755817296450, 
    145281707413952, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x228a28a49a49a69a0000924b269a6b28800034d34d24d00004d34d36934104134d04000004904c349201041241024a49a0004a26920934d34d34d80004c34d30d3410402080002082083adbcf24980004d34d00004d24904d3410012492410248, 66438758485720862846686996639947889544926626111574447646095897731827321357794333821710645464585580804, 143091269898433, 572029792162240, 589639694947264]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a49249349a6db0000924b24924f36c000249249269000049249249241a41bcdb6f36c00024924820806d068249249241a4036c3ac38c000029249300049a6d20924924934920004824924d249a4024904026c30824836f24800004b30c06036f30c249208049261069249241249a41bcd80030f30c0448, 425523960418752, 4152475765709822164888452251670546109520883132917440949116256156783113074226005508672188972864161945240762699556765256665017374924627125441304349738952109028174418335756155462, 286981267526080, 989321606871381778045224032412724137007070548622224358849833134954427299928946852602131015203537417574576323671855996080369264362905900682262642733519662641795331800343948871, 3957316615499415510444267685974968730066344978484337343277860458963730595778168086284812339712773245571135552151237037243609488222614309482549609600888316375732336577285637702, 286019195769280, 
    286019329987008, 9071248806336, 9071248806336]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a28a49a4924924d800049349249a0820924924926124124da6d248248249248200049049349208209209a49a4906020124da6d248248028a68a49249249360000a49249249049029209208001240a49249249049020a2d26d369ac1860b4d249a4da0004924924920820db89a69369243269a692492486c92cb24980004904100004d241049008249249200000000009240200200249248028a4d36d36d368000b6db6db4da4907b2cf349260000a2d34c301349040b4db4d849249020a2d261060309ac0841040000048049008208249200000001000200200200248248341000040040049208209a4920d36106020d2432682082492486c90000cda49849028a4d249240301240b4926904d84904120820100100084924904934903b2c0003369240a208, 572854290747840, 572854693794240, 572854693794240, 1461507215281996944351681699986446261958498865986, 568460539204032, 581659376751552, 
    581659376751552, 581659376358336, 480481546266110744842554101926582037516884295026952688057685822915922451476555041798932418578729116029575589708958890381834645230825118526766109072244413132375528125058464018747520347301127424805483633409535543143128487309878521189887521794987059008973571080249877512, 563225109205440, 563500255547840, 563500255547840, 
    563500255547840, 572029792162240, 572029792162240, 581109621461952, 581109621461952, 581109353026496, 
    576294828904896]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a49259649249259300009acb6cb38004164d24964c048349b6db4980d049249041019a09acb06000324164d24964c04024984da498d900924924924924964c0002492492cd80104d249a4d36024124d04c64c0002412410000c904db49318601209249249363240249269a8966c0002cb67a38f56c0002492492c980004935b359b0000924924b2602013cd35364c0002492482080cd04905800001920824924b260200001048040008049249279269340009a4f26b2c0041649a51e4d64866d3cd24a601049379b49600019248201009258209a4000b6ab24164824004164826164d049ac100924db49b4db0020d251679258000269a4da6980104db69b6936c24124d66d24c0006492080602496082798402d9ac9051379c00600209b6136136b24024926800026960c2492c9b49200049079e5900000824924f20b2600010410400002483cf2480000c9a492080492c104930005b45920924924020b2613d104034b608049348219b01009009ac338000b24166c26004c0406620d1848081049200019308009ac000338b04160c260041e4836d86c049a61049300019b49619209249ec9b1840180f3c920d34f3600010416c1e6000020b34c3cc00000004160180320926100000324125960c00066024b2498c200804b34d60db03201249a08219b59209258000661058249049001ac9051319e00301e09241a41361a4124c6480010482490410cdac904d241a41369a4124c00064d248649219a000512080, 548087505526881151358608753891152238884681691714, 73672656228800, 144049050882496, 214417727951296, 144049050882496, 365399103964886692344315616700286641950121022274, 
    376817085501386189408960319324630167007583556418, 182711399295867957584509646452913977922829701954, 365399103964886692344315616700277634750866281282, 354116840985024, 11440325970597821564695256503220059156481332034, 535654348311007583219220530212096713780992547072089192797149631974549208673495929356241575420291621572, 
    730775907131406180436117470005856337186418348866, 11440630863601178873987711552033784868255052354, 91366501655140124510127261243513169170747380546, 596585030916676750471931164953278183974375516342068643160110204278569568129882867397011223021496791172, 132875501330558638018205846738710772492753777890805980163787670727077664389829832357685000678593156933, 4055037888506132447723663373383685709025918025685749825995495115526442388837726138856244613543428, 
    290547029905856, 290547030299072, 532287082837304853857219408792445780473986583543539829202877625096423859091255693128893579742220034756, 590616141864731671365364751947741311757561467420477516486560916410582775195958190813430584085132308612, 642197477659072, 532287082837304853857221167384801072214094874305664370917006641910651141086867548609393292986806346436, 
    132875501330558638018204967013189289881161945137395420845908507474747455524515515800690676264805488453, 132875501330558638018204967013189289881161945137395420932529131664708847339065870014431044052464326469, 565304150213185, 1461529513348157059012705351945112181989653414723, 565716467073601, 565716198638145, 
    565716467073601, 565304150213185, 132875501330558638018203208850177834882591055747171349036949194617876764720310011550878821871945930565, 1461529513368760171542325315473939157020015919939, 572305474458048, 572305474851264, 
    572305474851264, 73672656228800, 73671649595840, 144049050882496, 114224765568707201108850748587459204628623676226, 22880651898657588846968087484423499394683261762, 
    214417727951296, 144049050882496, 707001554440640, 91388802485409246863503412827628624998551278402, 283954255237568, 283954255237568, 
    22880651877389859785080505101693856430549914434, 354116840985024, 283954255237568, 847181234049472, 365421404795155814697691768284395060900285928258, 73671649595840, 
    73671649595840, 4153200366495387900827873951498842478103725840948588146232550577462324988684855241427073380665875257721256853016385386933219761850762939046962963934223583912007649326025112134, 114224853191416683290133679050089112650117043010, 73671649595840, 588402312849511981333498738016951603344631933739087692927281794919498521495358966676173838218931905220, 214417727951296, 
    73671649595840, 537796105276741744684020501629611755230409858128727161560998171806099131030440829664349861403330519748, 3957316615499415510444320060224698116918833857480650043455340645125437742430173515207591388748984104516102375650077650446552675350938436212173180325648221877934939138693187142, 565716064424641, 588409060682130665965264616729073877589442689540027440321440838286084172662753296070399929856005677764, 565716198638145, 
    565716467073601, 132875517170550389995170533287665928174499114469919095439169942954102849060583629412223266852994207941, 565716467073601, 565716198638145, 91283632755648, 75879262785984, 
    411137932617642844489381242256715292672719344450, 365466006455694059434154630329449332980639093570, 75879262785984, 45761216642489893605841749521599367719497529922, 216616751206848, 45761216642489893605841749521599367717886917186, 
    75879262785984, 146243780088256, 286156768940480, 145281707413952, 286156768940480, 286156768940480, 
    75879262785984, 519298297334960417723530276511126561540813643964450133159300026362247130092758793784864945129816324, 91522607467023981013470883496536270657009242946, 91522607467023981013470883496540703904803869506, 75879262785984, 114358309213464139978078279163307624944904459074, 
    216616751206848, 75879262785984, 146243780088256, 145281707413952, 286156768940480, 182866808249348988324135087314922608253489664834, 
    286156768940480, 286156768940480, 91522607424820831155673575546715343276403086146, 426756818342336, 990123517809088, 426756818342336, 
    426756818342336, 286156768940480, 286156768940480, 1461685619159542453087059722587838326416368276291, 532345469047865660768622333090341906276664111579798987567971631203042387187328535005061061350135079620, 582173774869328525925783379720064175142245382296998908570761952147014971445728160867009857703945347780, 
    532345469047865660768624091682697198016772402341923529282100648017269669182940390485560774594721391300, 145281707413952, 145281707413952, 426756818342336, 435690216100288, 145281707413952, 
    426756818342336, 426756818342336, 145281707413952, 290546225516992, 290546493952448, 290546493952448, 
    290546225516992, 1461685619180644028015958376562753258556152156995, 163307685155776, 79238933844416, 290547029905856, 290547029905856, 
    79238933844416, 91701014109176802612191586390536726004711314242, 149679753925056, 149679753925056, 548419972200835735836527665045506500948989588034, 79238933844416, 
    290547029905856, 290547030299072, 79238933844416, 360713910751680, 642197477659072, 23549676764528270582391042233629597599554097986, 
    290546091299264, 290546493952448, 149679753925056, 431154864853440, 431154864853440, 431154864853440, 
    712630109999552, 149679753925056, 290547030823360, 290547030823360]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b10_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_13_0
  · exact tv_b10_13_1
  · exact tv_b10_13_2
  · exact tv_b10_13_3
  · exact tv_b10_13_4
  · exact tv_b10_13_5
  · exact tv_b10_13_6
  · exact tv_b10_13_7
  · exact tv_b10_13_8
  · exact tv_b10_13_9
  · exact tv_b10_13_10
  · exact tv_b10_13_11
  · exact tv_b10_13_12
  · exact tv_b10_13_13
  · exact tv_b10_13_14
  · exact tv_b10_13_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x22a22924924924d249800049349249a00009a49349b60001b7126924804020804020804d049348200009209a4d389860301b71269040248025245169269249a00005a4f249268208169209000009205a4f24820824810924928924924926000124934924984904824120820030124c24c268208249269241849069c09309208201971125a89a69a6800012524c20826820812424a369a69000029aadac9a61061b6da69370000249a49a49200049349a49a0000924d26d36986135126924800024b2cda4980004d248200049241008000049249208241000009b60001000249208025269249a69a00005a4d269a6820814b379b49400005968200008249205a4c208269248109b49269a4924800124936934da4906934b38926000124da8d248208269349b4920820926820124904124926904da0804197112524da69a68208125a08000209a4812424a0000cf269029aa1800309a61b6c000269370248240008049008048000049a08241000000000001200040000209800048040049300009a4820924904030934135100024920824b0000cda4984d025268249a00009205a4d268208248169200009a08005a4c208269a4814b400019b4930510d36db63008201b79e6c001b6c26dc71b00091309269b4020124124938d84004906db6e30c30db0826000020100124da68208248209340049a08049349a0820920130000030926124c20026924820900800924920197112524da6820820812524c208269a68124028a48a4924924934926000124d24926820826924d24d841069b49a4920920820100820134124d24820824826934da4180c069b49a49209200a49229a4924924980002924d249241240a0904820804d02924924924124082926f269a80000a6936a269841869b69a49a0820926926924800124d269248208269349b4f241049349a4920920926b36926000134920800124904020020124924820904000024d000048009249200a6da49a4da49200029a4db6d36924124d2cf249800028a49a0c049241029a49361249240829260001b09a80a6906200c2c9069b08209a49a0920900020124020120020924820904004000000004800920920820000120100124c20826924826924100c24d049348209249209260003369261340b4db6e0c1a6904924924d00804902924da4136124120900004804002924d24124924084c0000cda49028820a4922924924924d808049a69b49a00009249a6d36000124926d248040248209000049048269b00009209249a6934030124926d040248045225149269a49a00005249a69268208149069a00009205249a68208248109a492c9249249b4020124924934a04904920824000020024924da682082492c9241849009269e49208201969127269acb38c000124201209a682081242c9a49a492492cd808059c49379b0000924b26934000134db4d6cc0602482492000c985844930001920924b26934030134db4d0c0668028a4934db49a08049249349a00009a6db6d369861a69a6d2480403cda49a6a00002924e36db6db8000100004d24124900004934924920180030934986000026d209248049269269300005249a4a26820834d24934904102514590000926824920420024b269248109a6d36d268201e6db6de70000249b6db4f249069a6da4d30000d36f369a61861a6924924820836e38e36d883069a49249a08209240001069049241000000200249041e6db71b6c00016db6db6db0c30d34924d241041a69249a68208125124000249a09a481242490400000480492080000480082618010003002082010002480002498c000002000820db89a80001b6da69208000049a41a49000049349a49a0000020100104000026d209248000249acda4984db69a0000db61049268200008305249a4820824834d249041049025100009249a69a0420024926824810004b479b49305109a69260001261a49a69042849069a6da0000d309a6924c209248269a69308249a0000120984924104004930804904000900b36926020124da69248208069349249201e6db10001b6c16db6db0c36db0d349241041241a69248209a68125124201249a69a68124029268a49249249360201249a6d268208249249b4d84104d349c49209209208240001241249a6c208248249249a4d00c04d349b49209200a69a29a4924924d80802924924d241240a4820900004902924924924124082f3c926d34924b360201669259e6c00034dac9a4d00006e36d35b30180d30924800326161925800064834dac9a4d00c00a26d341819a00a2d36db6d268201a6924926820836db4db4da41069a69a4924920f3c9269a80000a4936db8e38d88204c30134904924020924924924836d80c24d241069a09a49249200b6db6db49a0806db6db6d369241b4d3cf26988102d228b0c04da4124902db61369249240821000000001200208200209208000040040000000008049209200009260000000861a0836dac9008269a69a49200001269069240209249269248000008040041008309a4924920000926b369261061a68061b6d040b6928d00004a04d249a4d361241a29008041241a4902124124d241240800241acda49028820a49acda49800049269389a60001249a7226820824924da4da00049249b69b0000db69b69b61001e6da6da6d000269acda4900002db49b89240001b91e6d248000041200040241049a00008049200009800001300209000241208049379b69b00005349a6db6c30c24934d249041069a49a69a00005a69269a68208125108200009a4920420020826924810926b3892c0001b71e71b7830c24b24da6b08186d369c6de000092493693c800136da8da4f04906dbd9e79c10409a6936b2618c1249a6d24820836e24da69882069269d69a082010480010098410002c004da08041b6de6db7000016db6db6db0c309249249241041a69a69b4c000125a69a69248208124208269248208124249a4d24e200049a49a4920000b249349b89001a69269a690402c9a49a4980004dbc9a69260001b8db6e38c0002c9a69a4b00002aa6f349281801a8d249b68000208041240241000049a0804920824000986d060000209201248049269369200005249a49a48208279b4934b400005125100009268249204208249a49248109a6924934800124926924da4906db4966926920926928926000326924d24820824938a669a08209248201249049841249009200249041e6db6db8d80016db6db6db0db09a71a692482081251251242c9b4924d200079b5934960000924f28b36904124d34db710803cda6b2498000c9a49a080492412c1800059b4967920924020b36904104034db116c8028840000000040008000049249a00000000001000200060269000000040000048000009a4924820180030db8d060000269a092680000cda49a6b02180000c30dbc1241800009a6db6100800000920800420020824b24804104d249049000009a69209004208269a4b24812514510000000008100000066db78060000000040008000009b6da0d30000030000120020020124824804000db0c34900800800920820100030f369a60208269249248208209a4924920924000066db7186c10c30db6db6db01041249241240200209248208124208269249a6812512402924d34936d36800124926da6820836da4db4f0428d9ac9e6924920dbcf38db60000b92471c6dc1860d34800136904124820da89248001a4180004c0da248309249200a6934d24db4da0002db69b6d36d241b6db6dbce08282cb4d20c04da41021b693612492408293cd369bc000126926924820826d34d24db41869a49a4924920f36926926000136da49a8a08206a349289a0820f369a692c0000b6f3cda49861869a49269a08200301049009040209240209248000000241b41800208049249200a6e349a6d00004936da4936d24134f249a49800029a2880c04924124102136124924924082f36d269348001e7565925000034ebc9acda41079b494cdb4300f389ac926000326926030124904b060001671259e4804c0082cda4106200926c359a00a293c0001b6d06126820924926826d04d80c34d869a09a0924920000100000120020826924924806c00c34db41809a09a69249200003369269ac0b6f0c330c36f049361861a6836d040a6e80006d341049361a4136d241000041001048021361a4d36d24104000c3cda69028a28820a498000cda49849261001b0820124820024a26804124000004c049248000008000009800000000001a00060260040200040201848200009a69b0db69800309b61a09000249a0c2698000cda49020300000009241b9000066d248049300019c69b0534820c36db6c24904104d249008249a00009a04201268208268108000009a68205a68208269a681251092600003092c1b70610061b7824b04186c28b06d300009a6de01049000001301000200040049001b18603079e0100800000800024020c20924836da41848208009008008208209a6106030b2c124820c26924806b04186da8b069208609269a01b6c000671b7016db0c30db6db09241041249240209a68000000124200268209208125a6820826924812404004020000d808049a000492030010498002002010000002080c0249800249841809a60009200301b6c00238c000041241840000049249a080000000098018000002092082400c000000024982180da81088200201208001b6800800900000920420024820824804104904d24901804930004b405100009249a68204208249269a4812510000120800034104000924004900000d009a6da0100928000920020124c20924824908a608269a0000124906934104004920824904820924da69248208269349269a0000186c671b1010c36db0db6db01041241249240201a68209248124000269a69a08124209a69a69248124249800049240049a00048008008240000309a60208000269a00208049840201800009a4824920824020d369860000269209a680000cda49a4984e3a000db8db010000c9a69a4982006020f269260000269249b68049200009368205248208269a48200009a08069204208269a69a48100019b4944b305925109a600012490c1e70001e71b6c24906004da0806e30930926920820000100800026820824924820900000024900a308209a4920000000926134020820124924820820804920920d36306820db6136d881b0c38f041e6c06036db0c16db0db0db6db08200208209248124200269a692481251242c980804d241079b0005934930924020030b36124c0402cdc0c2080c984024d000019b5834930924020f36b06104064d211c6c0000cda6b2498cda49828829a6f3c0009a6124934938000136124926c209a6826924e84300c06dac9e0920920130800100000124820c26820800824000c04100024800920920920c300000000a4b36d8c1b0c06f661818361800a6a3cf00026b04924d24900004d029249a4136124104c20804000102124924124d240a2882934d388001b61a49268209248269b4d2420080c9a49a4920920f24926000926136e2498822880a9b49208289a00001049061000209241268208009800240041000208049209200240000009260b69bc9842208069249208269a00a6d349a0006d04924d24936124134924980024a029800049241a4d021241249249240a2882134000120800024820120820800804000c24900020800924920000126100806020826924924806900834f241008209a4926920000336926926106c08030c38c040003269a692608630083c9a49808209a49269a0080d000048200061a41361369241000040040200021a41b6d3692410000cf24984d02884c0c320838d02882336020130904066800165125804800800c2cd819a010102d040000326100934000066d60d2580480083cdac180000934c371b00003369ac9263369260a208, 1135812834104256, 1134850761429952, 1152580520776640, 2923728051603390863826918211054002176787356930882, 2926582546989799708388883300202201475666367566658, 1156772408923072, 
    1152443081954240, 1152580520776640, 2925868923147434427647516108460384401302537458498, 572863283729344, 572863283729344, 23549676806770201822954308732664817792791434050, 
    84680121062336, 150650818794432, 572863283729344, 1461507215282038482885006303636003181116220592962, 291388038583232, 291388038583232, 
    1134988334994368, 1134988334994368, 1134850895647680, 1135263212901312, 1152580520776640, 1152580520776640, 
    1134850895647680, 308706152289216, 572314064786368, 572314064786368, 1841870162698525361240322946250400638322956391234, 290564210168768, 
    290564210168768, 79320538289088, 79732855542720, 79870294627264, 290426770822080, 290839088075712, 
    308156395951040, 308156395951040, 290426770822080, 308156395951040, 308156395951040, 1131414787593152, 
    1130452714918848, 1134988334732224, 1134988334732224, 1130383995442112, 1139249076638656, 1139248942420928, 
    1134988334732224, 2923728051608375487825928679506210158597963338562, 581659376751552, 23014456880311265341926669828429896987980157762, 163844958327744, 581659376751552, 
    581659376751552, 581659376358336, 82480896545728, 291388038583232, 163844958327744, 581659376751552, 
    14294832160013833441906927664491996702805414722, 1134988334601152, 1134988334601152, 1134850895647680, 1134988334732224, 1134988334732224, 
    2923192831719134920015013452463234402766150521666, 183045235268598296434478370947402740692213134146, 1464357548312270496665950208013379424602852250434, 1464361729701995221157789245960555546170634621762, 265856395036478320592505678676601135255137476060406855316964702288657055168642074706786938574153871492, 1464361729701995221157789245960558923883240051522, 
    265872615188032345003444305520771183226437239218957206010836618020339484910256745132257209891563139204, 146252369499072, 82480829436864, 363955604820928, 1098268498820905904031186449895131554991099204418, 73684534563776, 
    73684534563776, 293586860643264, 293586860643264, 3957769494445566912370758382200966777530261105519384318125818322350747926034454643726555899235900020006541902626231575670028257963195630833577433867276713174224615415025196615, 291388038583232, 291388038583232, 
    620836637882915730956668679695678580603389867713789312306264045016094496812413746142302820555157548230659532237372587591140556622623982935661357907725526767863642316360391301416663089191130248042849522727042070843533539265346990783520677627873077558144411635460031216340811303971956659773513958338834060095865631168570665128854450991748409131082749978970082939154682170789079870905320671487428335242214287316249963559971628350557393383956011110170782278454788921861059991164837393232599977495450127916169464588, 6626524740013463535830307783162115251411677106937497665327590355809844238475512287881836578997425538256802217029819075324416692475796699694288438682089862302196130912661371462, 581659376751552, 480481889932903142167854800630407608450563993282697590645993910056489149020120820103452121515442875730895744488538833658824817574460527191250652239015072451630612068139926274656278423059989407662200805178446514995394564539087401581708150729455532099114140680748877512, 1464361710667450402646890759751500826331972719426, 6626524739984670267013396996019050100327454785942999750990006058620084120822665741142517774086522773981276332507326420216152609314070006214141663964933461761911788368100817478, 
    146252369499072, 75883624928192, 146252369105856, 146252369105856, 1143646988669888, 93475744388032, 
    300184131605440, 300184131605440, 581659376751552, 1147976114312128, 1143784427754432, 581659376751552, 
    1147976114312128, 1143784427623360, 1147976114312128, 1156772341617600, 1147976382944192, 1147976114312128, 
    1143784428540864, 299359498408896, 581109621461952, 2925859174743503808868118817581947470982846436162, 581109621461952, 581109621461952, 
    167968529978304, 299634913186752, 299634913186752, 299634913186752, 581109621461952, 581109621461952, 
    581109621461952, 299634376315840, 581109621461952, 167280529904576, 581109621461952, 581109621461952, 
    167280529904576, 581109621461952, 158485107971008, 93476281127872, 93475743798208, 171609924047808, 
    171609924047808, 299359498408896, 581109621461952, 299359498408896, 299359498408896, 299634913186752, 
    299359498408896, 870968776987584, 2923728051608375487825853723753442063490511622978, 1130452849136576, 1139249076769728, 1134988334994368, 
    2923192831166508376964468370453612523717212066626, 532539897021795096686880881803708965210400040735456108091229700414897272654978519405372388553351655556, 14272542303851044288489154435428510846096069442, 1128184905012160, 1134988334732224, 2924107165717779020513679290591386235336369762882, 
    1128184905012160, 1134988334601152, 1128184905012160, 1132583085806528, 1136981266666432, 1128184905012160, 
    1134988335518656, 290563405386688, 581109621461952, 172504015442880, 308705884115904, 163295337124800, 
    308431006208960, 581109621461952, 581109621461952, 581109353026496, 290563942257600, 290563942257600, 
    308431006208960, 581109353026496, 581109353026496, 299634376315840, 145290297349056, 581109621461952, 
    581109621461952, 581109621461952, 581109621461952, 290563673822144, 265783407325692137575226381985169414376715065732597837294304783194910693212968839626182634861624751620, 2206209924082192741132619679207427323615125289648971376694399426996601513437820164209808203927975428, 
    145290431566784, 294824549815232, 290563673822144, 290563673822144, 290563673822144, 435562038170560, 
    1016104311854016, 593891846788032, 1016104311854016, 581109621461952, 593891846788032, 589631105012672, 
    1016104311854016, 290563673822144, 290563673822144, 149825917031360, 290563405386688, 308431006208960, 
    290563405386688, 1143784293405632, 1134850761429952, 1130383928333248, 282042190271424, 282042190271424, 
    563517435417536, 563517435417536, 74853772235712, 862860012164032, 74853772235712, 92720836383680, 
    75403528508352, 75403528508352, 23025520098421449036053112386400835609949197122, 168105834714048, 149688343860160, 563517166982080, 
    149688343860160, 167555542029248, 150238502327232, 149688343860160, 563517972288448, 563517972288448, 
    580629121471424, 2923728070664188035398424602728449563008461525826, 2923192852774438676444075307543075703405718623042, 2923192852774438676444075307543075703405718623042, 2923192852775435601243865795132441763191038497602, 531567448248157844913174823736097128844121960795751845974434306341994933126652925557665858848943403140, 
    580697304601536, 82068580078528, 290838283293632, 145702748427200, 163432641860544, 581109621461952, 
    2923728070660200336199320681031687754952082543426, 581109621461952, 72654748980160, 14294821334947027643883130301945363522115425090, 871656105186240, 72654748980160, 
    90796691297216, 22891715116806714915796202881703034293260998466, 172504015442880, 145290297349056, 581109353026496, 145290297349056, 
    163432641860544, 145290297349056, 581110158332864, 581109621461952, 581109621461952, 581109621461952, 
    82068512969664, 871656105186240, 290839088600000, 300183996994496, 862172818052032, 168242601661376, 
    532539889101799220683992589817442196904918742896506078774597119529422869149610871153586480073811587204, 563242289075136, 563242289075136, 299359498408896, 167281200993216, 299359498408896, 
    290564210168768, 871381227541440, 581395745902124843139278367478821046963152470659552222654858506268635129133497067158473492328262037636, 75883624928192, 23014456880311265341926669828429896987980157762, 146252369105856, 
    581659376751552, 146252369105856, 146252369105856, 580834475119552, 149825917031360, 172504015442880, 
    290563405386688, 581109621461952, 290563673822144, 308706152289216, 308430469338048]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924104130924124924900c04d049249208249209249241360201249a68248248040000040000049208209a4920924d36020d241249a68249a4826d8000cda49049ecdb6306c300825149249b01009a0524d26c24824824934904904900824000924820726920c249248144908a29249240301240a4924904d849049269a09209201040001001000a4934d84934902a061040309ac0a2194524924c06036c14924d209b0180924d341241241049a6020924812524820824924812424924c35930004920924d64c0402682603cd80026904db00019b4120920d04064d80826d8000cda09048259301809a0d80f380001b6102924934924830934824924920920d20806db60009a4134820836934824db4920926d208360001b6824136d24826c34836db6d86206e041249a6c06036c24db69808508209a69a6c06036c24934d04104904924d341241241209a68000008249041049049041b08209209209241341241240268000268008255269c08209a08249249208208209a49a49248248249a4920c00984a249248300263209a6800000804904124d34d04020100934d24104184024db4904104104936d241024a4920804926b209a49a4024924804104004026d04020100104924024800020800836d8c0249b6d04d2490248, 176076617748673, 11596433824214822256170632680344663460489024322, 11774838384760261032667368938382808761845707586, 79449387438528, 72852317671872, 980735308902498431997701485221357084771536168664656037504984851965575934579626644738769121791949664325, 
    11507228461405188624840636281607168882194273090, 11596431782481678038345242618072369759986406210, 1461691542816108156979392648812690009026625344323, 79449387438528, 79449387438528, 73671649661376, 
    95677451867072, 79307653386688, 79732855542720, 79307653386688, 75870740025792]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12525934931834100924934c60c04020a269800248019208000059209a6db0000c30100104000104800800000024904d36db183410092c9a6306820084d679e00071309249349200009a0924924104924124964820c04024934d049049008000008048209241041009240200000001248200001048049048a0594944db6c40d86024d351318301008269201809a00a09b6c06038c04d41000006db01261041808201359b6c30986814920db1824d200a2924924904124d049249241041241049248001a4804904104024904d679c000d9b08008241009240348000200248249249208249208249659b7000c06024934d30004930924924c00024834b26980024980100000004100db8e3a0001b6120904000100800800000020804864d300009209a89a8000124104d66db6db6180db19b6db6d86036c6ade6db1007584d608279b7930c30b60f4bb341041a61e6de4c00026834db9905930924934d24c30135824d34d30800d60c289a6000a26004020000104030db6d80008d84004100804100020000000820106134820c44826a26986006b04124934d361061341269249000049049a4924000134184d04c00004806900004004906186180000030804820100104004000000004024936d04984904d659500015b09249a41061240241001200000208348368040008249a4920c00d049249248300343041b4c00004c04104126da4901066db6eb6f300001809369a41a0000d86e36d209801a41b4db4804924924104124134934924904904934924180100934924906034865934d000049049208249b49209041a61269248241069869b4920920800004c00000026184d30000030db6db6c300360000301b7247036db6db0c00d8618adb0000000830106f369a60001ec1e9238c20c34c36e26b06000180db6e3c3060301e9236c00006036db8d8c18cd897491e0124d34904104d04d24d34924124124d24906006024d24924180db19e4d240001a6030820926d34c20000c049a4920800020126d2482482080c0289a6a04d30006d06da0834800024000804104004c24904000300136b2400400000000403480c0249a498c30180db3db20c30180e3aeb830c0201b6db8826904924100920924134930804824904920800834920904020020d24804100004124906d0180493d9609860301b6e37030c06036db6d84920506020124da4824904024824904124000120924020820026124820000c009b49201040001049241a4820124da4826180c071b71b0c30180db6db612480, 105776595210433, 105707875733697, 105639156256961, 105776595210433, 106120121223233, 106120121223233, 
    105639084886081, 105639084886081, 105639084886081, 105707804362817, 105639084886081, 105707804362817, 
    105639084886081, 106120121223233, 106120121223233, 105639151999169, 105639286212673, 105639286212673, 
    105639554648129, 290555619840448, 290555619840448, 105776662321345, 105776595210433, 1683062796666087482455218032204149148387388503690641542173667872134640634459214755288803413294554931027445763234720860788234538068628310959596272565039303375800231715331984623011045658145064731609215379593645211178395219553675327957255726488283271562262557615980263080915283507266584691851933622069996328934161233306974134379709623685003125523980930455034494366774627074111433738949521781612821798654275495757271725878626000876082087525780653662274843983580557464290679406811017582165051339201904640173408297028332570277219757146802011546318611897110869917027642428280747717448718871570484760962929978266633024540182725697052846534985061375002093982837726008203100502545527924687344053513344218022725038504390196050497591389721244085875814341440621449504807413451787853805696350491056129840234098890259475213147789487907818959159702765912585833336830233244687874117436005430490664201606831417625688538060112599100441505144741046724109503376662162865867581412685098921888455134478750767863889450082059519967921236831956562, 
    645595635082061105784563843682232354512291949759998157872383986214355769719835957114030248969938410704853201609754473273980725323073733999454398808208783665352266797574738071196254072026924116353098048792475039391980979061151471710983259830620208291449801390084919698267665035567904325834424999073754279281275432646570201351549107189696512583690475338220883664363252773747843218920330250495833844629566417875503068745505670351218735313222131683062657855861691804172735606331807925553884021535311568381510108864257303053470747160148048756815322144235943860473670594595706892340512165004107148152236815708777011163069121754961870156213625858982161865537383174215957905761986476964961555315725191212435566630176705187785502278111929027714657229585275600235281254638519073118677300492011640072738580671084764567720133733725079365168272, 105707875733697, 17127037667974468336428502840759516096653167171, 105639223367873, 105707804430529, 105707875733697, 
    17127037647392122459441439975469696266361899843, 105707804430529, 105707875733697, 290555619840448, 290555619840448, 105707804430529, 
    9141764793860607894203101208071535377971475549914782468179310538781690946474113444101353139327866434585238406732252437174328646407782179461137308848163981851164129397729461786807319116160054388198097340365396135518770876418407336038706751127405998151658353668843989078371992446114527153991691654505366403936411225448564060926199778847596425392494748142508363153870019557413851251862700571171646347557437817472598816429186637887257320692930807288769543463298379536422197075621221416364020034134150232886269874052629095679596885511863045615037947314340876277839179825072725561978786862614717842407689743325663922428742141642714891864106365690236513448174794290254, 14272531393547573756877663160342396266619081539, 290555619971520, 871389817213888, 290343018959296, 290343018959296, 
    290343018959296, 393921778761834660491047924465781875345228584770, 105639084886081, 105707804362817, 105707804362817, 105639084886081, 
    105639084886081, 105639084886081, 105639286212673, 105639084886081, 105707804362817, 105707804362817, 
    371085815683523277355496240762347237098458731330, 290555619971520, 290555619971520, 371085815683523277355960470047966685777662858050, 123695392729281776154324680830907950924395418773420513711774277433948379611839455540674987384233624363911137099744867168088638264208791100697000028571151554727473007039917638, 1119008186549250717972877797205634454652828309314, 
    11596431745302094555091818029891226754896450371, 862593724715968, 862593724715968, 1124672583986153395524573297181108906447983400770, 371085796627710871799887822917814931930375803714, 371085796627710729823020597356121964299616801602, 
    1101836620743017761192089998096321304803107984194, 283816816153024, 354615057585088, 290413885919680, 290555620233664, 290555620233664, 
    290555620233664, 871389817476032, 290413885919680, 290839088075712, 283816816153024, 586521187104198254813645053509003345801582898131341410945831859858981260071462232524432505883308814468, 
    586521187104198254813645053669692823761587531051663339205994487953047687277818608311185602047411810436, 290413885919680, 290413885919680, 290839088075712]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125148249300049a0524924c209268249349049049049200009a4820524821826926814490514512924d241241241049a6020924812524820826924812424924920804d04820920900104124924920c04904a269248301241a09a6906026c04104124d840041049049a08200001009261240000201248248248248200001029269268301b41b6db6d86036c029a69248201341249248208268249269a49209209249248301240a69a4920c049068269200009b01041049361000800040249049028209208000040a69a4920c04d02124d258248248249308209a09209a0924c00024824934d041049069b4930820100924924124124026800020800024904104d049008000001808209241241241240209200060240270579b00019b0824920804924004904004004020184100804924920000000100924000020124824824a0c0249a4984936d8c0269a4982c60100f269261040201249a68029a68201249061248201249a68249269809249201041001008000800000040249069200009a08209a0300926d340a2ca20a5a0410c004c24d05301805934960000100336b26040124104046036d8c026b2498cda498288, 28545062787014666911229576289226118991196476226, 246514083502273, 246514083502273, 105639286212673, 105639286212673, 105639084886081, 
    105639084886081, 105639084886081, 106120121223233, 105639286212673, 28545062787014666911229578576622384131180876610, 176076617814209, 
    105707804430529, 106120121290945, 246514016458945, 176076617814209, 81444399747520, 79449387438528, 
    79449387438528, 91279069811648]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524c00064d24c20005920004930924104800000c000209800248049300019349309ac000326928120d04064d20c2498000c9a49049300019b4930920820000000082534c20c06166c14d300001b59a0904c00004d24824904130000030000920000820104000000000026980000824980000000004000926104020b2c135000006967014d20000125820136d86036db6d84d34da0126924020820024100020c04024934100000800934920000920924124134c60125930024934d34804924904d34100d24820d34100124924024904c00006d04820804d30004900924134c000248040269800248041000001b4120820000036826120d04006d00820980000da0904804d300009209a09a8000124104900805934d30924924100924104020134d44820024024d84904904924000920924124900024004004120004c008008249349b0820920934924000030124d24800006c649349029341b4de6d34c36c34d34da4d00924130800184130830124c00104024104130000100000826000820105820006104c20800000c209841b4100184130826000030824106104820004c26820980000804124104800024804124904025104904120c00100820900d26104124124900004824904924000d30920924800134020020926d00020824824924104d04d27934c00000181924d24104134124900004024100025500c049b00049a0920924800124026804026da4980800824db4820820100a389ac134100136da0024824920000d07986dbcdbcf309209248000340301a6900000c04004126da4904d04da4db4b300001809b6926000036f34da8c24900db4db49b0984924100926924134d368049a49008208009049a0820100924924000020024d24800024824904904921804964b30922906020124d248209b70001c6dc6c2ae3ae01337030104000120804134060164db6c0000400ca28980c04107930040c36300dbcdb6308c301b71bcc269a4124904024930c24d040249a4d04924900104d20d24db0126924124104000800820804024d24904904100020000000100934124104820125966c249241008069b49a0824b36f3c03cdbcc0410c004824904961805934960000100326b2600012410403602498c024b2498c9a4984926184c06db6da0920924c001a41a482493000698cd8c924000da09201049b69261041361b6d34820834c26da6900004d0c9b71a092610, 105776595146945, 121002670259927234406472746862566689836206058689245600441129357318572005962985478317286193487993553685552330402380302100848347309795936319253403900457886085089958332509767, 25690556491338218685467278950272359600620831555, 97053213373758536482767242694500393135554712386, 105776595146945, 105639151999169, 
    105639286212673, 105639286212673, 105639084886081, 105639084886081, 105639084886081, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892887670405059358277984117666919117711963374164847763910230277944192294279571238432451898950, 
    105639286212673, 731467232869769418366667779740016535594145469250, 581659376751552, 265750967022100742200056346271123354975386203364984610897514658418107890493754861168491758488524456196, 265783407325208791029135914950560770933036259608709011479497973507619824905215155671440320393241985284, 581659376751552, 
    105776595278017, 105776595278017, 105639156256961, 106120188399809, 105776595210433, 105776595210433, 
    6766417618502702711772487940764974169326030630412874781113794170334463301140426726675249240880121732864930022439174612512871378547301969717945226638662951399152321508087864744355852591372313536312493422840299120468324659264747745216034052068081207591267584536595448008035582556331551192119510556493534657844021623363156509851035964829347357550649999364358094176633517623193502794, 28545062745182767388031051043033423022264422211, 105707804430529, 105776662321345, 581659376751552, 105639156256961, 
    105776595210433, 105776595210433, 105776595210433, 105707804430529, 105776528103617, 105776528103617, 
    105776595210433, 371089997073248001847490021804729841559309144898, 106120121290945, 51381112940723817102984014520585776393699220290, 97053213336539995412115169952748291332558050114, 15132089597824606029294938579764493745169796443384291387955427529834668362862204821468609399004813120639954213263715394815614089204267251739008569243254634568852729850457805213734890924350307002379253797025576810469275387706505393416951639187132984075264746988553, 
    105639084886081, 105776595278017, 106120121223233, 51381112940723817102984014520587465250001935170, 371085815683523277355418869214745121556126520130, 73671649661376, 
    73671649661376, 73671649661376, 73671649661376, 89084140327872, 89084140327872, 144040460947904, 
    146239484203456, 146239484203456, 537800160313693666801786317717183131979374947421342043205663627968014413552512479802207573600540730052, 581659376751552, 146239484203456, 573029569385977991062543329210225784855044328448242342814627317671367155283075598756617051915804700804, 
    159433623736768]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249b6924926104124924924d30004924924920820924924936d261249a69a49248271ac9a49000048a4930c04d241049208249269201200000001201249a68249248025149249b4924000524da6d24824824934934924904498824000924820424820024a248108a29a69249b40000a4924924db49049269a6924920a369249a620c0a21b60001b6104084904004934902196544d24dc6f00014924d269b6a30925134d249241249a6924820812512424924db5934920000924d64da49800271bcda6900004a259369a6000936dbcdb6db0004c30004121930dc0f30db6000120d04004860c02924936924934830824924926926d20a36db69a4000136d249a6db4824c36db6db0db6136c209348348301b6c36c06004924920920d20134da6db6d80026db6db6db0db09b6da6db6c00024934d24904104924d349249241269a6938800024db69a692c92080002492482482490410490490412698482082092413412492402492492ca208209a49a4924a248249a4926db08049a69249b6c203249a69b88000249041041a6d34904000920934d241024b6db0c06db61840001001001041040040000048041008069a49200000001001200000201a492483720c036db6f04d2490248, 246514016458945, 246514016458945, 149817327096256, 163299632092096, 46028913718009035691403391721109846825642259266, 45694401263967809232331051087002111728720828226, 
    1461523981738624274032783955847876506853000151875, 45716702094236931585707202671118411948168861506, 1461546326125036362266283430743942558338779252547, 145419280585152, 149817327096256, 149817327096256, 
    149817327096256, 979960733553356403045394092346077206128045485299074263612761660811814303347704933664553129376410128453, 46408025067953432608219533389963802671679820610, 149817327096256]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524d34934d40c20924924d659248269269a49000048a4d40804106d2082c9a0f301861209240041248049249249249200009269249261041249249250248249269349a49048b69a0000926820924104926d240240200041a48249209049a4900594924d349359671309ac9249a418c0a49b70301b7040814920c079b0c200a29249a4924a04104924924d24924134924924c000249249041249a4904124904930820924924124924024924924d34920000924924d249000249269a4980004924d349240009249a6a24d200041200041201009a69a0d34000120904004800004924934924d34830c24d34934924d609a49a69a60001449249249048248249a49b6826104020104804020a26836d86304104900920100124926924924b000049a4924926c00134934d25000024926924b34904a36924924d24000da6d050000269000048049041041040000009b4820126104024d36d26dc00009349349b51880249a4924d20c049269249348301649b4db4c00026a0410412492cd86d86d86dc79b00001009249a40001d61b75ecc04924924926104134936924a249049349259ec100934d24936984065934d2490000493492082492c920904124125b24820924d34934d841049249a4928d24124d24966f06024d34924db6180b24d24dac000125830821964b268200008049269208249208049261049269200209a41249a0804d20104100804d44db0926820134804000020135934c34d060249a4b049268201809aadb818450, 176145272281281, 371084596106858830460040071677272686943434464066, 176007967480001, 176007898337473, 371084596106858830460040071677272686943434464066, 176076618731713, 
    426898418045376, 299350774256064, 7729078731994588773169520663173251283296907801640110954566326392461407902589179010824201006206595624384034249679197139738901826122469110271954324683457548639214530598008391, 426752389157312, 176007833258049, 176007764115521, 
    176007833258049, 290554681233856, 290554681233856, 143228851462977, 426752389157312, 426752389157312, 
    176076617748673, 176076617814209, 176076617814209, 176007898337473, 17867341828544, 426761113309632, 
    431159159820736, 979753408009561441403821085877675560297771701180358304078786250706770420876921972708662868161585894566608767845429839715650417483777713123531621475651614699327938458556702922806257186251537950066265075002730897254235607712523156343607400479407124371050856969246988552, 4050035796103150511514478395439818754354514104258973876441152487528550318155475782109386997880756624793958637680422149152239475040914966784557402776723050991418579190493399622, 456743304743237133622503763453563951170398999362, 985937581325649841630162394998519639200251432609887395420495737128750867714985128487558625125349591609093729670185984770324529083850703654741099843772767065529058165181327523419136180764860248599499784661046663997838237160258466695334750208615064568527324428749837512, 581109621461952, 
    431159294038464, 431159294038464, 143641445159617, 143641445159617, 431150435668416, 431150435668416]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12514924934b20000524924d26820824934934924904494820004b2c920524820126b24810514512924d24d249241249a6924820812512424924924920c04924924924d208049a49249348201ac9a6926d000249a4924d30c029269269b4c301b6db6db6d86004104124c24904104900824920000180906d260000201249248029a4924924830124924aa68208249269a49249209249249348200a6924924d208069269269b0000926924934c300a69249a6d30c02104104930924080004024924902124d259249248249369a49208209a6924d24800024934d249041069b49349208209249249249241a6926d26d80026dc79c6f4c0008208000000208249041049049008000000009209241241249240259a49a4924d30c0c9a6924934c30336db6db6d80024984104124d2cd84f25984967920000100b369240309249b4d668028a49208049241048201001009241040040000048041008049249200000001001200000201a4924837b0c0249a6b02d249029a4820124904124820024924824926980924920104100004120080000004004906820000920820830180f369a40a28a208, 246514016458945, 246514016458945, 246514016458945, 97053213341856942889471639834786480012834919234, 246857613842625, 176076617814209, 
    176007898337473, 176076617814209, 176076617814209, 176076617814209, 176076618207425, 176007898337473, 
    149817327096256, 176076618731713, 176488935592129, 91701014109171615405761835991292696255214416706, 149817327096256, 149817327096256, 
    149817327096256, 149817327096256, 92057827393514071553238442363179781741900550978, 163849253295040, 163849253295040, 163436936827840]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524d64d24c00024935924930000924d64924c000249ac9a49000049659349300009acf369260000a4b3cda480000000000490192092cb20db0000120104000000802534da6d66c31414d359359a0000964dc6d248000249359355b0000926924b2818a1349d71670000269b6da4980004d359b59b0000826d309a00001141008051b0c30136db6db6d86184d34da6926d24124924936986024924924db61819b79249b6000134d349a4924904d34d34936180d44d36d249240208201041a6820c24834134900000804930100000920924124024934d34d24800024934d34920000924d34d269000249a69a4900004944d349a40009a8db69a6000124a269a4d200000000041001209a89a0d34000120104000800804924924926104134d369249a49049249249a4100924924926d04064d64924d80002920820834934920820920924d24000020124d24800024824924900924d34934d30c30934d24d34c30c25135934db4d309a6b26a24000145164926d04026a36e269800048249a49b68200000201040040209ac836e06184004100000100124924924804024d24924d84104924924d20100d24db4926124124924936984024924924db6100924924934800134d24925100006db6db6db60009a69a6944c301b0000db0c00020824824124900004904838920000100934124024b36f3cdbcf3cc24924924d20c0c924924934830336da6936d8002498410412492cd04965984965920000100b269240009249b496480492aebae37638230db6db6db6c30236db6db6db0c0cdbcdb79b8000924104106924e361041481355c6c000040289b6980c04d0ad46e30134db6db6db6db61b6db6db6d86036db6db6db61819b79b6db6c00126830c30db6db6c30c36c36db6d80000c06db8db0000db0db6db6024820804120104920820000824124030135130c24820804120104900c04d34da0920820104804020030136d3082480c0249a4b04db0200db6db61269a01809a6db8104901804dc08009241009209241040201490410200040049a4100800804a20900820100926924000060128f248000040049a49029249208000200041b4c20820c34830020926924c340200063602b6db6c249a4930d8080c1bc9240200000001809349a6100030336db4800006034da898000d988db6db00041009a69a40001661b49b48000248269a69000049049a6da01241040209008041040248249049041000049208201001269041241040008008208040349a4904904100820020000100136924104020124934824d01804db4d2092410080493492080, 176076617814209, 176145272346817, 176145272346817, 3962147287403470016010702432308645357506668248651544168968039659837861734850877599031543432705693201509532693011198807150308255619598351249939881314139746086546686442575539782, 176145272281281, 92057827377563193468189475209975653601582076739, 
    94198707078082088256388419169899259125947433795, 176145272346817, 4080981816248566486622747978161616224421528568769333410407207199332498767289399556565523954191601411595135777940129717163387437158745710009217632404219625272485453398694735430, 3959248884274359365548419067457206717069019400319716417426288999055236660788395602615264067538354604009793740129177219952428115466193983138853946207292012181113633800837180998, 176076617945281, 176076618207425, 
    176145272281281, 176145272281281, 435694511067584, 435694511067584, 286156768940480, 290554815451584, 
    290554815451584, 176076617814209, 176007898337473, 176076617814209, 176076617814209, 176076617814209, 
    513258947384672241508770081198767529029528120476883228694076763406433457368536062294145592635566923626776628088168188713519888649592443891807036862224882537979239082536518, 176007898337473, 290554815451584, 176076618731713, 143091269898433, 143091269898433, 
    581109621461952, 563517435417536, 581109621461952, 581109621461952, 143366290420673, 286156768940480, 
    290554815451584, 290554815451584, 290554815451584, 290554815451584, 290555083887040, 290555083887040, 
    145281841631680, 286156768940480, 145281841631680, 145281841631680, 290554815451584, 572313796875200, 
    158497992872896, 299351445344704, 158497992872896, 143641445159617, 143641445159617, 532150795548267421505637658571878159108952396334665541067527104970043012461355695048811312633464713348, 
    143641445159617, 143641445159617, 290554815451584, 581109621461952, 286156768940480, 567915481928640, 
    290554815451584, 290554815451584, 290554815451584, 299350908473792]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249248a4934d24d808049249269a0820924d36d261241249a69248248040000000049049249208209209249a4d360201249a69248248025944aca349a69a00005a69a6e248248108048201809a05a4a278248248108a28a49249269360200a4934db49049021000000001240b4934db49049021945949125009a42a4820812424924924d34d279b0000926d249e4c06026c2693cd80004d44d20001930d20d24984066c029249249349249b6830824db4926920d208369a4db6000134d24830834834924926920d201a49a4924924924904104924d349241241009009a6800024924904104906f36e40c30180924d34924124036db6db6db0c069a69a4d300009269a6d36820226a269b6d04036db6db6db0c04db6db6db6c30124d041841b4d24904006984924920000180d369240000201249248024a49a0826920820d34c341340001a69a4824924804184124c24d040001049309341a68009ac8000041841a4d3cd84d00004134d2490400010092492410248, 188397414113878598942350365559499709935104579394, 183045214891496774834478724531658395114358731586, 290555619971520, 283745949127104, 283745949127104, 1461546326109085565469944662157316214272888489795, 
    286014900801984, 286014900801984, 308439863792576, 308439596143552]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125248a5924934d31820964d24d24864824924836c00005964930c30100924924d248040049248a69b69a69c0000924924d361041249249a4c2482cda69349849008008200009a09249241061241a4db6c218040249269249849005949248a5944936d30100828920db01801b7836c310470140a2964924924934b04104b26924d261241049241a6000024924904304904924924926124024924924964935960000925124964c0402492492cc000049049300001009201249040040049249269ac926f2800012c9a49acb00804d26d379800009ac9263080201ad9a49acb00800924924935925924c31825934934930d309249249b0000104125820c34024104934930d301249249a6b34934a00004b469a4d26030104984d86000026b34900004908eb7650c301809869a4c20134024924924d30c049249a49b4d20124924967186024924924d20c04924924934830126db6db6db6c301b6db6db6d86004004124126d80004904d86d30000000d86e360000001301a4804924936d249a4835824db6db6db623c135924db5031825934936d40d608269a6e38000104124000004030db6c36d883058349301001001b6de79e99b6f6d86c03cdb6decf0c186f36db7b3c3661b6dec36600003cf00d8c30180cde6db7b3c000024920904920004120030160000924824126800134d04c24d00024904c04db6c0000400412412cd84c20836d2cd20db6c361b6c00030020004046804004124126d81000f36db6e300000009009a610492412492c1041349369249a4904104900836920934d04904d00005335984d679b09c6db6c36d86030804926824920800124224124820534934824906024904924b041049249209340009249a49269240000001201248249261241340000000001a41a48279b6db0db6200f36db63380000200209a092482000000480492080, 426685817164224, 94200100853515505560790686895552127626408647490, 92772156262528581988687718766620031499263554114, 145221980525504, 188397414114916412921459883716003771822555272003, 188397414117574868913029715461811385960295830339, 
    188397414114916412921459883716003771823629013827, 188397414116245640917244799588909549215188783939, 145221980525504, 3959248884261713200054070301374900504787186648309658798780682691903566592414038266300240000915910215491626339616934714806643645666349797103727844081826305107932115979325451846, 316745325807681, 188397414113919488121669396126637712037235922755, 
    3965015557814664228012186897656180333172568134776402773959307762878331079072938579465118851890008882862359261610733735737287053059748754282242478971280909612528702970979670342, 283816816153024, 283816816153024, 365399103960235674681222881499677307806022654786, 283816816153024, 123665204423862013091695744586263243078332998781788532443937729108824167316601303465923524800550402188448545940316143953459162093348005521786529748236926260657988406370852423, 
    123696340535246148183249400972245181624177526025726223924698647449929569560573958237196050814774798201249377309206487813761074689582613880672772487531685925652047222181682759, 283816816153024, 283816816153024, 354202740593600, 354202740593600, 123665204429260709645147580245635889287654848008836846424307615232086719432836670709970083437415410646788564129229916432207711768464830820285290478226245794269544377684556359, 
    15015033664604734385304171617226701436605314496455237494291795681606021681079827736075617074811617342380978787129425599223626254634291809215979749825612586198191405910132609334920639918923026833240762551613068150412865007987835282957421676745377897733169697248877513, 284241213538881, 284241213538881, 365466180675625289890224018189037585997878025026, 426754469532096, 286014900801984, 
    286014900801984, 286014900801984, 426769971680192, 426754469532096, 286014900801984, 286014900801984, 
    286014900801984, 426769971680192, 182866808228112565279967155395384909796598690627, 15015033881354251346468457975036149315255745592249626807130963813530430696979169062042352290376891651855992138139960607797816754048365006110807534918824188602283939297982743186520619222551560804150058726295098955509631648888784784050923450850649034155106848249877513, 286014900801984, 435557340549568, 
    286014900801984, 286014900801984, 435566064702400, 435566064702400, 290413886837184, 290413886837184, 
    3957829878074701413907686383239865501658171837967551860237145669736323934851191706140079383456429908679022819247051147354365924974865014835058517931718691008960206582268819526, 983485173535472516292983558099259672340416835892789215131387921690848427180952659264109468581401338848375301458172474061836979836873826344643667220914757848109627509829112915738621966671650072552982360758225568191253976769120753135510955170836196468639925256249877512, 426823189008832, 427319727494080, 426823189008832, 427319727494080, 
    6774196050954635362461461967602982022548002716692884825353129154306731405264943405496774878105943513079369238456748650463643557859837424280056231767766317289248166829356872612579755956072068423242285210450708009443621424277468157730798605023316730241652748165289608155978670200425886081431709551581701604462634265559215331397600102590841920418897810445199187035295986768223798346, 290412880204224, 990553148756928, 2219655157321364988704558315492936806446652486030628537745237583264940623010269544427226925908996681428397034012560562243824547546794912515233761567011089210307148690209982328767286412999444799456115264018065326355519274346574710841694798768933984146950942491179399771552348344339714339526815596656240927936529785466304308115688151456594935655714524001772252163844620467846455076055594541044362344421981808069964478614211348348981945974769524387910076446781883122161365774495529352997026407602234982961804213900, 989865953989568, 989865953989568, 
    283958550204864, 990553148756928, 127214941311622704256526298211844695893270623086573357001146077483017346225896805051960697867652, 286156768940480, 990553148756928, 365399103964897076933080926198393315377658483522, 
    365399103964897076938032686355534977215280206658, 365399103964897076938032686355535821640210338626, 1461529556906314653900892778528220560788394422850, 365421404795166199291408837939651277434728239938, 1584806376596168463253968013908706081342648324518585627243378283275113548289568895156944396007966929045608555120826038077844916423354476375630679414412877977457788052119898244051260743419833626678787201120974601430434073219645188279871559664483730879764513832498877512, 283966335624001, 
    426898418045376, 426898418045376, 989865953989568, 426898418045376, 989865953989568, 283966335624001, 
    286014900801984, 286014900801984, 286014900801984, 990553148756928, 354615057060800, 145703016862656, 
    427181885887424, 290839088600000, 354752496407488, 990553148756928, 290839087682496, 145703016862656, 
    73135785776064, 73135785776064, 145206478377408, 145703016862656, 145206478377408, 145703016862656]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125144a4924b2c9a0000524929b268208149248200009205249278208248105145129125049242268208124249249249b49359b0000924924966c04026da49bcd800049b4930001930920924906064c02924924936d24936c30c24db49249b0d209b6926db0000136d24830c34c24d249249b0d2032c9a69a69b6da8800024924934d041089b6e489a08209259249241240208000000208249249041049069a6db08201009259249241240249249249208049a6d36db6da61249a4924d30c029a6924934c30124904104124d249041049049249200001809349240000201249248029249269248201249a6924820824934db4db69049a69a4924920db6db6db6c300b6db6db6db0c069a69a69a00008a21061069349240800040249249020a49248208049049a6d30db60201000248000000020009200003041041a61a6920804104024da49041049049a4920000100d26d24000020124924824da482cda49849029249248201241249a4820924824934db4d869049a69a49209208a69a49200049a01061049369240800040349349029b0926b369240a208, 105639084886081, 105639084886081, 30946491887137527512635394397712577111467401421869053931423480197210555848490741530571694691444298637454440404714861679400811931037368747989281518304777692052556589045165638, 283958550204864, 286156768940480, 290555620757952, 
    290555620757952, 283745949127104, 283745949127104, 283966335624001, 286014900801984, 286014900801984, 
    308439863792576, 308439596143552, 308439059272640, 308439596143552, 308439596143552]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125248a4924935930000924924d64c0402492483cd80004924930001920920924d04064802514924924924934dc0180824920db8000104800000000010004da0000000124924926924dbc980004934926f260301349241e6c0002692520000c904904926c20334024924924924925930000924924964c0402492492cd80004924920001920920924904064804924924934d24935000024da4d34d401009249249b0000134d24830004024da4d34d00100124924924924924e041049b69a4936124124d049a6000024924904004908e36db0c303009249a4930124024924924d30c049249a49b4d20124924936986024924924d20c04924924934830126db6db6db6c301b6db6db6d86004004124126d80804d04d86d20000000d86e360200001201b6804924924924180924926926104124924925106024926934920c029249249349a4986036de4d36d800008008268249a082092092c9240000003209248000000248249009249471249c5004024db6db6e380301449349c4c000249a4d271300008269a6e36000104904800004c30e36c38e00004824120100030124934d24900034d24da4984104924d3cd64d009249a6d24c301249249a490403cdbcf6cf61804924d66d282009a4924da6c301a4924d269261809a4924da6c300200401a0926800024024824906000000100924024920904920000800824824db0924824120800124904826d00020804936c04d20800000db8c00004004124126d8d860c36dbce30db6c361b6c001b6d86c3cd80004004124126d04d20834db4d200000009889a60000209a49b68049249241009a0924926106924124924904026024926930804d029061241a01248208008248069b0820920d009240000001a0824800000024824900804b478049309209249a4c301261249b70001b4824926930c04806db6da41015a0926db49400051b0100184d86d261800000040069871bceb0000200000930f009a81881381b01b6820006984d06d20124924804026834d24984024904924d309201009249a6020134124924984024824924106100c20900024824024904924d261001a00000009009240001249a012482480, 316745325807681, 290555619840448, 316745325807681, 316745527134273, 52402071030052510226571306715644277499972362470266378992173871549475382662366924380793745891579781800662363531271423719196554160694383830205800793826175474123178440298881351022300741932098554012186771387746093665016443464520353142376699801445544332809497132152219011821827287771762118368787927202061258484309260574178481901473205758580225237112127236775457400668118069087536075, 316745325807681, 
    15015491880072522916433016304135929284359156940133935635973506323406995497285647122261209856094157300819743572791087912310147621163438626061746688727445777937295922261586884913959276227850809200952828171670709169714428994048017560831101577862237961307815937246956553, 371085815678569806979088637708282623657314355011, 3957316615500260807304151141993611365631737584608255211625976834062548623992585898034778024102235607758465992721828477863741189041684767464095645045352381316679496975430889030, 290413081530816, 284241213538881, 284241213538881, 
    426761113309632, 426761113309632, 426761113309632, 290413081530816, 290413081530816, 439955252842944, 
    426761247527360, 435557340549568, 188398111013183097815981959314676415357914190403, 316676806017089, 145277412446656, 290555619971520, 
    72639716594112, 72639716594112, 283966335624001, 145277412446656, 145277412446656, 73120752931264, 
    73120752931264, 284516645102401, 145689729307072, 145689729307072, 72639716594112, 72639716594112, 
    284241750418241, 145277412446656, 145277412446656]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x328a69a49bcdb4d26d800069b49b69c0000d24d44ea6c06038f20800f000069b4830000b20db6f36208030124d44d860268029249a4db6d349b6000136c369a4030006136824827020836db09209b0820124a26a289a69b6c000249248208248208248249a49a6b20000934da6a36db6c06034d34d34900004d34d38d24124104134c00804d04004d301241241024a49a00049a69a0904134db4800004004d30d24124026800006030c28d34e36d80004934d30c04934104d34d30124d2410248, 581109621461952, 590189718410176, 732180859396178183579687064224734714265551819586, 448458807431084501734840576071712681273559349856749467232355169981524902537735782346991462871560507461, 315581302341600454162980438385081013047762242618292642185958804983852361622108952196963921772582105157, 581109621461952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x16524934d64d24924947000064db6db6db6036134d24c06040c2db0c30000c1041b6126180004024934db71b00009bd1b8de8c00024a24a38dc7006024924926a000049249249241a41bce48e69000024924820808d888249249241a4049030c49000002934db6db6dc70060671c6dc6db11b0db79b6dc60361b6db6de6c0003db3d9bdb0c186db6dc79b19b0db6db6db6246036c30186066c3db3180c30cd80180c079b01801b6db0db6006024930004db71309bd000038de6c24924a34920004824924d249a4024800006040c24836e24800004830c000000000249208049200061c0c012010009249241249a4000000000000006dc0d86d800011b0c471b6c30046c38e36906008d04db0826db0000d370301b6c30838e48c69188184db0800000d20d371b68300348205249b01b6d80046c661b61b6c00db09b78249002641b48209e6c000669269879b1820db61b0e4620603482000006486092492180192080, 2076195733906855321610250751793454803949015874625542905023717685644146870777358242094797772183101892, 33218886717633724322929770282846208316909174814442074122836055103559240864881504107036958791236122116, 129777547423926009027780781102568141247809428432542757610719523840815426617176300214442814007725444, 129777547423926009027780781102568141638247729720950328861052970571161682915071093471066967127412100, 2076195733906855321610250751793451608177390250222496765028063275349193198618746324677786622287208900, 456741910950649929728244397489098419508716000066, 
    2076195733906855321610250751793454803913980796492993811941002800266395474592459125086604557891461572, 456741910946651840864762976563459513387965240130, 41523604313294222723281532232352798101976243670243762534684172182216438835877916718125656370607826436, 66502625331739736685845951987862070047603822321133703065636459289366969623524894719964200049852404997, 33218886717633724322929770282846208316897019609211577292832712416407312947856943431186793170145965572, 411092285609664332416856013581923724914719742786, 
    7089992252700859969487171186172208911008898232883260323297872729411723860437239424915604755750918478824280692275026579537920628393011895125631904880325871041964756371662435910, 581659376751552, 365466006455704444305170270850658186048607114050, 1038216427127841050626293395988698719079573027325193086294139506105652934147270431040069777005530500, 1038216427127841050626293396355569673326158933651021827598302640312507228351327928154607205608457860, 1038216427127841050626293396355569673326158933651021827598302640312507228351329609114169271807772292, 
    1038216427127841050626293396355569673326158933651021827598302640312507228351329609118586113095763588, 1038216427127841050626293422770278379080344189110691201498048303206016411043482849037360660664256132, 1038216427127841050626293396355569673326158933651021827598302640312507228351327647994806827390994052, 1038216427127841050626293422770278379080344189110691201498048303206016411043590430449332897420379780, 1038216427127841050626293395988698719470058972080127723250836294544555446560165758529288435983764868, 45762523284908034719455770089311860452757634626, 
    427035856998848, 45762523284908030916503969404623655962648018498, 426752389157312, 426761247527360, 426752389157312, 426761247527360, 
    426761113309632, 989728515036096, 426761247527360, 989728515036096, 426752389157312, 286156768940480, 
    365466006455704444305170270850666911806171140930, 426752389157312, 435557340549568, 1007732615287744, 581109621461952, 8305731417022698958352097782075148137966489218630742390475078754831753390201949667768638273556106628, 
    8305731417022698958352097785376986726185762375652697577746239282234413100114757685273050951104073476, 8305731417022698958352097785376986726185762375652697581810550114854269353643052160189784563576737540, 8305731417022698958352097808856727797967260381142156687681637569611088398775647418072955948383702788, 8305731417022698958352097785376986726185762375652697577068854127272259304519181979881242546352426756, 8305731417022698958352097808856727797967260381142156720196124230569938427002003217406824848165015300, 183044866400560245299219600275978356503615648322, 
    290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a4d249a4d34d251000049249369a0820f3493c9341041a6d24d24824824104000004d04924930820920db49261040201a6d24d24824802934926934d34934000136da4da4d041049001000001341369a4a041049041249249a69a69b8c00024924820826820824824db8f36dbc186124d249a49000049269b4920820db69289241043269249249a486cd3cda4a00004d24100004d24d04900804926920000100020924020124024924802934947937944000136d64db4d0410db3db369260001349340001349341369042049249040a4db8306030dbc1241040000041049008008249200001001040000201240248248241000051040049208009a4920f3610c03094432692402492486cd0000cda4984902934946d36000134136d34d84104d0d9e79c00019b0900000134100106d04004d24d05b3c00033692612408, 1462220839128391462983701627165148605588829197122, 1462220839128391462983837027373458500252430586690, 1461507215282038483043462627483940235585897190210, 1461507215282038483043462628664531856303308493634, 591634974905280, 589639962596288, 
    589906250568640, 589906250568640, 589906250568640, 568469129139136, 581659376751552, 581659376751552, 
    581659376358336, 480481916521385581297853212313707405463849895553539535509176267796488054283372442442719493135054456599089114842813613920702502828498747899720139532815776348282158144921938446973798957118933279824461901706431255003917817827621043179840075494707391977857491976246997512, 581659376751552, 480481889932903142167854800630407608450563993282697590645993910056489503791618570091768622831126190722040686638384928368825083785486769103506407699876834065728914582714819445455014527405657706359485746142769063252140230891404894434622142701828691104117064712748877512, 1464361710667450402963803409808558176706148520770, 580834475119552, 
    581109621461952, 581109621461952, 581109621461952, 581109621461952, 581659108840384, 581109621461952, 
    581109621461952, 581109621461952, 572046972031936, 581109621461952, 581109621461952, 581109353026496, 
    593904731689920, 589639694947264, 581109353026496, 581109621461952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a4935924924925930000928b64b26000164d24964c040369a69bc9818049249041019a092cb08000324164d24964c0403692493080c900924d64924924964c0002592d92c980004db69b6f26030124d04c64c0002422c18000c9059b4961830100db4904c20324024926924966c0002c9a492492c980004935b359b0000924924b2602013d134f64c0002492482080cd84905800001920824924b26020000104c0400080493492593492400092cb34b26000164d24964d64c3692492493000493593496000193482410092582092c000b66b24164d24804164c3612080493c1009249b59b59b0000d249acdac980004db4934924c00124d64d24c00064d20904024960c25a0002d9ac9049679b0060000d84830124f04024926904026960c2492c9b4920004905905900000824924f26b26000104d04c0002483cda480000c9a492080492c184930005b45920924924020b2613d104034f6080493482593010092092cb34000b26166d24804004038124900804d04924101930800928000326b04160d248041e4838a2080c9a61849300019b49619209249ec9b1840180b2ae39630c30300920d34f3600013416c1e6000020b34c3cd800000041001b0000926100000326135961000066824b2498c180804f359201801a01248300019b5820d249acd8002c984d84934020134124d64c00104c2410000c9ac104db6800326986124c00064d24c649679b0004d6080, 376817085501394302402512340935650033589955875650, 283958550204864, 1096149922635686237522569070110328800701828879170, 73670508745152, 144040460947904, 144040460947904, 
    214411285500352, 144040460947904, 365399103964897076967743247298392829540358443842, 354123283435968, 283958550204864, 11440630863596311095682835151132037527946408514, 
    91366501655132336064839459002070373426253550402, 362919376458176, 713670124921035323315652138314541372410975042, 290555619840448, 290555620233664, 532287082837304853857219408770119062390332177485363506637560520741324261089116939018937186157458562116, 
    362919376458176, 642203920110528, 532287082837304853857221167362474354130440468247488048351689537555551543084728794499436899402044873796, 565304150213185, 1461529513348177828279367653769890641568514245443, 565716467073601, 
    565716198638145, 565716467073601, 565304150213185, 290555619971520, 1461529513368780940808987617298717616598876750659, 572314064393152, 
    572314064786368, 572314064786368, 73670508745152, 73669502112192, 144040460947904, 144040460947904, 
    214411285565888, 73669971874240, 214411285500352, 144040460947904, 91388802485401458418215610586185829254057448258, 22880651877387912666330914305620875841810487106, 
    354123283435968, 283958550204864, 847200561402816, 283958550204864, 73669502112192, 73669502112192, 
    4153201855441500818701610578049673258631686710515226850029317199127947990018738035342015558391114932961184338268419131505021848037637987942689378456271626255785080967357495878, 114224853191406947696385725069724209722526029634, 73669502112192, 218809332076992, 214411285500352, 73669502112192, 
    537796105276741744684020501612001949339104881696594565793659786720081817116121574343530077818028466884, 565716064424641, 588409155722081177827047457669990376747846963691417518556147904119760935911429618403304916428852994756, 565716198638145, 565716467073601, 565716467073601, 
    565716198638145, 91262157918656, 75868525367744, 411137932617644142563595875963622425296801651522, 365466006455704444027871699984706393973297533762, 1096216825126493604582697522796647677974953384770, 
    75868525367744, 216610308821440, 216610308755904, 45761216642489893568703548343037959470913191490, 75868525367744, 146239485120960, 
    286156768940480, 426761113309632, 286156768940480, 426761247527360, 286156768940480, 75868525367744, 
    91522607467016192538472520312244348314936431426, 91522607467016192538472520312248781562731057986, 75868525367744, 216610308821440, 216610308755904, 638835659117504, 
    75868525367744, 146239485120960, 145277412446656, 286156768940480, 91522607424813042680675212362423420934330274626, 426761247527360, 
    990141234549696, 426761113309632, 286156768940480, 849398780138432, 286156768940480, 1461685619159563222353722024412616785995229107011, 
    532345469047865660768622333088140680540250989525782413097054333067290222948038628089958588401972354116, 582173774869328525925783379737988441853037947570716238949902121358965199062243510735206108435107224644, 532345469047865660768624091680495972280359280287906954811183349881517504943650483570458301646558665796, 145277412446656, 145277412446656, 435557340549568, 
    435831950021056, 145277412446656, 435557340549568, 426761113309632, 145277412446656, 1461685619180664797282620678387531718135012987715, 
    163281915351488, 79236786360768, 290555619840448, 290555619971520, 290555620233664, 79236786360768, 
    360720353202624, 91701014109169014176807304463376972459410477890, 149675458957760, 149675458957760, 431159294038464, 431159159820736, 
    431159294038464, 149675458957760, 290555620757952, 79236786360768, 290555619840448, 290555620233664, 
    79236786360768, 360720353202624, 642203920110528, 23549676764526323463641451437556617014035896130, 411761136293176523780012746484295148286901246786, 149675458957760, 
    290554681233856, 290555083887040, 149675458957760, 431159294038464, 431159159820736, 149675458957760, 
    290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b10_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_15_0
  · exact tv_b10_15_1
  · exact tv_b10_15_2
  · exact tv_b10_15_3
  · exact tv_b10_15_4
  · exact tv_b10_15_5
  · exact tv_b10_15_6
  · exact tv_b10_15_7
  · exact tv_b10_15_8
  · exact tv_b10_15_9
  · exact tv_b10_15_10
  · exact tv_b10_15_11
  · exact tv_b10_15_12
  · exact tv_b10_15_13
  · exact tv_b10_15_14
  · exact tv_b10_15_15

private theorem tv_b10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [1, 1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b10_0
  · exact tv_b10_1
  · exact tv_b10_2
  · exact tv_b10_3
  · exact tv_b10_4
  · exact tv_b10_5
  · exact tv_b10_6
  · exact tv_b10_7
  · exact tv_b10_8
  · exact tv_b10_9
  · exact tv_b10_10
  · exact tv_b10_11
  · exact tv_b10_12
  · exact tv_b10_13
  · exact tv_b10_14
  · exact tv_b10_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H3 := by
  intro M hFirst hM10 hRun _hUsed hForm hMissing hLoop hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 := mk_good_ne_sp1 M (by simp [hM10]) (by simp [hM10])
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, false⟩) := matches_set hm0 hM10
  exact tv_b10 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H3
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H3 := OMA.BB4H2.step_proof
